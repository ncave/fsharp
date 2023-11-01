// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace FSharp.Compiler.SourceCodeServices

open System
open System.Collections.Concurrent
open System.IO
open System.Threading

open Internal.Utilities.Collections
open Internal.Utilities.Library
open Internal.Utilities.Library.Extras

open FSharp.Compiler
open FSharp.Compiler.AbstractIL
open FSharp.Compiler.AbstractIL.IL
open FSharp.Compiler.AbstractIL.ILBinaryReader
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.CheckBasics
open FSharp.Compiler.CheckDeclarations
open FSharp.Compiler.CompilerConfig
open FSharp.Compiler.CompilerDiagnostics
open FSharp.Compiler.CompilerGlobalState
open FSharp.Compiler.CompilerImports
open FSharp.Compiler.CompilerOptions
open FSharp.Compiler.DependencyManager
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.DiagnosticsLogger
open FSharp.Compiler.Driver
open FSharp.Compiler.NameResolution
open FSharp.Compiler.ParseAndCheckInputs
open FSharp.Compiler.ScriptClosure
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.TcGlobals
open FSharp.Compiler.Text
open FSharp.Compiler.Text.Range
open FSharp.Compiler.Tokenization
open FSharp.Compiler.TypedTree
open FSharp.Compiler.TypedTreeBasics
open FSharp.Compiler.TypedTreeOps
open FSharp.Compiler.BuildGraph
open FSharp.Compiler.GraphChecking

//-------------------------------------------------------------------------
// InteractiveChecker
//-------------------------------------------------------------------------

type internal TcResult = TcEnv * TopAttribs * CheckedImplFile option * ModuleOrNamespaceType
type internal TcErrors = FSharpDiagnostic[]

type internal CompilerState = {
    tcConfig: TcConfig
    tcGlobals: TcGlobals
    tcImports: TcImports
    tcInitialState: TcState
    projectOptions: FSharpProjectOptions
    parseCache: ConcurrentDictionary<string * int, FSharpParseFileResults>
    checkCache: ConcurrentDictionary<string, (TcResult * TcErrors) * (TcState * ModuleNamesDict)>
}

type internal CacheMsg<'T> =
    | Get of AsyncReplyChannel<'T>
    | Reset

type internal Cache<'T>(init: (unit -> unit) -> Async<'T>) =
    let agent =
        MailboxProcessor<CacheMsg<'T>>.Start(fun agent ->
            let rec loop cached  = async {
                match! agent.Receive() with
                | Get channel ->
                    match cached with
                    | Some cached ->
                        channel.Reply(cached)
                        return! Some cached |> loop
                    | None ->
                        let reset() = agent.Post Reset
                        let! cached = init reset
                        channel.Reply cached
                        return! Some cached |> loop
                | Reset ->
                    return! loop None
            }

            loop None)
    member _.Get() = agent.PostAndAsyncReply(Get)
    member _.Reset() = agent.Post Reset

[<AutoOpen>]
module internal ParseAndCheck =

    let userOpName = "Unknown"
    let suggestNamesForErrors = true
    let captureIdentifiersWhenParsing = false

    let measureTime (f: unit -> 'a) =
        let sw = Diagnostics.Stopwatch.StartNew()
        let res = f()
        sw.Stop()
        res, sw.ElapsedMilliseconds

    let measureTimeAsync (f: unit -> Async<'a>) = async {
        let sw = Diagnostics.Stopwatch.StartNew()
        let! res = f()
        sw.Stop()
        return res, sw.ElapsedMilliseconds
    }

    // Cache to store current compiler state.
    // In the case of type provider invalidation,
    // compiler state needs to be reset to recognize TP changes.
    let initializeCompilerState projectOptions reset = async {
        let tcConfig =
            let tcConfigB =
                TcConfigBuilder.CreateNew(
                    SimulatedMSBuildReferenceResolver.getResolver(),
                    defaultFSharpBinariesDir = FSharpCheckerResultsSettings.defaultFSharpBinariesDir,
                    reduceMemoryUsage = ReduceMemoryFlag.Yes,
                    implicitIncludeDir = Path.GetDirectoryName(projectOptions.ProjectFileName),
                    isInteractive = false,
                    isInvalidationSupported = true,
                    defaultCopyFSharpCore = CopyFSharpCoreFlag.No,
                    tryGetMetadataSnapshot = (fun _ -> None),
                    sdkDirOverride = None,
                    rangeForErrors = range0
                )
            let sourceFiles = projectOptions.SourceFiles |> Array.toList
            let argv = projectOptions.OtherOptions |> Array.toList
            let _sourceFiles = ApplyCommandLineArgs(tcConfigB, sourceFiles, argv)
            TcConfig.Create(tcConfigB, validate=false)

        let tcConfigP = TcConfigProvider.Constant(tcConfig)

        let dependencyProvider = new DependencyProvider()
        let! tcGlobals, tcImports =
            TcImports.BuildTcImports (tcConfigP, dependencyProvider)
            |> Async.AwaitNodeCode

        // Handle type provider invalidation by resetting compiler state
        tcImports.GetCcusExcludingBase()
        |> Seq.iter (fun ccu ->
            ccu.Deref.InvalidateEvent.Add(fun _ -> reset())
        )

        let assemblyName = projectOptions.ProjectFileName |> Path.GetFileNameWithoutExtension
        let tcInitial, openDecls0 = GetInitialTcEnv (assemblyName, rangeStartup, tcConfig, tcImports, tcGlobals)
        let tcInitialState = GetInitialTcState (rangeStartup, assemblyName, tcConfig, tcGlobals, tcImports, tcInitial, openDecls0)

        // parse cache, keyed on file name and source hash
        let parseCache = ConcurrentDictionary<string * int, FSharpParseFileResults>(HashIdentity.Structural)
        // type check cache, keyed on file name
        let checkCache = ConcurrentDictionary<string, (TcResult * TcErrors) * (TcState * ModuleNamesDict)>(HashIdentity.Structural)

        return {
            tcConfig = tcConfig
            tcGlobals = tcGlobals
            tcImports = tcImports
            tcInitialState = tcInitialState
            projectOptions = projectOptions
            parseCache = parseCache
            checkCache = checkCache
        }
    }

    let MakeProjectResults (projectFileName: string, parseResults: FSharpParseFileResults[], tcState: TcState, errors: FSharpDiagnostic[],
                            topAttrsOpt: TopAttribs option, tcImplFilesOpt: CheckedImplFile list option, compilerState) =
        let assemblyRef = mkSimpleAssemblyRef "stdin"
        let access = tcState.TcEnvFromImpls.AccessRights
        let symbolUses = Choice2Of2 TcSymbolUses.Empty
        let dependencyFiles = parseResults |> Seq.map (fun x -> x.DependencyFiles) |> Array.concat
        let getAssemblyData () = None
        let details = (compilerState.tcGlobals, compilerState.tcImports, tcState.Ccu, tcState.CcuSig, symbolUses, topAttrsOpt,
                        getAssemblyData, assemblyRef, access, tcImplFilesOpt, dependencyFiles, compilerState.projectOptions)
        let keepAssemblyContents = true
        FSharpCheckProjectResults (projectFileName, Some compilerState.tcConfig, keepAssemblyContents, errors, Some details)

    let ClearStaleCache (fileName: string, parsingOptions: FSharpParsingOptions, compilerState) =
        let fileIndex = parsingOptions.SourceFiles |> Array.findIndex ((=) fileName)
        let filesAbove = parsingOptions.SourceFiles |> Array.take fileIndex
        // backup all cached typecheck entries above file
        let cachedAbove = filesAbove |> Array.choose (fun key ->
            match compilerState.checkCache.TryGetValue(key) with
            | true, value -> Some (key, value)
            | false, _ -> None)
        // remove all parse cache entries with the same file name
        let staleParseKeys = compilerState.parseCache.Keys |> Seq.filter (fun (n,_) -> n = fileName) |> Seq.toArray
        staleParseKeys |> Array.iter (fun key -> compilerState.parseCache.TryRemove(key) |> ignore)
        compilerState.checkCache.Clear(); // clear all typecheck cache
        // restore all cached typecheck entries above file
        cachedAbove |> Array.iter (fun (key, value) -> compilerState.checkCache.TryAdd(key, value) |> ignore)

    let ParseFile (fileName: string, sourceHash: int, source: Lazy<string>, parsingOptions: FSharpParsingOptions, compilerState, ct) =
        let parseCacheKey = fileName, sourceHash
        compilerState.parseCache.GetOrAdd(parseCacheKey, fun _ ->
            ClearStaleCache(fileName, parsingOptions, compilerState)
            let sourceText = SourceText.ofString source.Value
            let flatErrors = compilerState.tcConfig.flatErrors
            let parseErrors, parseTreeOpt, anyErrors =
                ParseAndCheckFile.parseFile (sourceText, fileName, parsingOptions, userOpName, suggestNamesForErrors, flatErrors, captureIdentifiersWhenParsing, ct)
            let dependencyFiles = [||] // interactions have no dependencies
            FSharpParseFileResults (parseErrors, parseTreeOpt, anyErrors, dependencyFiles) )

    let TypeCheckOneInputEntry (parseResults: FSharpParseFileResults, tcSink: TcResultsSink, tcState: TcState, moduleNamesDict: ModuleNamesDict, compilerState) =
        let input = parseResults.ParseTree
        let diagnosticsOptions = compilerState.tcConfig.diagnosticsOptions
        let capturingLogger = CompilationDiagnosticLogger("TypeCheckFile", diagnosticsOptions)
        let diagnosticsLogger = GetDiagnosticsLoggerFilteringByScopedPragmas(false, input.ScopedPragmas, diagnosticsOptions, capturingLogger)
        use _scope = new CompilationGlobalsScope (diagnosticsLogger, BuildPhase.TypeCheck)

        let checkForErrors () = parseResults.ParseHadErrors || diagnosticsLogger.ErrorCount > 0
        let prefixPathOpt = None

        let input, moduleNamesDict = input |> DeduplicateParsedInputModuleName moduleNamesDict
        let tcResult, tcState =
            CheckOneInput (checkForErrors, compilerState.tcConfig, compilerState.tcImports, compilerState.tcGlobals, prefixPathOpt, tcSink, tcState, input)
            |> Cancellable.runWithoutCancellation

        let fileName = parseResults.FileName
        let flatErrors = compilerState.tcConfig.flatErrors
        let parseDiagnostics = capturingLogger.GetDiagnostics()
        let tcErrors = DiagnosticHelpers.CreateDiagnostics (diagnosticsOptions, false, fileName, parseDiagnostics, suggestNamesForErrors, flatErrors, None)
        (tcResult, tcErrors), (tcState, moduleNamesDict)

    let CheckFile (projectFileName: string, parseResults: FSharpParseFileResults, tcState: TcState, moduleNamesDict: ModuleNamesDict, compilerState) =
        let sink = TcResultsSinkImpl(compilerState.tcGlobals)
        let tcSink = TcResultsSink.WithSink sink
        let (tcResult, tcErrors), (tcState, moduleNamesDict) =
            TypeCheckOneInputEntry (parseResults, tcSink, tcState, moduleNamesDict, compilerState)
        let fileName = parseResults.FileName
        compilerState.checkCache.[fileName] <- ((tcResult, tcErrors), (tcState, moduleNamesDict))

        let loadClosure = None
        let keepAssemblyContents = true

        let tcEnvAtEnd, _topAttrs, implFile, ccuSigForFile = tcResult
        let errors = Array.append parseResults.Diagnostics tcErrors

        let scope = TypeCheckInfo (compilerState.tcConfig, compilerState.tcGlobals, ccuSigForFile, tcState.Ccu, compilerState.tcImports, tcEnvAtEnd.AccessRights,
                                projectFileName, fileName, compilerState.projectOptions, sink.GetResolutions(), sink.GetSymbolUses(), tcEnvAtEnd.NameEnv,
                                loadClosure, implFile, sink.GetOpenDeclarations())
        FSharpCheckFileResults (fileName, errors, Some scope, parseResults.DependencyFiles, None, keepAssemblyContents)

    let TypeCheckClosedInputSet (parseResults: FSharpParseFileResults[], tcState, compilerState, subscriber) =
        let cachedTypeCheck (tcState, moduleNamesDict) (parseRes: FSharpParseFileResults) =
            let checkCacheKey = parseRes.FileName

            let typeCheckOneInput _fileName =
                TypeCheckOneInputEntry (parseRes, TcResultsSink.NoSink, tcState, moduleNamesDict, compilerState)

            let (result, errors), (tcState, moduleNamesDict) = compilerState.checkCache.GetOrAdd(checkCacheKey, typeCheckOneInput)

            let _, _, implFile, _ = result
            match subscriber, implFile with
            | Some subscriber, Some implFile ->
                let cenv = SymbolEnv(compilerState.tcGlobals, tcState.Ccu, Some tcState.CcuSig, compilerState.tcImports)
                FSharpImplementationFileContents(cenv, implFile) |> subscriber
            | _ -> ()

            (result, errors), (tcState, moduleNamesDict)

        let results, (tcState, moduleNamesDict) =
            ((tcState, Map.empty), parseResults) ||> Array.mapFold cachedTypeCheck

        let tcResults, tcErrors = Array.unzip results
        let (tcEnvAtEndOfLastFile, topAttrs, implFiles, _ccuSigsForFiles), tcState =
            CheckMultipleInputsFinish(tcResults |> Array.toList, tcState)

        let tcState, declaredImpls, ccuContents = CheckClosedInputSetFinish (implFiles, tcState)
        tcState.Ccu.Deref.Contents <- ccuContents
        tcState, topAttrs, declaredImpls, tcEnvAtEndOfLastFile, moduleNamesDict, tcErrors

    /// Errors grouped by file, sorted by line, column
    let ErrorsByFile (fileNames: string[], errorList: FSharpDiagnostic[] list) =
        let errorMap = errorList |> Array.concat |> Array.groupBy (fun x -> x.FileName) |> Map.ofArray
        let errors = fileNames |> Array.choose errorMap.TryFind
        errors |> Array.iter (Array.sortInPlaceBy (fun x -> x.StartLine, x.StartColumn))
        errors |> Array.concat

type InteractiveChecker internal (compilerStateCache) =

    static member Create(projectOptions: FSharpProjectOptions) =
        Cache(initializeCompilerState projectOptions) |> InteractiveChecker

    /// Clears parse and typecheck caches.
    member _.ClearCache () = async {
        let! compilerState = compilerStateCache.Get()
        compilerState.parseCache.Clear()
        compilerState.checkCache.Clear()
    }

    member _.GetImportedAssemblies() = async {
        let! compilerState = compilerStateCache.Get()
        let tcImports = compilerState.tcImports
        let tcGlobals = compilerState.tcGlobals
        return
            tcImports.GetImportedAssemblies()
            |> List.map (fun x -> FSharpAssembly(tcGlobals, tcImports, x.FSharpViewOfMetadata))
    }

    /// Compile project to file. If project has already been type checked,
    /// check results will be taken from the cache.
    member _.Compile(fileNames: string[], sourceReader: string -> int * Lazy<string>, outFile: string) = async {
        let! ct = Async.CancellationToken
        let! compilerState = compilerStateCache.Get()
        let parsingOptions = FSharpParsingOptions.FromTcConfig(compilerState.tcConfig, fileNames, false)
        let parseResults = fileNames |> Array.map (fun fileName ->
            let sourceHash, source = sourceReader fileName
            ParseFile(fileName, sourceHash, source, parsingOptions, compilerState, ct))

        let (tcState, topAttrs, tcImplFiles, _tcEnvAtEnd, _moduleNamesDict, _tcErrors) =
            TypeCheckClosedInputSet (parseResults, compilerState.tcInitialState, compilerState, None)

        let ctok = CompilationThreadToken()
        let flatErrors = compilerState.tcConfig.flatErrors
        let errors, diagnosticsLogger, _loggerProvider = CompileHelpers.mkCompilationDiagnosticsHandlers(flatErrors)
        let exitCode =
            CompileHelpers.tryCompile diagnosticsLogger (fun exiter ->
                CompileFromTypedAst (ctok, compilerState.tcGlobals, compilerState.tcImports, tcState.Ccu,
                    tcImplFiles, topAttrs, compilerState.tcConfig, outFile, diagnosticsLogger, exiter))

        return errors.ToArray(), exitCode
    }

    /// Parses and checks the whole project, good for compilers (Fable etc.)
    /// Does not retain name resolutions and symbol uses which are quite memory hungry (so no intellisense etc.).
    /// Already parsed files will be cached so subsequent compilations will be faster.
    member _.ParseAndCheckProject (projectFileName: string, fileNames: string[], sourceReader: string -> int * Lazy<string>,
                                    ?lastFile: string, ?subscriber: FSharpImplementationFileContents -> unit) = async {
        let! ct = Async.CancellationToken
        let! compilerState = compilerStateCache.Get()
        // parse files
        let parsingOptions = FSharpParsingOptions.FromTcConfig(compilerState.tcConfig, fileNames, false)
        let parseResults =
            let fileNames =
                match lastFile with
                | None -> fileNames
                | Some fileName ->
                    let fileIndex = fileNames |> Array.findIndex ((=) fileName)
                    fileNames |> Array.take (fileIndex + 1)

            let parseFile fileName =
                let sourceHash, source = sourceReader fileName
                ParseFile(fileName, sourceHash, source, parsingOptions, compilerState, ct)

            // Don't parallelize if we have cached files, as it would create issues with invalidation
            if compilerState.parseCache.Count = 0 then
                fileNames |> Array.Parallel.map parseFile
            else
                fileNames |> Array.map parseFile

        // type check files
        let (tcState, topAttrs, tcImplFiles, _tcEnvAtEnd, _moduleNamesDict, tcErrors) =
            TypeCheckClosedInputSet (parseResults, compilerState.tcInitialState, compilerState, subscriber)

        // make project results
        let parseErrors = parseResults |> Array.collect (fun p -> p.Diagnostics)
        let typedErrors = tcErrors |> Array.concat
        let errors = ErrorsByFile (fileNames, [ parseErrors; typedErrors ])
        let projectResults = MakeProjectResults (projectFileName, parseResults, tcState, errors, Some topAttrs, Some tcImplFiles, compilerState)

        return projectResults
    }

    /// Parses and checks file in project, will compile and cache all the files up to this one
    /// (if not already done before), or fetch them from cache. Returns partial project results,
    /// up to and including the file requested. Returns parse and typecheck results containing
    /// name resolutions and symbol uses for the file requested only, so intellisense etc. works.
    member _.ParseAndCheckFileInProject (projectFileName: string, fileNames: string[], sourceReader: string -> int * Lazy<string>, fileName: string) = async {
        let! ct = Async.CancellationToken
        let! compilerState = compilerStateCache.Get()

        // get files before file
        let fileIndex = fileNames |> Array.findIndex ((=) fileName)
        let fileNamesBeforeFile = fileNames |> Array.take fileIndex

        // parse files before file
        let parsingOptions = FSharpParsingOptions.FromTcConfig(compilerState.tcConfig, fileNames, false)
        let parseFile fileName =
            let sourceHash, source = sourceReader fileName
            ParseFile (fileName, sourceHash, source, parsingOptions, compilerState, ct)
        let parseResults = fileNamesBeforeFile |> Array.map parseFile

        // type check files before file
        let tcState, topAttrs, tcImplFiles, _tcEnvAtEnd, moduleNamesDict, tcErrors =
            TypeCheckClosedInputSet (parseResults, compilerState.tcInitialState, compilerState, None)

        // parse and type check file
        let parseFileResults = parseFile fileName
        let checkFileResults = CheckFile (projectFileName, parseFileResults, tcState, moduleNamesDict, compilerState)
        let (tcResult, _tcErrors), (tcState, _moduleNamesDict) = compilerState.checkCache.[fileName]
        let _tcEnvAtEndFile, topAttrsFile, implFile, _ccuSigForFile = tcResult

        // collect errors
        let parseErrorsBefore = parseResults |> Array.collect (fun p -> p.Diagnostics)
        let typedErrorsBefore = tcErrors |> Array.concat
        let newErrors = checkFileResults.Diagnostics
        let errors = ErrorsByFile (fileNames, [ parseErrorsBefore; typedErrorsBefore; newErrors ])

        // make partial project results
        let parseResults = Array.append parseResults [| parseFileResults |]
        let tcImplFiles = List.append tcImplFiles (Option.toList implFile)
        let topAttrs = CombineTopAttrs topAttrsFile topAttrs
        let projectResults = MakeProjectResults (projectFileName, parseResults, tcState, errors, Some topAttrs, Some tcImplFiles, compilerState)

        return (parseFileResults, checkFileResults, projectResults)
    }

    /// Find the transitive dependent files of the current file based on the untyped syntax tree.
    member _.GetDependentFiles(currentFileName: string, fileNames: string[], sourceReader: string -> int * Lazy<string>) = async {
        // parse files
        let! ct = Async.CancellationToken
        let! compilerState = compilerStateCache.Get()
        // parse files
        let parsingOptions = FSharpParsingOptions.FromTcConfig(compilerState.tcConfig, fileNames, false)
        let parseFile fileName =
            let sourceHash, source = sourceReader fileName
            ParseFile (fileName, sourceHash, source, parsingOptions, compilerState, ct)

        // TODO: not sure if parse cache issues still applies
        let parseResults = fileNames |> Array.Parallel.map parseFile
        let sourceFiles: FileInProject array =
            parseResults
            |> Array.mapi (fun idx (parseResults: FSharpParseFileResults) ->
                let input = parseResults.ParseTree
                {
                    Idx = idx
                    FileName = input.FileName
                    ParsedInput = input
                })

        let currentFileIdx = Array.IndexOf(fileNames, currentFileName)

        let filePairs = FilePairMap(sourceFiles)
        let graph, _trie = DependencyResolution.mkGraph filePairs sourceFiles        
        let findTransitiveDependentFiles (startNode : FileIndex) : FileIndex array =
            let rec dfs (node : FileIndex) (visited : Set<FileIndex>) (acc : FileIndex array) : FileIndex array =
                if (Set.contains node visited) then
                    acc
                else
                    let newVisited = Set.add node visited

                    let consumers =
                        // Last node in the project cannot have 
                        if node = graph.Count - 1 then
                            acc
                        else
                            // Look if the next nodes depend on the current node
                            [| (node + 1) .. (graph.Count - 1) |]
                            |> Array.fold
                                (fun innerAcc nextIdx ->
                                    if not (Array.contains node graph.[nextIdx]) then
                                        innerAcc
                                    else
                                        dfs nextIdx newVisited innerAcc)
                                acc

                    [| yield node; yield! consumers |]

            dfs startNode Set.empty Array.empty
            |> Array.sort

        let dependentFiles =
            findTransitiveDependentFiles currentFileIdx
            |> Array.sort
            |> Array.map (fun idx -> Array.item idx fileNames)

        return dependentFiles
    }
