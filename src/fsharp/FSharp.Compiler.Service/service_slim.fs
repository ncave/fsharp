// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace FSharp.Compiler.SourceCodeServices

open System
open System.Collections.Concurrent
open System.IO

open FSharp.Compiler 
open FSharp.Compiler.AbstractIL
open FSharp.Compiler.AbstractIL.IL
open FSharp.Compiler.AbstractIL.ILBinaryReader
open FSharp.Compiler.AbstractIL.Internal.Library
open FSharp.Compiler.AbstractIL.Internal.Utils
open FSharp.Compiler.CheckExpressions
open FSharp.Compiler.CheckDeclarations
open FSharp.Compiler.CompilerConfig
open FSharp.Compiler.CompilerDiagnostics
open FSharp.Compiler.CompilerGlobalState
open FSharp.Compiler.CompilerImports
open FSharp.Compiler.CompilerOptions
open FSharp.Compiler.Driver
open FSharp.Compiler.ErrorLogger
open FSharp.Compiler.Lib
open FSharp.Compiler.NameResolution
open FSharp.Compiler.ParseAndCheckInputs
open FSharp.Compiler.Range
open FSharp.Compiler.ScriptClosure
open FSharp.Compiler.SyntaxTree
open FSharp.Compiler.TcGlobals 
open FSharp.Compiler.Text
open FSharp.Compiler.TypedTree
open FSharp.Compiler.TypedTreeBasics
open FSharp.Compiler.TypedTreeOps

open Microsoft.DotNet.DependencyManager

open Internal.Utilities
open Internal.Utilities.Collections

//-------------------------------------------------------------------------
// InteractiveChecker
//-------------------------------------------------------------------------

type internal TcResult = TcEnv * TopAttribs * TypedImplFile option * ModuleOrNamespaceType
type internal TcErrors = FSharpErrorInfo[]

type internal CompilerState = {
    tcConfig : TcConfig
    tcGlobals : TcGlobals
    tcImports : TcImports
    tcInitialState : TcState
    ctok : CompilationThreadToken
    parseCache : ConcurrentDictionary<string * int, FSharpParseFileResults>
    checkCache : ConcurrentDictionary<string, (TcResult * TcErrors) * (TcState * ModuleNamesDict)>
}

// Cache to store current compiler state.
// In the case of type provider invalidation,
// compiler state needs to be reset to recognize TP changes.
type internal CompilerStateCache(projectOptions: FSharpProjectOptions) as this =

    let initializeCompilerState() =
        let tcConfig =
            let tcConfigB = { TcConfigBuilder.Initial with isInvalidationSupported = true }
            tcConfigB.implicitIncludeDir <- Path.GetDirectoryName(projectOptions.ProjectFileName)
            tcConfigB.legacyReferenceResolver <- SimulatedMSBuildReferenceResolver.getResolver()
            let sourceFiles = projectOptions.SourceFiles |> Array.toList
            let argv = projectOptions.OtherOptions |> Array.toList
            let _sourceFiles = ApplyCommandLineArgs(tcConfigB, sourceFiles, argv)
            TcConfig.Create(tcConfigB, validate=false)

        let tcConfigP = TcConfigProvider.Constant(tcConfig)

        let ctok = CompilationThreadToken()
        let dependencyProvider = new DependencyProvider()
        let tcGlobals, tcImports =
            TcImports.BuildTcImports (ctok, tcConfigP, dependencyProvider)
            |> Cancellable.runWithoutCancellation

        // Handle type provider invalidation by resetting compiler state
        tcImports.GetCcusExcludingBase()
        |> Seq.iter (fun ccu ->
            ccu.Deref.InvalidateEvent.Add(fun _ -> this.Reset())
        )

        let niceNameGen = NiceNameGenerator()
        let assemblyName = projectOptions.ProjectFileName |> Path.GetFileNameWithoutExtension
        let tcInitialEnv = GetInitialTcEnv (assemblyName, rangeStartup, tcConfig, tcImports, tcGlobals)
        let tcInitialState = GetInitialTcState (rangeStartup, assemblyName, tcConfig, tcGlobals, tcImports, niceNameGen, tcInitialEnv)

        // parse cache, keyed on file name and source hash
        let parseCache = ConcurrentDictionary<string * int, FSharpParseFileResults>(HashIdentity.Structural)
        // type check cache, keyed on file name
        let checkCache = ConcurrentDictionary<string, (TcResult * TcErrors) * (TcState * ModuleNamesDict)>(HashIdentity.Structural)

        {
            tcConfig = tcConfig
            tcGlobals = tcGlobals
            tcImports = tcImports
            tcInitialState = tcInitialState
            ctok = ctok
            parseCache = parseCache
            checkCache = checkCache
        }

    // Lazily evaluated in case multiple TP invalidations are triggered before next compilation requested
    let mutable compilerStateLazy = lazy initializeCompilerState()
    let lockObj = obj()

    member x.Get() =
        lock lockObj (fun () -> compilerStateLazy.Value)
    member x.Reset() =
        lock lockObj (fun () -> compilerStateLazy <- lazy initializeCompilerState())

type InteractiveChecker internal (compilerStateCache) =
    let userOpName = "Unknown"
    let suggestNamesForErrors = true

    static member Create(projectOptions: FSharpProjectOptions) =
        InteractiveChecker(CompilerStateCache(projectOptions))

    member private x.MakeProjectResults (projectFileName: string, parseResults: FSharpParseFileResults[], tcState: TcState, errors: FSharpErrorInfo[],
                                         symbolUses: TcSymbolUses list, topAttrsOpt: TopAttribs option, tcImplFilesOpt: TypedImplFile list option,
                                         compilerState) =
        let assemblyRef = mkSimpleAssemblyRef "stdin"
        let assemblyDataOpt = None
        let access = tcState.TcEnvFromImpls.AccessRights
        let dependencyFiles = parseResults |> Seq.map (fun x -> x.DependencyFiles) |> Array.concat
        let details = (compilerState.tcGlobals, compilerState.tcImports, tcState.Ccu, tcState.CcuSig, symbolUses, topAttrsOpt, assemblyDataOpt, assemblyRef, access, tcImplFilesOpt, dependencyFiles)
        let keepAssemblyContents = true
        FSharpCheckProjectResults (projectFileName, Some compilerState.tcConfig, keepAssemblyContents, errors, Some details)

    member private x.ClearStaleCache (fileName: string, parsingOptions: FSharpParsingOptions, compilerState) =
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

    member private x.ParseFile (fileName: string, sourceHash: int, source: Lazy<string>, parsingOptions: FSharpParsingOptions, compilerState) =
        let parseCacheKey = fileName, sourceHash
        compilerState.parseCache.GetOrAdd(parseCacheKey, fun _ ->
            x.ClearStaleCache(fileName, parsingOptions, compilerState)
            let sourceText = SourceText.ofString source.Value
            let parseErrors, parseTreeOpt, anyErrors = ParseAndCheckFile.parseFile (sourceText, fileName, parsingOptions, userOpName, suggestNamesForErrors)
            let dependencyFiles = [||] // interactions have no dependencies
            FSharpParseFileResults (parseErrors, parseTreeOpt, anyErrors, dependencyFiles) )

    member private x.TypeCheckOneInput (parseResults: FSharpParseFileResults, tcSink: TcResultsSink, tcState: TcState, moduleNamesDict: ModuleNamesDict, compilerState) =
        let input = parseResults.ParseTree.Value
        let capturingErrorLogger = CompilationErrorLogger("TypeCheckFile", compilerState.tcConfig.errorSeverityOptions)
        let errorLogger = GetErrorLoggerFilteringByScopedPragmas(false, GetScopedPragmasForInput(input), capturingErrorLogger)
        use _errorScope = new CompilationGlobalsScope (errorLogger, BuildPhase.TypeCheck)

        let checkForErrors () = parseResults.ParseHadErrors || errorLogger.ErrorCount > 0
        let prefixPathOpt = None

        let input, moduleNamesDict = input |> DeduplicateParsedInputModuleName moduleNamesDict
        let tcResult, tcState =
            TypeCheckOneInputEventually (checkForErrors, compilerState.tcConfig, compilerState.tcImports, compilerState.tcGlobals, prefixPathOpt, tcSink, tcState, input, false)
            |> Eventually.force compilerState.ctok

        let fileName = parseResults.FileName
        let tcErrors = ErrorHelpers.CreateErrorInfos (compilerState.tcConfig.errorSeverityOptions, false, fileName, (capturingErrorLogger.GetErrors()), suggestNamesForErrors)
        (tcResult, tcErrors), (tcState, moduleNamesDict)

    member private x.CheckFile (projectFileName: string, parseResults: FSharpParseFileResults, tcState: TcState, moduleNamesDict: ModuleNamesDict, compilerState) =
        match parseResults.ParseTree with
        | Some _input ->
            let sink = TcResultsSinkImpl(compilerState.tcGlobals)
            let tcSink = TcResultsSink.WithSink sink
            let (tcResult, tcErrors), (tcState, moduleNamesDict) =
                x.TypeCheckOneInput (parseResults, tcSink, tcState, moduleNamesDict, compilerState)
            let fileName = parseResults.FileName
            compilerState.checkCache.[fileName] <- ((tcResult, tcErrors), (tcState, moduleNamesDict))

            let loadClosure = None
            let keepAssemblyContents = true

            let tcEnvAtEnd, _topAttrs, implFile, ccuSigForFile = tcResult
            let errors = Array.append parseResults.Errors tcErrors

            let scope = TypeCheckInfo (compilerState.tcConfig, compilerState.tcGlobals, ccuSigForFile, tcState.Ccu, compilerState.tcImports, tcEnvAtEnd.AccessRights,
                                    projectFileName, fileName, sink.GetResolutions(), sink.GetSymbolUses(), tcEnvAtEnd.NameEnv,
                                    loadClosure, implFile, sink.GetOpenDeclarations())
            FSharpCheckFileResults (fileName, errors, Some scope, parseResults.DependencyFiles, None, keepAssemblyContents)
            |> Some
        | None ->
            None

    member private x.TypeCheckClosedInputSet (parseResults: FSharpParseFileResults[], tcState, compilerState) =
        let cachedTypeCheck (tcState, moduleNamesDict) (parseRes: FSharpParseFileResults) =
            let checkCacheKey = parseRes.FileName
            let typeCheckOneInput _fileName =
                x.TypeCheckOneInput (parseRes, TcResultsSink.NoSink, tcState, moduleNamesDict, compilerState)
            compilerState.checkCache.GetOrAdd(checkCacheKey, typeCheckOneInput)
        let results, (tcState, moduleNamesDict) =
            ((tcState, Map.empty), parseResults) ||> Array.mapFold cachedTypeCheck
        let tcResults, tcErrors = Array.unzip results
        let (tcEnvAtEndOfLastFile, topAttrs, implFiles, _ccuSigsForFiles), tcState =
            TypeCheckMultipleInputsFinish(tcResults |> Array.toList, tcState)
        let tcState, declaredImpls = TypeCheckClosedInputSetFinish (implFiles, tcState)
        tcState, topAttrs, declaredImpls, tcEnvAtEndOfLastFile, moduleNamesDict, tcErrors

    /// Errors grouped by file, sorted by line, column
    member private x.ErrorsByFile (fileNames: string[], errorList: FSharpErrorInfo[] list) =
        let errorMap = errorList |> Array.concat |> Array.groupBy (fun x -> x.FileName) |> Map.ofArray
        let errors = fileNames |> Array.choose errorMap.TryFind
        errors |> Array.iter (Array.sortInPlaceBy (fun x -> x.StartLineAlternate, x.StartColumn))
        errors |> Array.concat

    /// Clears parse and typecheck caches.
    member x.ClearCache () =
        let compilerState = compilerStateCache.Get()
        compilerState.parseCache.Clear()
        compilerState.checkCache.Clear()

    /// Parses and checks the whole project, good for compilers (Fable etc.)
    /// Does not retain name resolutions and symbol uses which are quite memory hungry (so no intellisense etc.).
    /// Already parsed files will be cached so subsequent compilations will be faster.
    member x.ParseAndCheckProject (projectFileName: string, fileNames: string[], sourceReader: string->int*Lazy<string>) =
        let compilerState = compilerStateCache.Get()
        // parse files
        let parsingOptions = FSharpParsingOptions.FromTcConfig(compilerState.tcConfig, fileNames, false)
        let parseResults = fileNames |> Array.map (fun fileName ->
            let sourceHash, source = sourceReader fileName
            x.ParseFile(fileName, sourceHash, source, parsingOptions, compilerState))

        // type check files
        let tcState, topAttrs, tcImplFiles, _tcEnvAtEnd, _moduleNamesDict, tcErrors =
            x.TypeCheckClosedInputSet (parseResults, compilerState.tcInitialState, compilerState)

        // make project results
        let parseErrors = parseResults |> Array.collect (fun p -> p.Errors)
        let typedErrors = tcErrors |> Array.concat
        let errors = x.ErrorsByFile (fileNames, [ parseErrors; typedErrors ])
        let symbolUses = [] //TODO:
        let projectResults = x.MakeProjectResults (projectFileName, parseResults, tcState, errors, symbolUses, Some topAttrs, Some tcImplFiles, compilerState)

        projectResults

    /// Parses and checks file in project, will compile and cache all the files up to this one
    /// (if not already done before), or fetch them from cache. Returns partial project results,
    /// up to and including the file requested. Returns parse and typecheck results containing
    /// name resolutions and symbol uses for the file requested only, so intellisense etc. works.
    member x.ParseAndCheckFileInProject (fileName: string, projectFileName: string, fileNames: string[], sources: string[]) =
        let compilerState = compilerStateCache.Get()
        // get files before file
        let fileIndex = fileNames |> Array.findIndex ((=) fileName)
        let fileNamesBeforeFile = fileNames |> Array.take fileIndex
        let sourcesBeforeFile = sources |> Array.take fileIndex

        // parse files before file
        let parsingOptions = FSharpParsingOptions.FromTcConfig(compilerState.tcConfig, fileNames, false)
        let parseFile (fileName, source) = x.ParseFile (fileName, hash source, lazy source, parsingOptions, compilerState)
        let parseResults = Array.zip fileNamesBeforeFile sourcesBeforeFile |> Array.map parseFile

        // type check files before file
        let tcState, topAttrs, tcImplFiles, _tcEnvAtEnd, moduleNamesDict, tcErrors =
            x.TypeCheckClosedInputSet (parseResults, compilerState.tcInitialState, compilerState)

        // parse and type check file
        let parseFileResults = parseFile (fileName, sources.[fileIndex])
        let checkFileResults = x.CheckFile (projectFileName, parseFileResults, tcState, moduleNamesDict, compilerState)
        let (tcResult, _tcErrors), (tcState, _moduleNamesDict) = compilerState.checkCache.[fileName]
        let _tcEnvAtEndFile, topAttrsFile, implFile, _ccuSigForFile = tcResult

        // collect errors
        let parseErrorsBefore = parseResults |> Array.collect (fun p -> p.Errors)
        let typedErrorsBefore = tcErrors |> Array.concat
        let newErrors = match checkFileResults with | Some res -> res.Errors | None -> [||]
        let errors = x.ErrorsByFile (fileNames, [ parseErrorsBefore; typedErrorsBefore; newErrors ])

        // make partial project results
        let parseResults = Array.append parseResults [| parseFileResults |]
        let tcImplFiles = List.append tcImplFiles (Option.toList implFile)
        let topAttrs = CombineTopAttrs topAttrsFile topAttrs
        let symbolUses = [] //TODO:
        let projectResults = x.MakeProjectResults (projectFileName, parseResults, tcState, errors, symbolUses, Some topAttrs, Some tcImplFiles, compilerState)

        parseFileResults, checkFileResults, projectResults
