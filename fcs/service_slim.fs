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

type internal TcResult = PartialResult
type internal TcErrors = FSharpDiagnostic[]

/// The result of checking one file over the dependency graph, kept for reuse while
/// neither the file nor anything it depends on changes.
type internal GraphCheckEntry = {
    parseResults: FSharpParseFileResults
    qualifiedName: string
    fileIndex: int
    /// Identifies the finisher: a new one gets a new generation.
    generation: int
    /// The files this one depends on, with the generations of the finishers it was checked against.
    dependencyGenerations: (string * int)[]
    /// Adds the file's signature to the state its dependents are checked in. Kept from an earlier check while later
    /// checks of the file give the same signature, so the dependents' results stay valid.
    finisher: Finisher<NodeToTypeCheck, TcState, PartialResult>
    /// The implementation to report, from the latest check of the file.
    implFile: CheckedImplFile option
    signature: Lazy<string option>
    tcErrors: TcErrors
}

/// How a file's result was obtained in a check over the dependency graph.
type internal GraphCheckOutcome =
    /// The file is unchanged, and none of the files it depends on, now or in the earlier check, was replaced.
    | Reused of GraphCheckEntry
    /// The file changed but its signature did not, and none of the files it depends on was replaced. The earlier
    /// finisher stays, so the file's dependents can be reused; the new implementation is reported.
    | Kept of GraphCheckEntry * CheckedImplFile
    /// The file was checked, and its dependents see the new result.
    | Replaced of Finisher<NodeToTypeCheck, TcState, PartialResult> * dependencyGenerations: (string * int)[]

type internal CompilerState = {
    tcConfig: TcConfig
    tcGlobals: TcGlobals
    tcImports: TcImports
    tcInitialState: TcState
    projectOptions: FSharpProjectOptions
    parseCache: ConcurrentDictionary<string * int, FSharpParseFileResults>
    checkCache: ConcurrentDictionary<string, (TcResult * TcErrors) * (TcState * ModuleNamesDict)>
    graphCheckCache: ConcurrentDictionary<string, GraphCheckEntry>
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

/// What the files that depend on a file see of it: the types, values, members and attributes its signature declares,
/// without ranges or stamps, and with type parameters numbered by position. Equal fingerprints mean the dependents
/// would check the same against either signature. Anything it cannot describe exactly gives None, so the file
/// always counts as changed.
module internal SignatureFingerprint =

    exception private NotDescribable

    let compute (mty: ModuleOrNamespaceType) (topAttrs: TopAttribs) : string option =
        let sb = Text.StringBuilder()
        let add (s: string) = sb.Append(s).Append('|') |> ignore
        let typarNumbers = Collections.Generic.Dictionary<Typar, int>(HashIdentity.Reference)

        let rec ty (t: TType) =
            match stripTyparEqns t with
            | TType_app (tcref, tinst, nullness) ->
                add "app"
                add (fullDisplayTextOfTyconRef tcref)
                nullnessOf nullness
                tys tinst
            | TType_fun (domainTy, rangeTy, nullness) ->
                add "fun"
                ty domainTy
                ty rangeTy
                nullnessOf nullness
            | TType_tuple (tupInfo, elementTys) ->
                add (if evalTupInfoIsStruct tupInfo then "struct tuple" else "tuple")
                tys elementTys
            | TType_anon (anonInfo, fieldTys) ->
                add "anon"
                add anonInfo.Assembly.AssemblyName
                add (string (evalAnonInfoIsStruct anonInfo))
                for name in anonInfo.SortedNames do add name
                tys fieldTys
            | TType_var (tp, nullness) ->
                typar tp
                nullnessOf nullness
            | TType_forall (tps, bodyTy) ->
                add "forall"
                typars tps
                ty bodyTy
            | TType_measure m ->
                add "measure"
                measure m
            | TType_ucase (ucref, tinst) ->
                add "ucase"
                add (fullDisplayTextOfTyconRef ucref.TyconRef)
                add ucref.CaseName
                tys tinst

        and tys (l: TType list) =
            add (string l.Length)
            List.iter ty l

        and nullnessOf (nullness: Nullness) = add (string (nullness.Evaluate()))

        and measure (m: Measure) =
            match stripUnitEqns m with
            | Measure.Var tp -> typar tp
            | Measure.Const (tcref, _) -> add (fullDisplayTextOfTyconRef tcref)
            | Measure.Prod (m1, m2, _) ->
                add "*"
                measure m1
                measure m2
            | Measure.Inv m1 ->
                add "/"
                measure m1
            | Measure.One _ -> add "1"
            | Measure.RationalPower (m1, power) ->
                add "^"
                measure m1
                add (sprintf "%A" power)

        // A type parameter is described once, where it first appears, and by its number after that.
        and typar (tp: Typar) =
            match typarNumbers.TryGetValue tp with
            | true, n -> add ("'" + string n)
            | _ ->
                let n = typarNumbers.Count
                typarNumbers[tp] <- n
                add ("'" + string n + " new")
                add (sprintf "%A %A" tp.StaticReq tp.Kind)
                add (string tp.Constraints.Length)
                List.iter constr tp.Constraints

        and typars (tps: Typars) =
            add (string tps.Length)
            List.iter typar tps

        and constr (c: TyparConstraint) =
            match c with
            | TyparConstraint.CoercesTo (t, _) ->
                add ":>"
                ty t
            | TyparConstraint.DefaultsTo (priority, t, _) ->
                add "default"
                add (string priority)
                ty t
            | TyparConstraint.MayResolveMember (TTrait (supportTys, memberName, memberFlags, argTys, returnTy, _, _, _), _) ->
                add "member"
                tys supportTys
                add memberName
                add (sprintf "%A" memberFlags)
                tys argTys
                optTy returnTy
            | TyparConstraint.SimpleChoice (choiceTys, _) ->
                add "choice"
                tys choiceTys
            | TyparConstraint.IsEnum (t, _) ->
                add "enum"
                ty t
            | TyparConstraint.IsDelegate (argsTy, retTy, _) ->
                add "delegate"
                ty argsTy
                ty retTy
            | TyparConstraint.SupportsNull _ -> add "null"
            | TyparConstraint.NotSupportsNull _ -> add "not null"
            | TyparConstraint.IsNonNullableStruct _ -> add "struct"
            | TyparConstraint.IsReferenceType _ -> add "not struct"
            | TyparConstraint.RequiresDefaultConstructor _ -> add "new"
            | TyparConstraint.SupportsComparison _ -> add "comparison"
            | TyparConstraint.SupportsEquality _ -> add "equality"
            | TyparConstraint.IsUnmanaged _ -> add "unmanaged"
            | TyparConstraint.AllowsRefStruct _ -> add "allows ref struct"

        and optTy (t: TType option) =
            match t with
            | Some t -> ty t
            | None -> add "-"

        and access (TAccess paths) =
            add (string paths.Length)
            for path in paths do add (sprintf "%A" path.AccessPath)

        and attribs (l: Attribs) =
            add (string l.Length)
            for Attrib (tcref, _, args, namedArgs, appliedToAccessor, targets, _) in l do
                add (fullDisplayTextOfTyconRef tcref)
                add (sprintf "%b %A" appliedToAccessor targets)
                add (string args.Length)
                for AttribExpr (_, e) in args do attribExpr e
                add (string namedArgs.Length)
                for AttribNamedArg (name, t, isField, AttribExpr (_, e)) in namedArgs do
                    add name
                    ty t
                    add (string isField)
                    attribExpr e

        and attribExpr (e: Expr) =
            match e with
            | Expr.Const (c, _, t) ->
                add (sprintf "%A" c)
                ty t
            | Expr.Op (TOp.Coerce, tinst, [ e ], _) ->
                add "coerce"
                tys tinst
                attribExpr e
            | Expr.Op (TOp.Array, tinst, elements, _) ->
                add "array"
                tys tinst
                add (string elements.Length)
                List.iter attribExpr elements
            | Expr.App (Expr.Val (vref, _, _), _, tinst, args, _) ->
                add (vref.LogicalName)
                tys tinst
                add (string args.Length)
                List.iter attribExpr args
            | _ -> raise NotDescribable

        and argInfo (info: ArgReprInfo) =
            add (match info.Name with Some id -> id.idText | None -> "-")
            attribs (info.Attribs.AsList())

        and slotSig (TSlotSig (name, declaringTy, classTps, methodTps, paramGroups, returnTy)) =
            add name
            ty declaringTy
            typars classTps
            typars methodTps
            add (string paramGroups.Length)
            for group in paramGroups do
                add (string group.Length)
                for TSlotParam (paramName, paramTy, isIn, isOut, isOptional, paramAttribs) in group do
                    add (defaultArg paramName "-")
                    ty paramTy
                    add (sprintf "%b %b %b" isIn isOut isOptional)
                    attribs paramAttribs
            optTy returnTy

        and value (v: Val) =
            add "val"
            add v.LogicalName
            add (defaultArg v.ValCompiledName "-")
            access v.Accessibility
            ty v.Type
            attribs v.Attribs
            add (sprintf "%A %A %b %b %b" v.LiteralValue v.InlineInfo v.IsMutable v.IsCompilerGenerated v.IsExtensionMember)

            match v.ValReprInfo with
            | Some (ValReprInfo (typarInfos, argGroups, result)) ->
                add (string typarInfos.Length)
                add (string argGroups.Length)
                for group in argGroups do
                    add (string group.Length)
                    List.iter argInfo group
                argInfo result
            | None -> add "-"

            match v.MemberInfo with
            | Some memberInfo ->
                add (fullDisplayTextOfTyconRef memberInfo.ApparentEnclosingEntity)
                add (sprintf "%A %b" memberInfo.MemberFlags memberInfo.IsImplemented)
                add (string memberInfo.ImplementedSlotSigs.Length)
                List.iter slotSig memberInfo.ImplementedSlotSigs
            | None -> add "-"

        and field (f: RecdField) =
            add f.LogicalName
            ty f.FormalType
            add (sprintf "%b %b %b %A" f.IsMutable f.IsStatic f.IsVolatile f.LiteralValue)
            access f.Accessibility
            attribs f.PropertyAttribs
            attribs f.FieldAttribs

        and entity (e: Entity) =
            add "entity"
            add e.LogicalName
            add e.CompiledName
            access e.Accessibility
            access e.TypeReprAccessibility
            attribs e.Attribs
            typars e.Typars

            if e.IsModuleOrNamespace then
                add (sprintf "%A" e.ModuleOrNamespaceType.ModuleOrNamespaceKind)
                moduleOrNamespace e.ModuleOrNamespaceType
            else
                optTy e.TypeAbbrev

                match e.TypeReprInfo with
                | TFSharpTyconRepr data ->
                    match data.fsobjmodel_kind with
                    | TFSharpRecord -> add "record"
                    | TFSharpUnion -> add "union"
                    | TFSharpClass -> add "class"
                    | TFSharpInterface -> add "interface"
                    | TFSharpStruct -> add "struct"
                    | TFSharpEnum -> add "enum"
                    | TFSharpDelegate ss ->
                        add "delegate"
                        slotSig ss
                | TMeasureableRepr t ->
                    add "measureable"
                    ty t
                | TNoRepr -> add "no repr"
                | TILObjectRepr _
                | TAsmRepr _
                | TProvidedTypeRepr _
                | TProvidedNamespaceRepr _ -> raise NotDescribable

                let contents = e.TypeContents
                optTy contents.tcaug_super
                add (string contents.tcaug_interfaces.Length)
                for interfaceTy, compilerGenerated, _ in contents.tcaug_interfaces do
                    ty interfaceTy
                    add (string compilerGenerated)
                add (sprintf "%b %b %b %b %b" contents.tcaug_compare.IsSome contents.tcaug_compare_withc.IsSome
                        contents.tcaug_equals.IsSome contents.tcaug_hash_and_equals_withc.IsSome contents.tcaug_abstract)

                add (string e.AllFieldsArray.Length)
                Array.iter field e.AllFieldsArray
                add (string e.UnionCasesArray.Length)
                for uc in e.UnionCasesArray do
                    add uc.LogicalName
                    add uc.CompiledName
                    access uc.Accessibility
                    attribs uc.Attribs
                    ty uc.ReturnType
                    add (string uc.RecdFieldsArray.Length)
                    Array.iter field uc.RecdFieldsArray

                match e.ExceptionInfo with
                | TExnAbbrevRepr tcref -> add (fullDisplayTextOfTyconRef tcref)
                | TExnFresh fields ->
                    add "exception"
                    add (string fields.FieldsByIndex.Length)
                    Array.iter field fields.FieldsByIndex
                | TExnNone -> add "-"
                | TExnAsmRepr _ -> raise NotDescribable

        and moduleOrNamespace (m: ModuleOrNamespaceType) =
            let entities = m.AllEntities |> Seq.toList
            add (string entities.Length)
            List.iter entity entities
            let vals = m.AllValsAndMembers |> Seq.toList
            add (string vals.Length)
            List.iter value vals

        try
            moduleOrNamespace mty
            attribs topAttrs.mainMethodAttrs
            attribs topAttrs.netModuleAttrs
            attribs topAttrs.assemblyAttrs
            Some (sb.ToString())
        with NotDescribable ->
            None

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
                    implicitIncludeDir = !! Path.GetDirectoryName(projectOptions.ProjectFileName),
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

        // Handle type provider invalidation by resetting compiler state
        tcImports.GetCcusExcludingBase()
        |> Seq.iter (fun ccu ->
            ccu.Deref.InvalidateEvent.Add(fun _ -> reset())
        )

        let assemblyName = !! Path.GetFileNameWithoutExtension(projectOptions.ProjectFileName)
        let tcInitial, openDecls0 = GetInitialTcEnv (assemblyName, rangeStartup, tcConfig, tcImports, tcGlobals)
        let tcInitialState = GetInitialTcState (rangeStartup, assemblyName, tcConfig, tcGlobals, tcImports, tcInitial, openDecls0)

        // parse cache, keyed on file name and source hash
        let parseCache = ConcurrentDictionary<string * int, FSharpParseFileResults>(HashIdentity.Structural)
        // type check cache, keyed on file name
        let checkCache = ConcurrentDictionary<string, (TcResult * TcErrors) * (TcState * ModuleNamesDict)>(HashIdentity.Structural)
        // graph type check cache, keyed on file name
        let graphCheckCache = ConcurrentDictionary<string, GraphCheckEntry>(HashIdentity.Structural)

        return {
            tcConfig = tcConfig
            tcGlobals = tcGlobals
            tcImports = tcImports
            tcInitialState = tcInitialState
            projectOptions = projectOptions
            parseCache = parseCache
            checkCache = checkCache
            graphCheckCache = graphCheckCache
        }
    }

    let MakeProjectResults (projectFileName: string, parseResults: FSharpParseFileResults[], tcState: TcState, errors: FSharpDiagnostic[],
                            topAttrsOpt: TopAttribs option, tcImplFilesOpt: CheckedImplFile list option, compilerState) =
        let assemblyRef = mkSimpleAssemblyRef "stdin"
        let access = tcState.TcEnvFromImpls.AccessRights
        let symbolUses = Choice2Of2 (async { return seq { } })
        let dependencyFiles = parseResults |> Seq.map (fun x -> x.DependencyFiles) |> Array.concat
        let getAssemblyData () = None
        let details = (compilerState.tcGlobals, compilerState.tcImports, tcState.Ccu, tcState.CcuSig, symbolUses, topAttrsOpt,
                        getAssemblyData, assemblyRef, access, tcImplFilesOpt, dependencyFiles, Some compilerState.projectOptions)
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

    /// Counts the compiler-generated names of a file from zero again, before checking it, so a file checked again in
    /// this process, as in watch mode, gets the names a fresh compilation gives instead of continuing from its last check.
    let ResetGeneratedNames (input: ParsedInput, compilerState) =
        compilerState.tcGlobals.CompilerGlobalState
        |> Option.iter (fun state -> state.ResetCompilerGeneratedNamesOfFile input.QualifiedName.Range.FileIndex)

    let TypeCheckOneInputEntry (parseResults: FSharpParseFileResults, tcSink: TcResultsSink, tcState: TcState, moduleNamesDict: ModuleNamesDict, compilerState) =
        let input = parseResults.ParseTree
        let diagnosticsOptions = compilerState.tcConfig.diagnosticsOptions
        let capturingLogger = CompilationDiagnosticLogger("TypeCheckFile", diagnosticsOptions)
        let diagnosticsLogger = GetDiagnosticsLoggerFilteringByScopedNowarn(diagnosticsOptions, capturingLogger)
        use _scope = new CompilationGlobalsScope (diagnosticsLogger, BuildPhase.TypeCheck)

        let checkForErrors () = parseResults.ParseHadErrors || diagnosticsLogger.ErrorCount > 0
        let prefixPathOpt = None

        let input, moduleNamesDict = input |> DeduplicateParsedInputModuleName moduleNamesDict
        ResetGeneratedNames (input, compilerState)
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

        let tcEnvAtEnd, _topAttrs, implFile, ccuSigForFile, ownSigForFile = tcResult
        let errors = Array.append parseResults.Diagnostics tcErrors

        let scope = TypeCheckInfo (compilerState.tcConfig, compilerState.tcGlobals, ccuSigForFile, ownSigForFile, tcState.Ccu, compilerState.tcImports, tcEnvAtEnd.AccessRights,
                                projectFileName, fileName, Some compilerState.projectOptions, sink.GetResolutions(), sink.GetSymbolUses(), tcEnvAtEnd.NameEnv,
                                loadClosure, implFile, sink.GetOpenDeclarations())
        FSharpCheckFileResults (fileName, errors, Some scope, parseResults.DependencyFiles, None, keepAssemblyContents)

    /// The last generation given to a graph check finisher; 0 is never given.
    let lastGraphCheckGeneration = ref 0

    /// Whether a changed file whose signature is the same keeps its dependents' results (FICKL_FCS_SIGNATURE_CUTOFF=0 turns it off).
    let signatureCutoff = Environment.GetEnvironmentVariable "FICKL_FCS_SIGNATURE_CUTOFF" <> "0"

    let ReportCheckedFile (tcState: TcState, tcResult: TcResult, compilerState, subscriber) =
        let _, _, implFile, _, _ = tcResult
        match subscriber, implFile with
        | Some subscriber, Some implFile ->
            let cenv = SymbolEnv(compilerState.tcGlobals, tcState.Ccu, Some tcState.CcuSig, compilerState.tcImports)
            FSharpImplementationFileContents(cenv, implFile) |> subscriber
        | _ -> ()

    /// Type checks the files in parallel where the file dependency graph allows. A file checked by an earlier call is
    /// reused while neither it nor anything it depends on has changed, so after an edit only the edited file and its
    /// dependents are checked again. Fills the check cache with the same per-file entries a sequential check would
    /// leave. The subscriber gets the files in project order, each as soon as it and all files before it are checked,
    /// because Fable expects every earlier file to be known, not only the file's dependencies.
    let TypeCheckInputsInParallel (parseResults: FSharpParseFileResults[], tcState: TcState, compilerState, subscriber) =
        let tcConfig = compilerState.tcConfig
        let diagnosticsOptions = tcConfig.diagnosticsOptions

        let inputsAndModuleNames, _ =
            (Map.empty, parseResults) ||> Array.mapFold (fun moduleNamesDict parseRes ->
                let input, moduleNamesDict = parseRes.ParseTree |> DeduplicateParsedInputModuleName moduleNamesDict
                (input, moduleNamesDict), moduleNamesDict)
        let inputs, moduleNamesDicts = Array.unzip inputsAndModuleNames
        let fileNames = parseResults |> Array.map (fun parseRes -> parseRes.FileName)

        let sourceFiles = inputs |> Array.mapi (fun idx input -> { Idx = idx; FileName = input.FileName; ParsedInput = input })
        let filePairs = FilePairMap(sourceFiles)
        let graph, _trie = DependencyResolution.mkGraph filePairs sourceFiles
        let dependencies = Array.init inputs.Length (fun idx -> graph[idx] |> Array.filter ((<>) idx) |> Array.map (fun dep -> fileNames[dep]))

        // Each file's outcome is decided when the graph reaches it, after the files it depends on: dependencies always
        // come earlier in the project. Entities are compared by identity, so a file's earlier result stays valid only
        // while the finishers of everything it depends on are the ones it was checked with, also across checks of
        // part of the project.
        let outcomes = Array.zeroCreate<GraphCheckOutcome> inputs.Length
        let generations = Array.zeroCreate<int> inputs.Length
        let fileIndexes = Collections.Generic.Dictionary<string, int>()
        fileNames |> Array.iteri (fun idx fileName -> fileIndexes[fileName] <- idx)

        // A file this check reaches later is not settled yet, and gets 0, which no finisher has.
        let currentGeneration fileName =
            match fileIndexes.TryGetValue fileName with
            | true, idx -> generations[idx]
            | _ ->
                match compilerState.graphCheckCache.TryGetValue fileName with
                | true, entry -> entry.generation
                | _ -> -1

        let capturingLoggers = parseResults |> Array.map (fun _ -> CompilationDiagnosticLogger("TypeCheckFile", diagnosticsOptions))
        let loggers = capturingLoggers |> Array.map (fun logger -> GetDiagnosticsLoggerFilteringByScopedNowarn(diagnosticsOptions, logger))

        let checkFile idx tcState =
            let settle outcome generation =
                outcomes[idx] <- outcome
                generations[idx] <- generation
            let earlier =
                match compilerState.graphCheckCache.TryGetValue fileNames[idx] with
                | true, entry when
                    entry.qualifiedName = inputs[idx].QualifiedName.Text
                    && entry.fileIndex = idx
                    && entry.dependencyGenerations |> Array.forall (fun (dep, generation) -> currentGeneration dep = generation)
                    && dependencies[idx] |> Array.forall (fun dep -> entry.dependencyGenerations |> Array.exists (fst >> (=) dep)) -> Some entry
                | _ -> None
            match earlier with
            | Some entry when obj.ReferenceEquals(entry.parseResults, parseResults[idx]) ->
                settle (Reused entry) entry.generation
                entry.finisher
            | _ ->
            let parseRes = parseResults[idx]
            let logger = loggers[idx]
            use _scope = new CompilationGlobalsScope (logger, BuildPhase.TypeCheck)
            let checkForErrors () = parseRes.ParseHadErrors || logger.ErrorCount > 0
            let prefixPathOpt = None
            ResetGeneratedNames (inputs[idx], compilerState)
            let finisher =
                CheckOneInputWithCallback (NodeToTypeCheck.PhysicalFile idx)
                    (checkForErrors, tcConfig, compilerState.tcImports, compilerState.tcGlobals, prefixPathOpt, TcResultsSink.NoSink, tcState, inputs[idx], false)
                |> Cancellable.runWithoutCancellation
            let kept =
                match earlier with
                | Some entry when signatureCutoff ->
                    // The graph applies a finisher once for every file that depends on it, so applying it once more to
                    // read the signature changes nothing. Its diagnostics are already in the file's logger.
                    let (Finisher (finisher = finish)) = finisher
                    let partialResult, _ =
                        use _ = new CompilationGlobalsScope (DiscardErrorsLogger, BuildPhase.TypeCheck)
                        finish tcState
                    match partialResult with
                    | _, topAttrs, Some implFile, _, _ ->
                        let signature = SignatureFingerprint.compute implFile.Signature topAttrs
                        if signature.IsSome && signature = entry.signature.Force() then Some (entry, implFile) else None
                    | _ -> None
                | _ -> None
            match kept with
            | Some (entry, implFile) ->
                settle (Kept (entry, implFile)) entry.generation
                entry.finisher
            | None ->
                let dependencyGenerations = dependencies[idx] |> Array.map (fun dep -> dep, currentGeneration dep)
                settle (Replaced (finisher, dependencyGenerations)) (Interlocked.Increment &lastGraphCheckGeneration.contents)
                finisher

        // The implementation to report for a file: a kept or reused file's finisher gives an earlier one.
        let withLatestImplFile idx ((tcEnv, topAttrs, implFile, ccuSig, ownSig): TcResult) : TcResult =
            let implFile =
                match outcomes[idx] with
                | Reused entry -> entry.implFile
                | Kept (_, implFile) -> Some implFile
                | Replaced _ -> implFile
            tcEnv, topAttrs, implFile, ccuSig, ownSig

        let checkedFiles = Array.zeroCreate<(TcResult * TcState) option> parseResults.Length
        let nextToReport = ref 0
        let onChecked idx tcResult tcState =
            lock checkedFiles (fun () ->
                checkedFiles[idx] <- Some (withLatestImplFile idx tcResult, tcState)
                while nextToReport.Value < checkedFiles.Length && checkedFiles[nextToReport.Value].IsSome do
                    let tcResult, tcState = checkedFiles[nextToReport.Value].Value
                    ReportCheckedFile (tcState, tcResult, compilerState, subscriber)
                    nextToReport.Value <- nextToReport.Value + 1)

        let fileResults =
            use _ = UseBuildPhase BuildPhase.TypeCheck
            CheckMultipleInputsUsingGraphModeWithStates (compilerState.tcImports, compilerState.tcGlobals, None, tcState, inputs,
                graph, filePairs, checkFile, onChecked, (fun idx -> loggers[idx]), CancellationToken.None)

        let flatErrors = tcConfig.flatErrors
        let results =
            fileResults |> Array.mapi (fun idx (tcResult, tcState) ->
                let fileName = fileNames[idx]
                let tcResult = withLatestImplFile idx tcResult
                let newErrors () =
                    let diagnostics = capturingLoggers[idx].GetDiagnostics()
                    DiagnosticHelpers.CreateDiagnostics (diagnosticsOptions, false, fileName, diagnostics, suggestNamesForErrors, flatErrors, None)
                let entry =
                    match outcomes[idx] with
                    | Reused entry -> entry
                    | Kept (entry, implFile) ->
                        // The kept finisher was checked against the earlier dependencies, which include the current ones.
                        { entry with parseResults = parseResults[idx]; implFile = Some implFile; tcErrors = newErrors () }
                    | Replaced (finisher, dependencyGenerations) ->
                        let _, topAttrs, implFile, _, _ = tcResult
                        { parseResults = parseResults[idx]; qualifiedName = inputs[idx].QualifiedName.Text; fileIndex = idx
                          generation = generations[idx]; dependencyGenerations = dependencyGenerations
                          finisher = finisher; implFile = implFile
                          signature = lazy (implFile |> Option.bind (fun implFile -> SignatureFingerprint.compute implFile.Signature topAttrs))
                          tcErrors = newErrors () }
                compilerState.graphCheckCache[fileName] <- entry
                compilerState.checkCache[fileName] <- ((tcResult, entry.tcErrors), (tcState, moduleNamesDicts[idx]))
                tcResult, entry.tcErrors)

        if not (isNull (Environment.GetEnvironmentVariable "FICKL_FCS_GRAPH_LOG")) then
            let count f = outcomes |> Array.filter f |> Array.length
            eprintfn "Graph check: %d reused, %d kept, %d replaced"
                (count (function Reused _ -> true | _ -> false))
                (count (function Kept _ -> true | _ -> false))
                (count (function Replaced _ -> true | _ -> false))

        let lastState = fileResults |> Array.last |> snd
        results, (lastState, Array.last moduleNamesDicts)

    let TypeCheckClosedInputSet (parseResults: FSharpParseFileResults[], tcState, compilerState, subscriber) =
        let cachedTypeCheck (tcState, moduleNamesDict) (parseRes: FSharpParseFileResults) =
            let checkCacheKey = parseRes.FileName

            let typeCheckOneInput _fileName =
                TypeCheckOneInputEntry (parseRes, TcResultsSink.NoSink, tcState, moduleNamesDict, compilerState)

            let (result, errors), (tcState, moduleNamesDict) = compilerState.checkCache.GetOrAdd(checkCacheKey, typeCheckOneInput)
            ReportCheckedFile (tcState, result, compilerState, subscriber)
            (result, errors), (tcState, moduleNamesDict)

        // Several files go through the dependency graph in parallel, reusing unaffected results from earlier checks.
        let checkInParallel =
            parseResults.Length > 1
            && compilerState.tcConfig.typeCheckingConfig.Mode = TypeCheckingMode.Graph
            && not compilerState.tcConfig.compilingFSharpCore

        let results, (tcState, moduleNamesDict) =
            if checkInParallel then
                TypeCheckInputsInParallel (parseResults, tcState, compilerState, subscriber)
            else
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

    /// Treats the anonymous record types of the assemblies `isUnified` accepts as one, as if compiled together, for
    /// every checker in the process: for sources checked as assemblies of their own that a compile of the project
    /// would check in its assembly.
    static member SetAnonRecdTypesUnifiedAssembly(isUnified: string -> bool) =
        FSharp.Compiler.TypedTreeBasics.anonRecdTypesUnifiedAssembly <- isUnified

    /// Clears parse and typecheck caches.
    member _.ClearCache () = async {
        let! compilerState = compilerStateCache.Get()
        compilerState.parseCache.Clear()
        compilerState.checkCache.Clear()
        compilerState.graphCheckCache.Clear()
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
        let exnOpt =
            CompileHelpers.tryCompile diagnosticsLogger (fun exiter ->
                CompileFromTypedAst (ctok, compilerState.tcGlobals, compilerState.tcImports, tcState.Ccu,
                    tcImplFiles, topAttrs, compilerState.tcConfig, outFile, diagnosticsLogger, exiter))

        return errors.ToArray(), exnOpt
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
        let _tcEnvAtEndFile, topAttrsFile, implFile, _ccuSigForFile, _ownSigForFile = tcResult

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
