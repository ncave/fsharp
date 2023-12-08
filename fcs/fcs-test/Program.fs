open System.IO
open System.Text.RegularExpressions
open FSharp.Compiler
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.SourceCodeServices
open FSharp.Compiler.EditorServices
open Buildalyzer

let getProjectOptionsFromProjectFile (isMain: bool) (projFile: string) =

    let tryGetResult (isMain: bool) (manager: AnalyzerManager) (maybeCsprojFile: string) =

        let analyzer = manager.GetProject(maybeCsprojFile)
        let env = analyzer.EnvironmentFactory.GetBuildEnvironment(Environment.EnvironmentOptions(DesignTime=true,Restore=false))
        // If System.the project targets multiple frameworks, multiple results will be returned
        // For now we just take the first one with non-empty command
        let results = analyzer.Build(env)
        results
        |> Seq.tryFind (fun r -> System.String.IsNullOrEmpty(r.Command) |> not)

    let manager =
        let log = new StringWriter()
        let options = AnalyzerManagerOptions(LogWriter = log)
        let m = AnalyzerManager(options)
        m

    // Because Buildalyzer works better with .csproj, we first "dress up" the project as if it were a C# one
    // and try to adapt the results. If it doesn't work, we try again to analyze the .fsproj directly
    let csprojResult =
        let csprojFile = projFile.Replace(".fsproj", ".csproj")
        if File.Exists(csprojFile) then
            None
        else
            try
                File.Copy(projFile, csprojFile)
                tryGetResult isMain manager csprojFile
                |> Option.map (fun (r: IAnalyzerResult) ->
                    // Careful, options for .csproj start with / but so do root paths in unix
                    let reg = Regex(@"^\/[^\/]+?(:?:|$)")
                    let comArgs =
                        r.CompilerArguments
                        |> Array.map (fun line ->
                            if reg.IsMatch(line) then
                                if line.StartsWith("/reference") then "-r" + line.Substring(10)
                                else "--" + line.Substring(1)
                            else line)
                    let comArgs =
                        match r.Properties.TryGetValue("OtherFlags") with
                        | false, _ -> comArgs
                        | true, otherFlags ->
                            let otherFlags = otherFlags.Split(' ', System.StringSplitOptions.RemoveEmptyEntries)
                            Array.append otherFlags comArgs
                    comArgs, r)
            finally
                File.Delete(csprojFile)

    let compilerArgs, result =
        csprojResult
        |> Option.orElseWith (fun () ->
            tryGetResult isMain manager projFile
            |> Option.map (fun r ->
                // result.CompilerArguments doesn't seem to work well in Linux
                let comArgs = Regex.Split(r.Command, @"\r?\n")
                comArgs, r))
        |> function
            | Some result -> result
            // TODO: Get Buildalyzer errors from the log
            | None -> failwith $"Cannot parse {projFile}"

    let projDir = Path.GetDirectoryName(projFile)
    let projOpts =
        compilerArgs
        |> Array.skipWhile (fun line -> not(line.StartsWith("-")))
        |> Array.map (fun f ->
            if f.EndsWith(".fs") || f.EndsWith(".fsi") then
                if Path.IsPathRooted f then f else Path.Combine(projDir, f)
            else f)
    projOpts,
    Seq.toArray result.ProjectReferences,
    result.Properties,
    result.TargetFramework

let mkStandardProjectReferences () = 
    let fileName = "fcs-test.fsproj"
    let projDir = __SOURCE_DIRECTORY__
    let projFile = Path.Combine(projDir, fileName)
    let (args, _, _, _) = getProjectOptionsFromProjectFile true projFile
    args
    |> Array.filter (fun s -> s.StartsWith("-r:"))

let mkProjectCommandLineArgsForScript (dllName, fileNames) = 
    [|  yield "--simpleresolution" 
        yield "--noframework" 
        yield "--debug:full" 
        yield "--define:DEBUG" 
        yield "--optimize-" 
        yield "--out:" + dllName
        yield "--doc:test.xml" 
        yield "--warn:3" 
        yield "--fullpaths" 
        yield "--flaterrors" 
        yield "--target:library" 
        for x in fileNames do 
            yield x
        let references = mkStandardProjectReferences ()
        for r in references do
            yield r
     |]

let getProjectOptionsFromCommandLineArgs(projName, argv): FSharpProjectOptions = 
      { ProjectFileName = projName
        ProjectId = None
        SourceFiles = [| |]
        OtherOptions = argv
        ReferencedProjects = [| |]  
        IsIncompleteTypeCheckEnvironment = false
        UseScriptResolutionRules = false
        LoadTime = System.DateTime.MaxValue
        UnresolvedReferences = None
        OriginalLoadReferences = []
        Stamp = None }

let printAst title (projectResults: FSharpCheckProjectResults) =
    let implFiles = projectResults.AssemblyContents.ImplementationFiles
    let decls = implFiles
                |> Seq.collect (fun file -> AstPrint.printFSharpDecls "" file.Declarations)
                |> String.concat "\n"
    printfn "%s Typed AST:" title
    decls |> printfn "%s"

[<EntryPoint>]
let main argv = 
    let projName = "Project.fsproj"
    let fileName = __SOURCE_DIRECTORY__ + "/test_script.fsx"
    let fileNames = [| fileName |]
    let source = File.ReadAllText (fileName, System.Text.Encoding.UTF8)

    let dllName = Path.ChangeExtension(fileName, ".dll")
    let args = mkProjectCommandLineArgsForScript (dllName, fileNames)
    // for arg in args do printfn "%s" arg

    let projectOptions = getProjectOptionsFromCommandLineArgs (projName, args)
    let checker = InteractiveChecker.Create(projectOptions)
    let sourceReader _fileName = (hash source, lazy source)

    // parse and typecheck a project
    let projectResults =
        checker.ParseAndCheckProject(projName, fileNames, sourceReader)
        |> Async.RunSynchronously
    projectResults.Diagnostics |> Array.iter (fun e -> printfn "%A: %A" (e.Severity) e)
    printAst "ParseAndCheckProject" projectResults

    // or just parse and typecheck a file in project
    let (parseResults, typeCheckResults, projectResults) =
        checker.ParseAndCheckFileInProject(projName, fileNames, sourceReader, fileName)
        |> Async.RunSynchronously
    projectResults.Diagnostics |> Array.iter (fun e -> printfn "%A: %A" (e.Severity) e)

    printAst "ParseAndCheckFileInProject" projectResults

    let inputLines = source.Split('\n')

    // Get tool tip at the specified location
    let tip = typeCheckResults.GetToolTip(4, 7, inputLines.[3], ["foo"], Tokenization.FSharpTokenTag.IDENT)
    (sprintf "%A" tip).Replace("\n","") |> printfn "\n---> ToolTip Text = %A" // should print "FSharpToolTipText [...]"

    // Get declarations (autocomplete) for msg
    let partialName = { QualifyingIdents = []; PartialIdent = "msg"; EndColumn = 17; LastDotPos = None }
    let decls = typeCheckResults.GetDeclarationListInfo(Some parseResults, 6, inputLines.[5], partialName, (fun _ -> []))
    [ for item in decls.Items -> item.NameInList ] |> printfn "\n---> msg AutoComplete = %A" // should print string methods

    // Get declarations (autocomplete) for canvas
    let partialName = { QualifyingIdents = []; PartialIdent = "canvas"; EndColumn = 10; LastDotPos = None }
    let decls = typeCheckResults.GetDeclarationListInfo(Some parseResults, 8, inputLines.[7], partialName, (fun _ -> []))
    [ for item in decls.Items -> item.NameInList ] |> printfn "\n---> canvas AutoComplete = %A"

    printfn "Done."
    0
