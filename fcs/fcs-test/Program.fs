open System.IO
open FSharp.Compiler
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.SourceCodeServices
open FSharp.Compiler.EditorServices

let getProjectOptions (folder: string) (projectFile: string) =
    let runProcess (workingDir: string) (exePath: string) (args: string) =
        let psi = System.Diagnostics.ProcessStartInfo()
        psi.FileName <- exePath
        psi.WorkingDirectory <- workingDir
        psi.RedirectStandardOutput <- false
        psi.RedirectStandardError <- false
        psi.Arguments <- args
        psi.CreateNoWindow <- true
        psi.UseShellExecute <- false

        use p = new System.Diagnostics.Process()
        p.StartInfo <- psi
        p.Start() |> ignore
        p.WaitForExit()

        let exitCode = p.ExitCode
        exitCode, ()

    let runCmd exePath args = runProcess folder exePath (args |> String.concat " ")
    let msbuildExec = Dotnet.ProjInfo.Inspect.dotnetMsbuild runCmd
    let result = Dotnet.ProjInfo.Inspect.getProjectInfo ignore msbuildExec Dotnet.ProjInfo.Inspect.getFscArgs projectFile
    match result with
    | Ok (Dotnet.ProjInfo.Inspect.GetResult.FscArgs x) -> x
    | _ -> []

let mkStandardProjectReferences () = 
    let projFile = "fcs-test.fsproj"
    let projDir = __SOURCE_DIRECTORY__
    getProjectOptions projDir projFile
    |> List.filter (fun s -> s.StartsWith("-r:"))
    |> List.map (fun s -> s.Replace("-r:", ""))

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
            yield "-r:" + r
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
