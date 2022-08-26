open System.IO
open System.Collections.Generic
open FSharp.Compiler.CodeAnalysis

let readRefs (folder: string) (projectFile: string) =
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
    | Ok(Dotnet.ProjInfo.Inspect.GetResult.FscArgs x) ->
        x
        |> List.filter (fun s -> s.StartsWith("-r:"))
        |> List.map (fun s -> s.Replace("-r:", ""))
    | _ -> []

let mkStandardProjectReferences () = 
    let projFile = "test.fsproj"
    let projDir = __SOURCE_DIRECTORY__ + "/test"
    readRefs projDir projFile

let mkProjectCommandLineArgsForScript (dllName, fileNames) = 
    [|
        yield "--simpleresolution" 
        yield "--noframework" 
        yield "--debug:full" 
        yield "--define:DEBUG" 
        yield "--targetprofile:netcore"
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

let checker = FSharpChecker.Create()

let parseAndCheckScript (file, input) =
    let dllName = Path.ChangeExtension(file, ".dll")
    let projName = Path.ChangeExtension(file, ".fsproj")
    let args = mkProjectCommandLineArgsForScript (dllName, [file])
    printfn "File: %s" file
    // args |> Array.iter (printfn "args: %s")
    let projectOptions = checker.GetProjectOptionsFromCommandLineArgs (projName, args)
    let parseRes, typedRes = checker.ParseAndCheckFileInProject(file, 0, input, projectOptions) |> Async.RunSynchronously

    if parseRes.Diagnostics.Length > 0 then
        printfn "---> Parse errors: %A" parseRes.Diagnostics

    let typedRes =
        match typedRes with
        | FSharpCheckFileAnswer.Succeeded(res) -> res
        | res -> failwithf "Type-check error: %A" res

    if typedRes.Diagnostics.Length > 0 then
        printfn "---> Type-check errors: %A" typedRes.Diagnostics

    parseRes, typedRes

[<EntryPoint>]
let main argv = 
    ignore argv
    printfn "FCS parsing and type-checking test ..."
    let file = __SOURCE_DIRECTORY__ + "/test/test.fs"
    let input = System.IO.File.ReadAllText(file)
    let sourceText = FSharp.Compiler.Text.SourceText.ofString input
    let parseRes, typedRes = parseAndCheckScript(file, sourceText)
    printfn "FCS parsing and type-checking is done."
    0
