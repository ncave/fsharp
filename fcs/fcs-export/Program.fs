open System.IO
open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
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
    let file = "fcs-export.fsproj"
    let projDir = __SOURCE_DIRECTORY__
    let projFile = Path.Combine(projDir, file)
    let (args, _, _, _) = getProjectOptionsFromProjectFile true projFile
    args
    |> Array.filter (fun s -> s.StartsWith("-r:"))

let mkProjectCommandLineArgsForScript (dllName, fileNames) = 
    [|  yield "--simpleresolution" 
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
            yield r
     |]

let checker = FSharpChecker.Create()

let parseAndCheckScript (file, input) =
    let dllName = Path.ChangeExtension(file, ".dll")
    let projName = Path.ChangeExtension(file, ".fsproj")
    let args = mkProjectCommandLineArgsForScript (dllName, [file])
    printfn "file: %s" file
    args |> Array.iter (printfn "args: %s")
    let projectOptions = checker.GetProjectOptionsFromCommandLineArgs (projName, args)
    let parseRes, typedRes = checker.ParseAndCheckFileInProject(file, 0, input, projectOptions) |> Async.RunSynchronously

    if parseRes.Diagnostics.Length > 0 then
        printfn "---> Parse Input = %A" input
        printfn "---> Parse Error = %A" parseRes.Diagnostics

    match typedRes with
    | FSharpCheckFileAnswer.Succeeded(res) -> parseRes, res
    | res -> failwithf "Parsing did not finish... (%A)" res

[<EntryPoint>]
let main argv = 
    ignore argv
    printfn "Exporting metadata..."
    let file = "/temp/test.fsx"
    let input = "let a = 42"
    let sourceText = FSharp.Compiler.Text.SourceText.ofString input
    // parse script just to export metadata
    let parseRes, typedRes = parseAndCheckScript(file, sourceText)
    printfn "Exporting is done. Binaries can be found in ./temp/metadata/"
    0
