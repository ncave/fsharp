open System.IO
open System.Collections.Generic
open FSharp.Compiler.CodeAnalysis
open Buildalyzer

let getProjectOptionsFromProjectFile (projFile: string) =

    let compileFilesToAbsolutePath projDir (f: string) =
        if f.EndsWith(".fs") || f.EndsWith(".fsi") then
            if Path.IsPathRooted f then f else Path.Combine(projDir, f)
        else
            f

    let manager =
        let log = new System.IO.StringWriter()
        let options = AnalyzerManagerOptions(LogWriter = log)
        let m = AnalyzerManager(options)
        m

    let tryGetResult (getCompilerArgs: IAnalyzerResult -> string[]) (projFile: string) =
        let analyzer = manager.GetProject(projFile)
        let env = analyzer.EnvironmentFactory.GetBuildEnvironment(Environment.EnvironmentOptions(DesignTime=true,Restore=false))
        // If the project targets multiple frameworks, multiple results will be returned
        // For now we just take the first one with non-empty command
        let results = analyzer.Build(env)
        results
        |> Seq.tryFind (fun r -> System.String.IsNullOrEmpty(r.Command) |> not)
        |> Option.map (fun result -> {|
                CompilerArguments = getCompilerArgs result
                ProjectReferences = result.ProjectReferences
                Properties = result.Properties |})

    // Because Buildalyzer works better with .csproj, we first "dress up" the project as if it were a C# one
    // and try to adapt the results. If it doesn't work, we try again to analyze the .fsproj directly
    let csprojResult =
        let csprojFile = projFile.Replace(".fsproj", ".csproj")
        if System.IO.File.Exists(csprojFile) then
            None
        else
            try
                System.IO.File.Copy(projFile, csprojFile)
                csprojFile
                |> tryGetResult (fun r ->
                    // Careful, options for .csproj start with / but so do root paths in unix
                    let reg = System.Text.RegularExpressions.Regex(@"^\/[^\/]+?(:?:|$)")
                    let comArgs =
                        r.CompilerArguments
                        |> Array.map (fun line ->
                            if reg.IsMatch(line) then
                                if line.StartsWith("/reference") then "-r" + line.Substring(10)
                                else "--" + line.Substring(1)
                            else line)
                    match r.Properties.TryGetValue("OtherFlags") with
                    | false, _ -> comArgs
                    | true, otherFlags ->
                        let otherFlags = otherFlags.Split(' ', System.StringSplitOptions.RemoveEmptyEntries)
                        Array.append otherFlags comArgs
                )
            finally
                System.IO.File.Delete(csprojFile)

    let result =
        csprojResult
        |> Option.orElseWith (fun () -> projFile |> tryGetResult (fun r ->
            // result.CompilerArguments doesn't seem to work well in Linux
            System.Text.RegularExpressions.Regex.Split(r.Command, @"\r?\n")))
        |> function
            | Some result -> result
            // TODO: Get Buildalyzer errors from the log
            | None -> failwith $"Cannot parse {projFile}"
    let projDir = System.IO.Path.GetDirectoryName(projFile)
    let projOpts =
        result.CompilerArguments
        |> Array.skipWhile (fun line -> not(line.StartsWith("-")))
        |> Array.map (compileFilesToAbsolutePath projDir)
    projOpts, Seq.toArray result.ProjectReferences, result.Properties

let mkStandardProjectReferences () = 
    let file = "fcs-export.fsproj"
    let projDir = __SOURCE_DIRECTORY__
    let projFile = Path.Combine(projDir, file)
    let (args, _, _) = getProjectOptionsFromProjectFile projFile
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
