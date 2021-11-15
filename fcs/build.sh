#!/usr/bin/env bash

dotnet build -c Release src/buildtools/buildtools.proj
dotnet build -c Release src/fsharp/FSharp.Compiler.Service
#dotnet /usr/share/dotnet/sdk/5.0.402/MSBuild.dll /p:Configuration=Release /p:FscToolExe=fsc src/fsharp/FSharp.Compiler.Service/
