#!/usr/bin/env bash

dotnet build -c Release src/buildtools/buildtools.proj
dotnet build -c Release src/fsharp/FSharp.Compiler.Service
dotnet run -c Release --project fcs/fcs-export
