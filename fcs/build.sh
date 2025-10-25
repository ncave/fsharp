#!/usr/bin/env bash

dotnet build -c Release buildtools
dotnet build -c Release src/Compiler
dotnet run -c Release --project fcs/fcs-test
echo "Binaries can be found here: /artifacts/bin/FSharp.Compiler.Service/Release/netstandard2.0/"