#!/usr/bin/env bash

dotnet build -c Release buildtools/fslex
dotnet build -c Release buildtools/fsyacc
dotnet build -c Release src/Compiler
dotnet run -c Release --project fcs/fcs-export
