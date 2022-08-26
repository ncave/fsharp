#!/usr/bin/env bash

dotnet build -c Release buildtools
dotnet build -c Release src/Compiler
dotnet restore fcs/fcs-test/test
dotnet run -c Release --project fcs/fcs-test
