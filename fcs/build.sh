#!/usr/bin/env bash

# cd to root
cd $(dirname $0)/..

# build fslex/fsyacc tools
dotnet build -c Release src/buildtools/buildtools.proj
# dotnet build -c Release src/fsharp/FSharp.Compiler.Service

# FCS-Fable codegen
cd fcs/fcs-fable/codegen
dotnet build -c Release
dotnet run -c Release -- ../../../src/fsharp/FSComp.txt FSComp.fs
dotnet run -c Release -- ../../../src/fsharp/fsi/FSIstrings.txt FSIstrings.fs

# cleanup comments
files="FSComp.fs FSIstrings.fs"
for file in $files; do
  echo "Delete comments in $file"
  sed -i '1s/^\xEF\xBB\xBF//' $file # remove BOM
  sed -i '/^ *\/\//d' $file # delete all comment lines
done

# replace all #line directives with comments
files="lex.fs pplex.fs illex.fs ilpars.fs pars.fs pppars.fs"
for file in $files; do
  echo "Replace #line directives with comments in $file"
  sed -i 's/^# [0-9]/\/\/\0/' $file # comment all #line directives
  sed -i 's/^\(\/\/# [0-9]\{1,\} "\).*\/codegen\/\(\.\.\/\)*/\1/' $file # cleanup #line paths
done

# FCS-Fable build
cd ..
dotnet build -c Release

# some tests
# cd test
# npm run test-dotnet
# npm run bench-dotnet
