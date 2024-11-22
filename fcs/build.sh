#!/usr/bin/env bash

# cd to root
cd $(dirname $0)/..

# build fslex/fsyacc tools
dotnet build -c Release buildtools/fslex
dotnet build -c Release buildtools/fsyacc

# build FSharp.Compiler.Service (to make sure it's not broken)
dotnet build -c Release src/Compiler

# build FCS-Fable codegen
cd fcs/fcs-fable/codegen
dotnet build -c Release
dotnet run -c Release -- ../../../src/Compiler/FSComp.txt FSComp.fs
dotnet run -c Release -- ../../../src/Compiler/Interactive/FSIstrings.txt FSIstrings.fs

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

# build FCS-Fable
cd ..
dotnet build -c Release

# run some tests
cd test
npm test
# npm run bench
