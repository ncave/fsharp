module Lib

type HTMLAttr =
    | Href of string
    | Custom

let a = Custom
let b = a.IsCustom
printfn $"IsCustom = {b}"