module ReVerC

open System.IO
open System
open Util
open Circuit
open AncillaHeap
open GenOp
open ExprTypes
open TypeCheck
open Interpreter
open Equiv

// Master methods

type compileMode =
  | Basic
  | Eager
  | Crush

type outputType =
  | DotQC
  | QSharp

let typeCheck top gexp = 
  let (top', eqs, bnds, typ) = inferTypes top [] gexp
  let eqs =
    let f c = match c with
      | TCons (x, y) -> not (x = y)
      | ICons (x, y) -> not (x = y)
    List.filter f eqs
  match unify_eq top' eqs bnds [] with
    | None      -> None
    | Some subs -> Some (applySubs subs gexp)

let verify gexp = ignore <| compileBDD (gexp, bddInit)

let printStats circ = 
  let isToff = function
    | RTOFF _ -> true
    | _       -> false
  printf "Bits used: %d\n" (Set.count (uses circ))
  printf "Gates: %d\n" (List.length circ)
  printf "Toffolis: %d\n" (List.length (List.filter isToff circ))

type compile (quote, ?verif0, ?mode0, ?otype0, ?ofile0) =
  // Defaults
  let verif = defaultArg verif0 false
  let mode  = defaultArg mode0  Eager
  let otype = defaultArg otype0 QSharp
  let ofile = match otype with
    | DotQC  -> defaultArg ofile0 "output.qc"
    | QSharp -> defaultArg ofile0 "output.qs"
  // Parsing
  let (top, gexp) = parseAST quote
  // Type inference
  do match typeCheck top gexp with
    | None -> printf "Error: could not infer types\n"
    | Some gexp' ->
        // Verification
        if verif then verify gexp'
        // Compilation
        let res = match mode with 
          | Basic -> Compiler.compileCirc (gexp', Compiler.circInit)
          | Eager -> GC.compileGCCirc (gexp', GC.circGCInit)
          | Crush -> Crush.compile (gexp', Crush.bexpInit) Crush.Pebbled
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, circ) ->
              let src = match otype with
                | DotQC -> printQCV circ (Set.toList (uses circ))
                | QSharp -> printQSharp circ
              File.WriteAllText(ofile, src)
