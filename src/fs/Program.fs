// Revs -- Reversible circuit synthesis from higher-level F# code
// ==============================================================
// 
// Forked from the RevLang library written by A. Parent (MSR, 2014)

open System.IO
open System
open Util
open Circuit
open AncillaHeap
open GenOp
open ExprTypes
open TypeCheck
open Interpreter
open Examples
open Equiv

let runDirect program cleanupStrategy = 
    let (top, gexp) = parseAST program
    printf "gExp:\n%s\n" (show gexp);
    let (top', eqs, bnds, typ) = inferTypes top [] gexp
    let eqs =
      let f c = match c with
        | TCons (x, y) -> not (x = y)
        | ICons (x, y) -> not (x = y)
      List.filter f eqs
//    printf "gExp:\n%s\n" (show gexp);
//    printf "Equality constraints:\n%A\n" eqs;
//    printf "Ordered constraints:\n%A\n" bnds;
    let res = unify_eq top'  eqs bnds []
    match res with
      | None -> printf "Error: could not infer types\n"
      | Some subs -> 
          let gexp' = applySubs subs gexp
          printf "Annotated gExp:\n%s\n" (show gexp');
          let res = compileCirc (gexp', circInit)
          let ver = compileBDD (gexp', bddInit)
          match res with
            | Err s -> printf "%s\n" s
            | Val (_, circ) -> printf "Circuit:\n%s\n" (String.concat "\n" (prettyPrintCircuit circ));
                               printf "Bits used: %d\n" (Set.count (uses circ));
                               printf "Gates: %d\n" (List.length circ);
                               printf "Toffolis: %d\n" (List.length (List.filter (fun x -> match x with RTOFF _ -> true | _ -> false) circ))

let runBool program cleanupStrategy = 
    let (top, gexp) = parseAST program
    let (top', eqs, bnds, typ) = inferTypes top [] gexp
    let eqs =
      let f c = match c with
        | TCons (x, y) -> not (x = y)
        | ICons (x, y) -> not (x = y)
      List.filter f eqs
    let res = unify_eq top'  eqs bnds []
//    printf "gExp:\n%s\n" (show gexp);
//    printf "Equality constraints:\n%A\n" eqs;
//    printf "Ordered constraints:\n%A\n" bnds;
    match res with
      | None -> printf "Error: could not infer types\n"
      | Some subs -> 
          let gexp' = applySubs subs gexp
          printf "Annotated gExp:\n%s\n" (show gexp');
          let res = compile (gexp', bexpInit) cleanupStrategy
          match res with
            | Err s -> printf "%s\n" s
            | Val (_, circ) -> printf "Circuit:\n%s\n" (String.concat "\n" (prettyPrintCircuit circ))
                               printf "Bits used: %d\n" (Set.count (uses circ));
                               printf "Gates: %d\n" (List.length circ);
                               printf "Toffolis: %d\n" (List.length (List.filter (fun x -> match x with RTOFF _ -> true | _ -> false) circ))


[<EntryPoint>]
let __main _ = 
  printf "Carry-Ripple 8:\n"
  ignore <| runDirect (carryRippleAdder 8) Pebbled
  Console.Out.Flush()
  (*
  printf "\nSHA (2 rounds):\n"
  ignore <| runDirect (exprSha 2) Pebbled
  Console.Out.Flush()
  printf "Carry-Ripple 32:\n"
  ignore <| runDirect (carryRippleAdder 32) Pebbled
  Console.Out.Flush()
  printf "\nCarry-Ripple 64:\n"
  //ignore <| runDirect (carryRippleAdder 64) Pebbled
  Console.Out.Flush()
  printf "\nMult 32:\n"
  //ignore <| runDirect (mult 32) Pebbled
  Console.Out.Flush()
  printf "\nMult 64:\n"
  //ignore <| runDirect (mult 64) Pebbled
  Console.Out.Flush()
  (*
  printf "\nCarry-Lookahead 32:\n"
  ignore <| runDirect (carryLookaheadAdder 32) Pebbled
  Console.Out.Flush()
  printf "\nCarry-Lookahead 64:\n"
  ignore <| runDirect (carryLookaheadAdder 64) Pebbled
  Console.Out.Flush()*)
  printf "\nModular adder 32:\n"
  ignore <| runDirect (addMod 32) Pebbled
  Console.Out.Flush()
  printf "\nModular adder 64:\n"
  ignore <| runDirect (addMod 64) Pebbled
  Console.Out.Flush()
  printf "\nCucarro adder 32:\n"
  ignore <| runDirect (cucarro 32) Pebbled
  Console.Out.Flush()
  printf "\nCucarro adder 64:\n"
  ignore <| runDirect (cucarro 64) Pebbled
  Console.Out.Flush()
  printf "\nma4:\n"
  ignore <| runDirect (ma4) Pebbled
  Console.Out.Flush()
  printf "\nSHA (2 rounds):\n"
  ignore <| runDirect (exprSha 2) Pebbled
  Console.Out.Flush()
  printf "\nMD5 (2 rounds):\n"
  ignore <| runDirect (exprMD5 2) Pebbled
  Console.Out.Flush()
  printf "\nSHA (4 rounds):\n"
  ignore <| runDirect (exprSha 4) Pebbled
  Console.Out.Flush()
  printf "\nSHA (8 rounds):\n"
  ignore <| runDirect (exprSha 8) Pebbled
  Console.Out.Flush()
  printf "\nSHA (16 rounds):\n"
  ignore <| runDirect (exprSha 16) Pebbled
  Console.Out.Flush()*)
  0
