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
open Interpreter
open Examples
//open Tests
//open Buddy

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
          match res with
            | Err s -> printf "%s\n" s
            | Val (_, circ) -> printf "Circuit:\n%s\n" (String.concat "\n" (prettyPrintCircuit circ));
                               //printf "Bits used: %d\n" (Set.count (getUses circ));
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
                               //printf "Bits used: %d\n" (Set.count (getUses circ));
                               printf "Gates: %d\n" (List.length circ);
                               printf "Toffolis: %d\n" (List.length (List.filter (fun x -> match x with RTOFF _ -> true | _ -> false) circ))


[<EntryPoint>]
let __main _ = 
  printf "Carry-Ripple 2:\n"
  ignore <| runBool (carryRippleAdder 2) Pebbled
  printf "\nCarry-Ripple 4:\n"
  ignore <| runBool (carryRippleAdder 4) Pebbled
  printf "Carry-Ripple 8:\n"
  ignore <| runBool (carryRippleAdder 8) Pebbled
  printf "\nMult 2:\n"
  ignore <| runBool (mult22 2) Pebbled
  printf "\nModular adder 2:\n"
  ignore <| runBool (addMod2 2) Pebbled
  printf "\nModular adder 4:\n"
  ignore <| runBool (addMod 4) Pebbled
  printf "\nCucarro adder 2:\n"
  ignore <| runBool (cucarro2 2) Pebbled
  printf "\nCucarro adder 4:\n"
  ignore <| runBool (cucarro 4) Pebbled
  printf "\nCucarro adder 8:\n"
  ignore <| runBool (cucarro 8) Pebbled
  printf "\nma4:\n"
  ignore <| runBool (ma4) Pebbled
  0
