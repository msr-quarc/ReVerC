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
open Cmd

type mode = 
  | Default
  | SpaceSave

let info = true
let ver = false

let isToff = function
  | RTOFF _ -> true
  | _       -> false

let typecheck (top, gexp) = 
  // Type inference
  let (top', eqs, bnds, typ) = inferTypes top [] gexp
  let eqs =
    let f c = match c with
      | TCons (x, y) -> not (x = y)
      | ICons (x, y) -> not (x = y)
    List.filter f eqs
  let res = unify_eq top' eqs bnds []
  match res with
    | None -> printf "Error: could not infer types\n"
              printf "Equality constraints:\n%A\n" eqs
              printf "Ordered constraints:\n%A\n" bnds
    | Some subs -> 
        let gexp' = applySubs subs gexp
        printf "Type inference succeeded, annotated program:\n%s\n" (show gexp')
registerCmd "tc" "Type check the program" typecheck

let verify (top, gexp) = 
  // Type inference
  let (top', eqs, bnds, typ) = inferTypes top [] gexp
  let eqs =
    let f c = match c with
      | TCons (x, y) -> not (x = y)
      | ICons (x, y) -> not (x = y)
    List.filter f eqs
  let res = unify_eq top' eqs bnds []
  match res with
    | None -> printf "Error: could not infer types\n"
    | Some subs -> 
        let gexp' = applySubs subs gexp
        ignore <| compileBDD (gexp', bddInit)
registerCmd "verify" "Run the model checker to verify assertions and cleans" verify

let comp (top, gexp) = 
  // Type inference
  let (top', eqs, bnds, typ) = inferTypes top [] gexp
  let eqs =
    let f c = match c with
      | TCons (x, y) -> not (x = y)
      | ICons (x, y) -> not (x = y)
    List.filter f eqs
  let res = unify_eq top' eqs bnds []
  match res with
    | None -> printf "Error: could not infer types\n"
    | Some subs -> 
        let gexp' = applySubs subs gexp
        // Compilation
        let res = compileCirc (gexp', circInit)
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, circ) -> 
              printf "%s" (printQCV circ (Set.count (uses circ)))
registerCmd "compile" "Compile the program in default mode" comp

let crush (top, gexp) = 
  // Type inference
  let (top', eqs, bnds, typ) = inferTypes top [] gexp
  let eqs =
    let f c = match c with
      | TCons (x, y) -> not (x = y)
      | ICons (x, y) -> not (x = y)
    List.filter f eqs
  let res = unify_eq top' eqs bnds []
  match res with
    | None -> printf "Error: could not infer types\n"
    | Some subs -> 
        let gexp' = applySubs subs gexp
        // Compilation
        let res = compile (gexp', bexpInit) Pebbled
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, circ) -> 
              printf "%s" (printQCV circ (Set.count (uses circ)))
registerCmd "compile-crush" "Compile the program in space saving mode" crush

let compStats (top, gexp) = 
  // Type inference
  let (top', eqs, bnds, typ) = inferTypes top [] gexp
  let eqs =
    let f c = match c with
      | TCons (x, y) -> not (x = y)
      | ICons (x, y) -> not (x = y)
    List.filter f eqs
  let res = unify_eq top' eqs bnds []
  match res with
    | None -> printf "Error: could not infer types\n"
    | Some subs -> 
        let gexp' = applySubs subs gexp
        // Compilation
        let res = compileCirc (gexp', circInit)
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, circ) -> 
              printf "Bits used: %d\n" (Set.count (uses circ))
              printf "Gates: %d\n" (List.length circ)
              printf "Toffolis: %d\n" (List.length (List.filter isToff circ))
registerCmd "compile-stats" "Compile the program in default mode, printing just circuit statistics" compStats

let run program mode cleanupStrategy = 
  // Parsing
  let (top, gexp) = parseAST program
  if info then printf "gExp:\n%s\n" (show gexp)
  // Type inference
  let (top', eqs, bnds, typ) = inferTypes top [] gexp
  let eqs =
    let f c = match c with
      | TCons (x, y) -> not (x = y)
      | ICons (x, y) -> not (x = y)
    List.filter f eqs
  let res = unify_eq top' eqs bnds []
  match res with
    | None -> printf "Error: could not infer types\n"
              printf "Equality constraints:\n%A\n" eqs
              printf "Ordered constraints:\n%A\n" bnds
    | Some subs -> 
        let gexp' = applySubs subs gexp
        if info then printf "Annotated gExp:\n%s\n" (show gexp');
        // Verification
        if ver then ignore <| compileBDD (gexp', bddInit)
        // Compilation
        let res = match mode with 
          | Default   -> compileCirc (gexp', circInit)
          | SpaceSave -> compile     (gexp', bexpInit) cleanupStrategy
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, circ) -> 
              if info then 
                printf "Bits used: %d\n" (Set.count (uses circ))
                printf "Gates: %d\n" (List.length circ)
                printf "Toffolis: %d\n" (List.length (List.filter isToff circ))
              printf "%s" (printQCV circ (Set.count (uses circ)))

let runHack program mode cleanupStrategy = 
  // Parsing
  let (top, gexp) = parseAST program
  // Type inference
  let (top', eqs, bnds, typ) = inferTypes top [] gexp
  let eqs =
    let f c = match c with
      | TCons (x, y) -> not (x = y)
      | ICons (x, y) -> not (x = y)
    List.filter f eqs
  let res = unify_eq top' eqs bnds []
  match res with
    | None -> ()
    | Some subs -> 
        let gexp' = applySubs subs gexp
        // Compilation
        let res = match mode with 
          | Default   -> compileCirc (gexp', circInit)
          | SpaceSave -> compile     (gexp', bexpInit) cleanupStrategy
        ()


[<EntryPoint>]
let __main _ = 
  ignore <| runHack polyEx Default Pebbled
  let mutable exit = false
  let mutable line = ""
  while (not exit) do
    Console.WriteLine "Enter a command: "
    line <- Console.ReadLine()
    if line = "exit" then exit <- true
    else parseLine line

(*
  ignore <| run polyEx Default Pebbled
  printHelp ()
  printf "Carry-Ripple 32:\n"
  ignore <| run (carryRippleAdder 32) Default Pebbled
  Console.Out.Flush()

  printf "\nModular adder 32:\n"
  ignore <| run (addMod 32) Default Pebbled
  Console.Out.Flush()

  printf "\nCucarro adder 32:\n"
  ignore <| run (cucarro 32) Default Pebbled
  Console.Out.Flush()

  printf "\nMult 32:\n"
  ignore <| run (mult 32) Default Pebbled
  Console.Out.Flush()

  printf "\nCarry-Lookahead 32:\n"
  ignore <| run (carryLookaheadAdder 32) Default Pebbled
  Console.Out.Flush()

  printf "\nma4:\n"
  ignore <| run (ma4) Default Pebbled
  Console.Out.Flush()

  printf "\nSHA (64 rounds):\n"
  ignore <| run (SHA2 64) Default Pebbled
  Console.Out.Flush()

  printf "\nSHA (64 rounds) -- manual cleanup:\n"
  ignore <| run (SHA2Efficient 64) Default Pebbled
  Console.Out.Flush()

  printf "\nMD5 (64 rounds):\n"
  ignore <| run (MD5 64) Default Pebbled
  Console.Out.Flush()

  printf "\nKeccak (64 bit lanes):\n"
  ignore <| run (keccakf 64) Default Pebbled
  Console.Out.Flush()

  printf "\nKeccak (64 bit lanes) -- in place:\n"
  ignore <| run (keccakfInPlace 64) Default Pebbled
  Console.Out.Flush()*)
  0
