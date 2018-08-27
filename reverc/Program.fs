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

let printIt (top, gexp) = printf "%s\n" (show gexp)
registerCmd "print" "Print the AST of the program" printIt

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
        let res = Compiler.compileCirc [] (gexp', Compiler.circInit)
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, _, circ) -> 
              let qcv = ReVerC.printQCV circ (Set.toList (uses circ))
              File.WriteAllText("output.qc", qcv)
              printf "%s" qcv
registerCmd "compile" "Compile the program in default mode" comp

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
        let res = Compiler.compileCirc [] (gexp', Compiler.circInit)
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, _, circ) -> 
              printf "Bits used: %d\n" (Set.count (uses circ))
              printf "Gates: %d\n" (List.length circ)
              printf "Toffolis: %d\n" (List.length (List.filter isToff circ))
registerCmd "compile-stats" "Compile the program in default mode, printing just circuit statistics" compStats

let compGC (top, gexp) = 
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
        let res = GC.compileGCCirc [] (gexp', GC.circGCInit)
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, _, circ) -> 
              let qcv = ReVerC.printQCV circ (Set.toList (uses circ))
              File.WriteAllText("output.qc", qcv)
              printf "%s" qcv
              let qsv = ReVerC.printQSharpSimple circ
              File.WriteAllText("output.qs", qsv)
              printf "%s" qsv
registerCmd "compileGC" "Compile the program with garbage collection" compGC

let compGCStats (top, gexp) = 
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
        let res = GC.compileGCCirc [] (gexp', GC.circGCInit)
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, _, circ) -> 
              printf "Bits used: %d\n" (Set.count (uses circ))
              printf "Gates: %d\n" (List.length circ)
              printf "Toffolis: %d\n" (List.length (List.filter isToff circ))
registerCmd "compileGC-stats" "Compile the program with garbage collection, printing just circuit statistics" compGCStats

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
        let res = Crush.compile [] (gexp', Crush.bexpInit) Crush.Pebbled
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, _, circ) -> 
              let qcv = ReVerC.printQCV circ (Set.toList (uses circ))
              File.WriteAllText("output.qc", qcv)
              printf "%s" qcv
registerCmd "crush" "Compile the program in space saving mode" crush

let crushStats (top, gexp) = 
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
        let res = Crush.compile [] (gexp', Crush.bexpInit) Crush.Pebbled
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, _, circ) -> 
              printf "Bits used: %d\n" (Set.count (uses circ))
              printf "Gates: %d\n" (List.length circ)
              printf "Toffolis: %d\n" (List.length (List.filter isToff circ))
registerCmd "crush-stats" "Compile the program in space saving mode, printing just circuit statistics" crushStats

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
          | Default   -> Compiler.compileCirc [] (gexp', Compiler.circInit)
          | SpaceSave -> Crush.compile [] (gexp', Crush.bexpInit) cleanupStrategy
        match res with
          | Err s -> printf "%s\n" s
          | Val (_, _, circ) -> 
              if info then 
                printf "Bits used: %d\n" (Set.count (uses circ))
                printf "Gates: %d\n" (List.length circ)
                printf "Toffolis: %d\n" (List.length (List.filter isToff circ))
              printf "%s" (ReVerC.printQCV circ (Set.toList (uses circ)))

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
          | Default   -> Compiler.compileCirc [] (gexp', Compiler.circInit)
          | SpaceSave -> Crush.compile [] (gexp', Crush.bexpInit) cleanupStrategy
        ()

[<EntryPoint>]
let __main _ = 
  ignore <| runHack polyEx Default Crush.Pebbled
  let mutable exit = false
  let mutable line = ""
  while (not exit) do
    Console.WriteLine "Enter a command: "
    line <- Console.ReadLine()
    printf "\n"
    if line = "exit" then exit <- true
    else parseLine line
    printf "\n"
  0
