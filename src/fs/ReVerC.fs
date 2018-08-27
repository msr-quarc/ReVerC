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

type compileMode =
  | Basic
  | Eager
  | Crush

type outputType =
  | DotQC
  | QSharp

// Printing methods

let printQCV circ varlist = 
    let printPrim = 
        function 
        | RCNOT(x, y) -> sprintf "tof %d %d\n" x y
        | RTOFF(x, y, z) -> sprintf "tof %d %d %d\n" x y z
        | RNOT x-> sprintf "not %d\n" x
    let varstr = FStar.String.concat " " (List.map (fun i -> i.ToString()) varlist)
    let header = ".v " + varstr + "\n.i " + varstr + "\n.o " + varstr
    let gsStrs = List.map printPrim circ
    let mutable gateStr = String.concat "" gsStrs
    header + "\nBEGIN\n" + gateStr + "\nEND\n"

let printQSharpSimple circ =
    let printPrim =
        function
        | RCNOT(x, y)    -> sprintf "CNOT(qubits[%d], qubits[%d]);\n" x y
        | RTOFF(x, y, z) -> sprintf "CCNOT(qubits[%d], qubits[%d], qubits[%d]);\n" x y z
        | RNOT x         -> sprintf "X(qubits[%d])\n" x
    let body = String.concat "" <| List.map (fun gate -> "\t\t\t" + printPrim gate) circ
    "namespace Quantum.ReVerC\n{\n" +
    "\topen Microsoft.Quantum.Primitive;\n" +
    "\topen Microsoft.Quantum.Canon;\n\n" +
    "\toperation revCircuit(qubits : Qubit[]) : ()\n\t{\n" +
    "\t\tbody\n\t\t{\n" +
    body +
    "\t\t}\n\t}\n}"

let printStats circ = 
  let isToff = function
    | RTOFF _ -> true
    | _       -> false
  printf "Bits used: %d\n" (Set.count (uses circ))
  printf "Gates: %d\n" (List.length circ)
  printf "Toffolis: %d\n" (List.length (List.filter isToff circ))

// Main utilities

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

let copyOut res = match res with
  | Err s -> Err s
  | Val (par, [], circ) -> Val (par, [], circ)
  | Val (par, output, circ) ->
      let top = 1 + (Seq.max (Set.toList (uses circ)))
      let copy = List.mapi (fun i x -> RCNOT(x, top+i)) output
      Val (par, [top .. top + (List.length output)], circ @ copy @ (List.rev circ))

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
          | Basic -> copyOut <| Compiler.compileCirc [] (gexp', Compiler.circInit)
          | Eager -> copyOut <| GC.compileGCCirc [] (gexp', GC.circGCInit)
          | Crush -> Crush.compile [] (gexp', Crush.bexpInit) Crush.Pebbled
        match res with
          | Err s -> printf "%s\n" s
          | Val (par, res, circ) ->
              let src = match otype with
                | DotQC -> printQCV circ (Set.toList (uses circ))
                | QSharp -> printQSharpSimple circ
              File.WriteAllText(ofile, src)
