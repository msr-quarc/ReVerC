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

// Printing methods

let printQCV (par, out, circ) = 
    let printPrim = 
        function 
        | RCNOT(x, y) -> sprintf "tof %d %d\n" x y
        | RTOFF(x, y, z) -> sprintf "tof %d %d %d\n" x y z
        | RNOT x-> sprintf "not %d\n" x
    let varstr = FStar.String.concat " " (List.map (fun i -> i.ToString()) (Set.toList (uses circ)))
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

let toQSharp name (par, out, circ) =
    // Process parameters
    let (paramList, symtab) =
        let getLocs xs =
            let getLoc gexp = match gexp with
                | LOC i -> i
                | _     -> failwith "Impossible"
            List.map getLoc xs 
        let addParam (pList, stab) (x, v) = match v with
            | LOC l    -> ((sprintf "%s : Qubit" x)::pList, Map.add l x stab)
            | ARRAY xs ->
                let locs = List.mapi (fun i l -> (l, i)) <| getLocs xs
                let f stab (l, i) = Map.add l (sprintf "%s[%d]" x i) stab
                ((sprintf "%s : Qubit[]" x)::pList, List.fold f stab locs)
        let (paramList, symtab) = List.fold addParam ([], Map.empty) par
        match out with
            | [] -> (paramList, symtab)
            | _  -> addParam (paramList, symtab) ("output", ARRAY (List.map LOC out))

    // Process gates
    let (num, _, body) =
        let f (n, stab, body) gate =
            let args = match gate with
                | RNOT x         -> [x]
                | RCNOT(x, y)    -> [x;y]
                | RTOFF(x, y, z) -> [x;y;z]
            let processArg (n, stab) x = match Map.tryFind x stab with
                | Some x -> (n, stab)
                | None   -> (n+1, Map.add x (sprintf "anc[%d]" n) stab)
            let (n, stab) = List.fold processArg (n, stab) args
            let gstr = match gate with
                | RNOT x         -> sprintf "X(%s);" (Map.find x stab)
                | RCNOT(x, y)    -> sprintf "CNOT(%s, %s);" (Map.find x stab) (Map.find y stab)
                | RTOFF(x, y, z) ->
                    sprintf "CCNOT(%s, %s, %s);" (Map.find x stab) (Map.find y stab) (Map.find z stab)
            (n, stab, gstr::body)
        List.fold f (0, symtab, []) circ
    ["operation " + name + "(" + String.concat ", " (List.rev paramList) + ") : ()";
     "{";
     "\tbody";
     "\t{";
     sprintf "\t\tusing (anc = Qubit[%d])" num;
     "\t\t{"] @
    List.map (fun gate -> "\t\t\t" + gate) (List.rev body) @
    ["\t\t}";
     "\t}";
     "}"]

let qSharpHeader =
    "namespace Quantum.ReVerC\n{\n" +
    "\topen Microsoft.Quantum.Primitive;\n" +
    "\topen Microsoft.Quantum.Canon;\n\n"

let printQSharpBody name res =
    let op = toQSharp name res
    String.concat "\n" (List.map (fun line -> "\t" + line) op)

let printQSharp name res = qSharpHeader + printQSharpBody name res + "\n}"

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

let compile quote verif mode =
  // Parsing
  let (top, gexp) = parseAST quote
  // Type inference
  match typeCheck top gexp with
    | None ->
        printf "Error: could not infer types\n"
        ([], [], [])
    | Some gexp' ->
        // Verification
        if verif then verify gexp'
        // Compilation
        let res = match mode with 
          | Basic -> copyOut <| Compiler.compileCirc [] (gexp', Compiler.circInit)
          | Eager -> copyOut <| GC.compileGCCirc [] (gexp', GC.circGCInit)
          | Crush -> Crush.compile [] (gexp', Crush.bexpInit) Crush.Pebbled
        match res with
          | Err s ->
              printf "%s\n" s
              ([], [], [])
          | Val (par, out, circ) -> (List.rev par, out, circ)
