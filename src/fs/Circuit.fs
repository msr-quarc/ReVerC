module Circuit
open Util
open Maps.Total

type Gate =
  | RCNOT of int * int
  | RTOFF of int * int * int
  | RNOT  of int

type Circuit =
  { gates : list<Gate>;
    inputs : list<string * int>;
    outputs : list<int>;
    ancilla : int }

// Printing
//val prettyPrintGate : Gate -> string
let prettyPrintGate gate = match gate with
  | RCNOT (a, b) -> "tof " ^ (IO.string_of_int a) ^ " " ^ (IO.string_of_int b)
  | RTOFF (a, b, c) -> "tof " ^ (IO.string_of_int a) ^ " " ^ (IO.string_of_int b) ^ " " ^ (IO.string_of_int c)
  | RNOT a -> "tof " ^ (IO.string_of_int a)

//val prettyPrintCircuit : list Gate -> list string
let prettyPrintCircuit = List.map prettyPrintGate

// Evaluation
//val applyGate : state -> Gate -> Tot state
let applyGate st gate = match gate with
  | RCNOT (a, b)    -> update st b ((st a) <> (st b))
  | RTOFF (a, b, c) -> update st c ((st c) <> ((st a) && (st b)))
  | RNOT  a         -> update st a (not (st a))

//val evalCirc : list Gate -> state -> Tot state
let rec evalCirc gates st = match gates with
  | [] -> st
  | x::xs -> evalCirc xs (applyGate st x)

// Well formed
//val wfGate : Gate -> Tot bool
let wfGate gate = match gate with
  | RCNOT (a, b) -> not (a = b)
  | RTOFF (a, b, c) -> not (a = c) && not (b = c)
  | RNOT a -> true

//val wfCirc : list Gate -> Tot bool
let rec wfCirc circ = match circ with
  | [] -> true
  | x::xs -> wfGate x && wfCirc xs

// Qubits used by a circuit
//val use : int -> list Gate -> Tot bool
let rec uses i lst = match lst with
  | [] -> false
  | (RCNOT (a, b))::xs    -> a = i || b = i || uses i xs
  | (RTOFF (a, b, c))::xs -> a = i || b = i || c = i || uses i xs
  | (RNOT a)::xs          -> a = i || uses i xs

//val uses : list Gate -> Tot (set int)
let usess lst = fun i -> uses i lst

(*
let rec getUses lst = match lst with
    | [] -> Set.empty
    | (RCNOT (a, b))::xs -> Set.add a (Set.add b (getUses xs))
    | (RTOFF (a, b, c))::xs -> Set.add a (Set.add b (Set.add c (getUses xs)))
    | (RNOT a)::xs -> Set.add a (getUses xs)
*)

let getUses lst = 
  let rec getUsesAcc lst acc =
    match lst with
    | [] -> acc
    | (RCNOT (a, b))::xs -> getUsesAcc xs (Set.add a (Set.add b acc))
    | (RTOFF (a, b, c))::xs -> getUsesAcc xs (Set.add a (Set.add b (Set.add c acc)))
    | (RNOT a)::xs -> getUsesAcc xs (Set.add a acc)
  in
  getUsesAcc lst Set.empty
// Qubits modified by a circuit
//val mod : int -> list Gate -> Tot bool
let rec md i gates = match gates with
  | [] -> false
  | (RCNOT (_, t))::xs
  | (RTOFF (_, _, t))::xs
  | (RNOT t)::xs -> i = t || md i xs

//val mods : list Gate -> Tot (set int)
let mods gates = fun i -> md i gates

// Qubits used as controls
//val ctrl : int -> list Gate -> Tot bool
let rec ctrl i lst = match lst with
  | [] -> false
  | (RCNOT (a, b))::xs    -> a = i || ctrl i xs
  | (RTOFF (a, b, c))::xs -> a = i || b = i || ctrl i xs
  | (RNOT a)::xs          -> ctrl i xs

//val ctrls : list Gate -> Tot (set int)
let ctrls gates = fun i -> ctrl i gates

// Uncompute relative a target bit
//val uncompute : list Gate -> int -> Tot (list Gate)
let uncompute circ targ = 
  let rec uncompute_rec acc circ targ = match circ with
    | [] -> List.rev acc
    | x::xs -> if (uses targ [x]) then uncompute_rec acc xs targ else uncompute_rec (x::acc) xs targ
  uncompute_rec [] circ targ
