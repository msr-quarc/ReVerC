(** Reversible circuit data type & utilities *)
module Circuit

(* Reversible circuit data structure & utilities. Properties proven
   mainly involve which bits may be modified by a circuit, and that
   various methods of uncomputing a computation are correct *)

open Total

type Gate =
  | RCNOT of int * int
  | RTOFF of int * int * int
  | RNOT  of int

type Circuit = list<Gate>

(* Printing *)
let prettyPrintGate gate = match gate with
  | RCNOT (a, b) -> FStar.String.strcat "tof " (FStar.String.strcat (Prims.string_of_int a) (FStar.String.strcat " " (Prims.string_of_int b)))
  | RTOFF (a, b, c) -> FStar.String.strcat "tof " (FStar.String.strcat (Prims.string_of_int a) (FStar.String.strcat " " (FStar.String.strcat (Prims.string_of_int b) (FStar.String.strcat " " (Prims.string_of_int c)))))
  | RNOT a -> FStar.String.strcat "tof " (Prims.string_of_int a)

let prettyPrintCircuit = List.map prettyPrintGate

(* Evaluation *)
let applyGate st gate = match gate with
  | RCNOT (a, b)    -> update st b ((lookup st a) <> (lookup st b))
  | RTOFF (a, b, c) -> update st c ((lookup st c) <> ((lookup st a) && (lookup st b)))
  | RNOT  a         -> update st a (not (lookup st a))

let rec evalCirc gates st = match gates with
  | [] -> st
  | x::xs -> evalCirc xs (applyGate st x)

(* Well formed circuits *)
let wfGate gate = match gate with
  | RCNOT (a, b) -> not (a = b)
  | RTOFF (a, b, c) -> not (a = c) && not (b = c)
  | RNOT a -> true

let rec wfCirc circ = match circ with
  | [] -> true
  | x::xs -> wfGate x && wfCirc xs

(* Uses, targets, and controls *)
let rec used i lst = match lst with
  | [] -> false
  | (RCNOT (a, b))::xs    -> a = i || b = i || used i xs
  | (RTOFF (a, b, c))::xs -> a = i || b = i || c = i || used i xs
  | (RNOT a)::xs          -> a = i || used i xs
let uses gates = 
  let rec uses_acc gates acc = match gates with
    | []                    -> acc
    | (RCNOT (a, b))::xs    -> uses_acc xs (Set.add a (Set.add b acc))
    | (RTOFF (a, b, c))::xs -> uses_acc xs (Set.add a (Set.add b (Set.add c acc)))
    | (RNOT a)::xs          -> uses_acc xs (Set.add a acc)
  in
    uses_acc gates Set.empty

let rec modded i gates = match gates with
  | [] -> false
  | (RCNOT (_, t))::xs
  | (RTOFF (_, _, t))::xs
  | (RNOT t)::xs -> i = t || modded i xs
let rec mods gates = match gates with
  | [] -> Set.empty
  | (RCNOT (_, t))::xs
  | (RTOFF (_, _, t))::xs
  | (RNOT t)::xs -> Set.add t (mods xs)

let rec ctrl i lst = match lst with
  | [] -> false
  | (RCNOT (a, b))::xs    -> a = i || ctrl i xs
  | (RTOFF (a, b, c))::xs -> a = i || b = i || ctrl i xs
  | (RNOT a)::xs          -> ctrl i xs
let rec ctrls gates = match gates with
  | [] -> Set.empty
  | (RCNOT (a, b))::xs    -> Set.add a (ctrls xs)
  | (RTOFF (a, b, c))::xs -> Set.add a (Set.add b (ctrls xs))
  | (RNOT a)::xs          -> ctrls xs

(* Uncompute relative a target bit *)
let rec uncompute circ targ = match circ with
  | [] -> []
  | x::xs -> if (used targ [x]) then uncompute xs targ else x::(uncompute xs targ)

