module Circuit

(* Circuit - Reversible circuit data structure & utilities. Properties proven
             mainly involve which bits may be modified by a circuit, and that
             various methods of uncomputing a computation are correct *)

open Util
open Total

type Gate =
  | RCNOT of int * int
  | RTOFF of int * int * int
  | RNOT  of int

type Circuit =
  { gates : list Gate;
    inputs : list (string * int);
    outputs : list int;
    ancilla : int }

// Printing
val prettyPrintGate : Gate -> string
let prettyPrintGate gate = match gate with
  | RCNOT (a, b) -> String.strcat "tof "
                   (String.strcat (Prims.string_of_int a)
                   (String.strcat " " (Prims.string_of_int b)))
  | RTOFF (a, b, c) -> String.strcat "tof "
                      (String.strcat (Prims.string_of_int a)
                      (String.strcat " "
                      (String.strcat (Prims.string_of_int b)
                      (String.strcat " " (Prims.string_of_int c)))))
  | RNOT a -> String.strcat "tof " (Prims.string_of_int a)

val prettyPrintCircuit : list Gate -> list string
let prettyPrintCircuit = List.map prettyPrintGate

// Evaluation
val applyGate : state -> Gate -> Tot state
let applyGate st gate = match gate with
  | RCNOT (a, b)    -> update st b ((st a) <> (st b))
  | RTOFF (a, b, c) -> update st c ((st c) <> ((st a) && (st b)))
  | RNOT  a         -> update st a (not (st a))

val evalCirc : list Gate -> state -> Tot state
let rec evalCirc gates st = match gates with
  | [] -> st
  | x::xs -> evalCirc xs (applyGate st x)

// Well formed
val wfGate : Gate -> Tot bool
let wfGate gate = match gate with
  | RCNOT (a, b) -> not (a = b)
  | RTOFF (a, b, c) -> not (a = c) && not (b = c)
  | RNOT a -> true

val wfCirc : list Gate -> Tot bool
let rec wfCirc circ = match circ with
  | [] -> true
  | x::xs -> wfGate x && wfCirc xs

// Qubits used by a circuit
val used : int -> list Gate -> Tot bool
let rec used i lst = match lst with
  | [] -> false
  | (RCNOT (a, b))::xs    -> a = i || b = i || used i xs
  | (RTOFF (a, b, c))::xs -> a = i || b = i || c = i || used i xs
  | (RNOT a)::xs          -> a = i || used i xs

val uses : list Gate -> Tot (set int)
let uses lst = fun i -> used i lst

// Qubits modified by a circuit
val modded : int -> list Gate -> Tot bool
let rec modded i gates = match gates with
  | [] -> false
  | (RCNOT (_, t))::xs
  | (RTOFF (_, _, t))::xs
  | (RNOT t)::xs -> i = t || modded i xs

val mods : list Gate -> Tot (set int)
let mods gates = fun i -> modded i gates

// Qubits used as controls
val ctrl : int -> list Gate -> Tot bool
let rec ctrl i lst = match lst with
  | [] -> false
  | (RCNOT (a, b))::xs    -> a = i || ctrl i xs
  | (RTOFF (a, b, c))::xs -> a = i || b = i || ctrl i xs
  | (RNOT a)::xs          -> ctrl i xs

val ctrls : list Gate -> Tot (set int)
let ctrls gates = fun i -> ctrl i gates

// Uncompute relative a target bit
val uncompute : list Gate -> int -> Tot (list Gate)
let rec uncompute circ targ = match circ with
  | [] -> []
  | x::xs -> if (used targ [x]) then uncompute xs targ else x::(uncompute xs targ)

// ---------------------------------------------------------- Circuit properties

// Lemmas about modified bits
val ref_imp_use : gates:(list Gate) ->
  Lemma (forall i. modded i gates \/ ctrl i gates <==> used i gates)
let rec ref_imp_use gates = match gates with
  | [] -> ()
  | x::xs -> ref_imp_use xs

val mods_sub_uses : gates:list Gate ->
  Lemma (subset (mods gates) (uses gates))
let mods_sub_uses gates = ref_imp_use gates

val ctrls_sub_uses : gates:list Gate ->
  Lemma (subset (ctrls gates) (uses gates))
let ctrls_sub_uses gates = ref_imp_use gates

val apply_mod : st:state -> x:Gate ->
  Lemma (agree_on st (applyGate st x) (complement (mods [x])))
let apply_mod st x = ()

val eval_mod : st:state -> gates:(list Gate) ->
  Lemma (agree_on st (evalCirc gates st) (complement (mods gates)))
let rec eval_mod st gates = match gates with
  | [] -> ()
  | x::xs -> apply_mod st x; eval_mod (applyGate st x) xs

// Append lemmas, uses SMTPat to expand out automatically (hopefully)

val evalCirc_append : l1:(list Gate) -> l2:(list Gate) -> st:state ->
  Lemma (requires true)
        (ensures (evalCirc (l1@l2) st = evalCirc l2 (evalCirc l1 st)))
  [SMTPat (evalCirc (l1@l2) st)]
let rec evalCirc_append l1 l2 st = match l1 with
  | [] -> ()
  | x::xs -> evalCirc_append xs l2 (applyGate st x)

val use_append : i:int -> x:(list Gate) -> y:(list Gate) ->
  Lemma (requires true)
        (ensures  (used i (x@y) <==> used i x \/ used i y))
  [SMTPat (used i (x@y))]
let rec use_append i x y = match x with
  | [] -> ()
  | x::xs -> use_append i xs y

val uses_append : x:(list Gate) -> y:(list Gate) ->
  Lemma (requires true)
        (ensures  (uses (x@y) = union (uses x) (uses y)))
  [SMTPat (uses (x@y))]
let rec uses_append x y =
  lemma_equal_intro (uses (x@y)) (union (uses x) (uses y))

val mod_append : i:int -> l1:(list Gate) -> l2:(list Gate) ->
  Lemma (requires true)
        (ensures  (modded i (l1@l2) <==> modded i l1 \/ modded i l2))
  [SMTPat (modded i (l1@l2))]
let rec mod_append i l1 l2 = match l1 with
  | [] -> ()
  | x::xs -> mod_append i xs l2

val mods_append : x:(list Gate) -> y:(list Gate) ->
  Lemma (requires true)
        (ensures  (mods (x@y) = union (mods x) (mods y)))
  [SMTPat (mods (x@y))]
let rec mods_append x y =
  lemma_equal_intro (mods (x@y)) (union (mods x) (mods y))

val ctrl_append : i:int -> x:(list Gate) -> y:(list Gate) ->
  Lemma (requires true)
        (ensures  (ctrl i (x@y) <==> ctrl i x \/ ctrl i y))
  [SMTPat (ctrl i (x@y))]
let rec ctrl_append i x y = match x with
  | [] -> ()
  | x::xs -> ctrl_append i xs y

val ctrls_append : x:(list Gate) -> y:(list Gate) ->
  Lemma (requires true)
        (ensures  (ctrls (x@y) = union (ctrls x) (ctrls y)))
  [SMTPat (ctrls (x@y))]
let rec ctrls_append x y =
  lemma_equal_intro (ctrls (x@y)) (union (ctrls x) (ctrls y))

val wf_append : x:list Gate -> y:list Gate ->
  Lemma (requires (wfCirc x /\ wfCirc y))
        (ensures  (wfCirc (x@y)))
  [SMTPat (wfCirc (x@y))]
let rec wf_append x y = match x with
  | [] -> ()
  | x::xs -> wf_append xs y

// Lemmas about reversibility
val rev_uses : circ:list Gate ->
  Lemma (requires true)
        (ensures (uses circ = uses (List.rev circ)))
  [SMTPat (uses (List.rev circ))]
let rec rev_uses circ = match circ with
  | [] -> ()
  | x::xs ->
    ListProperties.rev_append [x] xs;
    rev_uses xs;
    lemma_equal_intro (uses circ) (uses (List.rev circ))

val rev_mods : circ:list Gate ->
  Lemma (requires true)
        (ensures (mods circ = mods (List.rev circ)))
  [SMTPat (mods (List.rev circ))]
let rec rev_mods circ = match circ with
  | [] -> ()
  | x::xs ->
    ListProperties.rev_append [x] xs;
    rev_mods xs;
    lemma_equal_intro (mods circ) (mods (List.rev circ))

val rev_ctrls : circ:list Gate ->
  Lemma (requires true)
        (ensures (ctrls circ = ctrls (List.rev circ)))
  [SMTPat (ctrls (List.rev circ))]
let rec rev_ctrls circ = match circ with
  | [] -> ()
  | x::xs ->
    ListProperties.rev_append [x] xs;
    rev_ctrls xs;
    lemma_equal_intro (ctrls circ) (ctrls (List.rev circ))

val evalCirc_append_rev : x:list Gate -> y:list Gate -> st:state ->
  Lemma (evalCirc (List.rev (x@y)) st = evalCirc (List.rev x) (evalCirc (List.rev y) st))
let evalCirc_append_rev x y st = ListProperties.rev_append x y

val rev_gate : gate:Gate -> st:state ->
  Lemma (requires (wfGate gate))
        (ensures  (applyGate (applyGate st gate) gate = st))
let rev_gate gate st = lemma_map_equal_intro (applyGate (applyGate st gate) gate) st

val rev_inverse : circ:list Gate -> st:state ->
  Lemma (requires (wfCirc circ))
        (ensures  (evalCirc (circ@(List.rev circ)) st = st))
let rec rev_inverse circ st = match circ with
  | [] -> ()
  | x::xs ->
    rev_inverse xs (applyGate st x);
    evalCirc_append_rev [x] xs (evalCirc xs (applyGate st x));
    rev_gate x st

val applyGate_state_swap : x:Gate -> st:state -> st':state -> dom:set int ->
  Lemma (requires (subset (ctrls [x]) dom /\ agree_on st st' dom))
        (ensures  (agree_on (applyGate st x) (applyGate st' x) dom))
let applyGate_state_swap x st st' dom = ()

val evalCirc_state_swap : circ:list Gate -> st:state -> st':state -> dom:set int ->
  Lemma (requires (subset (ctrls circ) dom /\ agree_on st st' dom))
        (ensures  (agree_on (evalCirc circ st) (evalCirc circ st') dom))
let rec evalCirc_state_swap circ st st' dom = match circ with
  | [] -> ()
  | x::xs ->
    applyGate_state_swap x st st' dom;
    evalCirc_state_swap xs (applyGate st x) (applyGate st' x) dom

// Lemmas for uncomputing after copying to a target
val bennett : comp:list Gate -> copy:list Gate -> st:state ->
  Lemma (requires (wfCirc comp /\ disjoint (uses comp) (mods copy)))
        (ensures  (agree_on st (evalCirc (comp@copy@(List.rev comp)) st) (uses comp)))
let bennett comp copy st =
  let st'   = evalCirc comp st in
  let st''  = evalCirc copy st' in
    eval_mod st' copy;
    ctrls_sub_uses (List.rev comp);
    evalCirc_state_swap (List.rev comp) st' st'' (uses comp);
    rev_inverse comp st

val uncompute_targ : circ:list Gate -> targ:int ->
  Lemma (not (modded targ (uncompute circ targ)))
let rec uncompute_targ circ targ = match circ with
  | [] -> ()
  | x::xs -> uncompute_targ xs targ

val uncompute_wf : circ:list Gate -> targ:int ->
  Lemma (requires (wfCirc circ))
        (ensures  (wfCirc (uncompute circ targ)))
  [SMTPat (wfCirc (uncompute circ targ))]
let rec uncompute_wf circ targ = match circ with
  | [] -> ()
  | x::xs -> uncompute_wf xs targ

val uncompute_uses_subset : circ:list Gate -> targ:int ->
  Lemma (requires (wfCirc circ))
        (ensures  (subset (uses (uncompute circ targ)) (uses circ)))
let rec uncompute_uses_subset circ targ = match circ with
  | [] -> ()
  | x::xs -> uncompute_uses_subset xs targ

val uncompute_ctrls_subset : circ:list Gate -> targ:int ->
  Lemma (requires (wfCirc circ))
        (ensures  (subset (ctrls (uncompute circ targ)) (ctrls circ)))
let rec uncompute_ctrls_subset circ targ = match circ with
  | [] -> ()
  | x::xs -> uncompute_ctrls_subset xs targ

val uncompute_agree : circ:list Gate -> targ:int -> st:state ->
  Lemma (requires (wfCirc circ /\ not (ctrl targ circ)))
        (ensures  (agree_on (evalCirc circ st)
                            (evalCirc (uncompute circ targ) st)
                            (complement (singleton targ))))
let rec uncompute_agree circ targ st = match circ with
  | [] -> ()
  | x::xs ->
    if (used targ [x])
    then
      (evalCirc_state_swap xs (applyGate st x) st (complement (singleton targ));
       uncompute_agree xs targ st;
       agree_on_trans (evalCirc xs (applyGate st x))
                      (evalCirc xs st)
                      (evalCirc (uncompute xs targ) st)
                      (complement (singleton targ)))
    else uncompute_agree xs targ (applyGate st x)


val uncompute_mixed_inverse : circ:list Gate -> targ:int -> st:state ->
  Lemma (requires (wfCirc circ /\ not (ctrl targ circ)))
        (ensures  (agree_on st (evalCirc (List.rev (uncompute circ targ))
                                         (evalCirc circ st))
                               (complement (singleton targ))))
let uncompute_mixed_inverse circ targ st =
  uncompute_agree circ targ st;
  uncompute_ctrls_subset circ targ;
  evalCirc_state_swap (List.rev (uncompute circ targ))
                      (evalCirc circ st)
                      (evalCirc (uncompute circ targ) st)
                      (complement (singleton targ));
  rev_inverse (uncompute circ targ) st
