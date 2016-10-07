(** Reversible circuit data type & utilities *)
module Circuit

open FStar.Set
open SetExtra
open Total

(* Reversible circuit data structure & utilities.Properties proven
   mainly involve which bits may be modified by a circuit, and that
   various methods of uncomputing a computation are correct *)

type gate =
  | RCNOT of int * int
  | RTOFF of int * int * int
  | RNOT  of int

type circuit = list gate

val prettyPrintGate    : gate -> Tot string
val prettyPrintCircuit : circuit -> Tot (list string)

val applyGate          : state -> gate -> Tot state
val evalCirc           : circuit -> state -> Tot state
val wfGate             : gate -> Tot bool
val wfCirc             : circuit -> Tot bool
val uses               : circuit -> Tot (set int)
val mods               : circuit -> Tot (set int)
val ctrls              : circuit -> Tot (set int)
val uncompute          : circuit -> int -> Tot circuit

(* Printing *)
let prettyPrintGate gate = match gate with
  | RCNOT (a, b) -> FStar.String.strcat "tof "
                   (FStar.String.strcat (Prims.string_of_int a)
                   (FStar.String.strcat " " (Prims.string_of_int b)))
  | RTOFF (a, b, c) -> FStar.String.strcat "tof "
                      (FStar.String.strcat (Prims.string_of_int a)
                      (FStar.String.strcat " "
                      (FStar.String.strcat (Prims.string_of_int b)
                      (FStar.String.strcat " " (Prims.string_of_int c)))))
  | RNOT a -> FStar.String.strcat "tof " (Prims.string_of_int a)

let prettyPrintCircuit = FStar.List.Tot.map prettyPrintGate

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

(* Uses, targets, and controls. Uses mods and ctrls are highly inefficient *)
let rec uses lst = match lst with
  | []                   -> empty
  | (RCNOT (a, b))::xs    -> ins a (ins b (uses xs))
  | (RTOFF (a, b, c))::xs -> ins a (ins b (ins c (uses xs)))
  | (RNOT a)::xs          -> ins a (uses xs)

let rec mods gates = match gates with
  | []                   -> empty
  | (RCNOT (_, t))::xs
  | (RTOFF (_, _, t))::xs
  | (RNOT t)::xs          -> ins t (mods xs)

let rec ctrls lst = match lst with
  | []                   -> empty
  | (RCNOT (a, _))::xs    -> ins a (ctrls xs)
  | (RTOFF (a, b, _))::xs -> ins a (ins b (ctrls xs))
  | (RNOT _)::xs          -> ctrls xs

(* Uncompute relative a target bit *)
let rec uncompute circ targ = match circ with
  | [] -> []
  | x::xs -> if (mem targ (uses [x])) then uncompute xs targ else x::(uncompute xs targ)

(** Verification utilities *)

(* Lemmas about modified bits *)
val ref_imp_use : gates:circuit ->
  Lemma (Set.equal (uses gates) (union (mods gates) (ctrls gates)))
let rec ref_imp_use gates = match gates with
  | [] -> ()
  | x::xs -> ref_imp_use xs

val mods_sub_uses : gates:circuit ->
  Lemma (subset (mods gates) (uses gates))
let mods_sub_uses gates = ref_imp_use gates

val ctrls_sub_uses : gates:circuit ->
  Lemma (subset (ctrls gates) (uses gates))
let ctrls_sub_uses gates = ref_imp_use gates

val apply_mod : st:state -> x:gate ->
  Lemma (agree_on st (applyGate st x) (complement (mods [x])))
let apply_mod st x = ()

val eval_mod : st:state -> gates:circuit ->
  Lemma (requires True)
	(ensures (agree_on st (evalCirc gates st) (complement (mods gates))))
  (decreases gates)
let rec eval_mod st gates = match gates with
  | [] -> ()
  | x::xs -> apply_mod st x; eval_mod (applyGate st x) xs

(* Append lemmas, uses SMTPat to expand out automatically *)

val evalCirc_append : l1:circuit -> l2:circuit -> st:state ->
  Lemma (requires true)
        (ensures (evalCirc (l1@l2) st = evalCirc l2 (evalCirc l1 st)))
  [SMTPat (evalCirc (l1@l2) st)]
let rec evalCirc_append l1 l2 st = match l1 with
  | [] -> ()
  | x::xs -> evalCirc_append xs l2 (applyGate st x)

val uses_append : x:circuit -> y:circuit ->
  Lemma (requires True)
        (ensures (Set.equal (uses (x@y)) (union (uses x) (uses y))))
  [SMTPat (uses (x@y))]
let rec uses_append x y = match x with
  | [] -> ()
  | x::xs -> uses_append xs y

val mods_append : x:circuit -> y:circuit ->
  Lemma (requires True)
        (ensures  (Set.equal (mods (x@y)) (union (mods x) (mods y))))
  [SMTPat (mods (x@y))]
let rec mods_append x y = match x with
  | [] -> ()
  | x::xs -> mods_append xs y

val ctrls_append : x:circuit -> y:circuit ->
  Lemma (requires True)
        (ensures  (Set.equal (ctrls (x@y)) (union (ctrls x) (ctrls y))))
  [SMTPat (ctrls (x@y))]
let rec ctrls_append x y = match x with
  | [] -> ()
  | x::xs -> ctrls_append xs y

val wf_append : x:circuit -> y:circuit ->
  Lemma (requires (wfCirc x /\ wfCirc y))
        (ensures  (wfCirc (x@y)))
  [SMTPat (wfCirc (x@y))]
let rec wf_append x y = match x with
  | [] -> ()
  | x::xs -> wf_append xs y

(* Lemmas about reversibility *)
val rev_uses : circ:circuit ->
  Lemma (requires True)
        (ensures (Set.equal (uses circ) (uses (FStar.List.Tot.rev circ))))
  [SMTPat (uses (FStar.List.Tot.rev circ))]
let rec rev_uses circ = match circ with
  | [] -> ()
  | x::xs ->
    FStar.ListProperties.rev_append [x] xs;
    rev_uses xs;
    lemma_equal_intro (uses circ) (uses (FStar.List.Tot.rev circ))

val rev_mods : circ:circuit ->
  Lemma (requires True)
        (ensures (Set.equal (mods circ) (mods (FStar.List.Tot.rev circ))))
  [SMTPat (mods (FStar.List.Tot.rev circ))]
let rec rev_mods circ = match circ with
  | [] -> ()
  | x::xs ->
    FStar.ListProperties.rev_append [x] xs;
    rev_mods xs;
    lemma_equal_intro (mods circ) (mods (FStar.List.Tot.rev circ))

val rev_ctrls : circ:circuit ->
  Lemma (requires True)
        (ensures (Set.equal (ctrls circ) (ctrls (FStar.List.Tot.rev circ))))
  [SMTPat (ctrls (FStar.List.Tot.rev circ))]
let rec rev_ctrls circ = match circ with
  | [] -> ()
  | x::xs ->
    FStar.ListProperties.rev_append [x] xs;
    rev_ctrls xs;
    lemma_equal_intro (ctrls circ) (ctrls (FStar.List.Tot.rev circ))

val evalCirc_append_rev : x:circuit -> y:circuit -> st:state ->
  Lemma (evalCirc (FStar.List.Tot.rev (x@y)) st = evalCirc (FStar.List.Tot.rev x) (evalCirc (FStar.List.Tot.rev y) st))
let evalCirc_append_rev x y st = FStar.ListProperties.rev_append x y

val rev_gate : gate:gate -> st:state ->
  Lemma (requires (wfGate gate))
        (ensures  (equal (applyGate (applyGate st gate) gate) st))
let rev_gate gate st = lemma_map_equal_intro (applyGate (applyGate st gate) gate) st

val rev_inverse : circ:circuit -> st:state ->
  Lemma (requires (wfCirc circ))
        (ensures  (equal (evalCirc (circ@(FStar.List.Tot.rev circ)) st) st))
let rec rev_inverse circ st = match circ with
  | [] -> ()
  | x::xs ->
    rev_inverse xs (applyGate st x);
    evalCirc_append_rev [x] xs (evalCirc xs (applyGate st x));
    rev_gate x st;
    lemma_map_equal_intro (evalCirc (circ@(FStar.List.Tot.rev circ)) st) st

val applyGate_state_swap : x:gate -> st:state -> st':state -> dom:set int ->
  Lemma (requires (subset (ctrls [x]) dom /\ agree_on st st' dom))
        (ensures  (agree_on (applyGate st x) (applyGate st' x) dom))
let applyGate_state_swap x st st' dom = ()

val evalCirc_state_swap : circ:circuit -> st:state -> st':state -> dom:set int ->
  Lemma (requires (subset (ctrls circ) dom /\ agree_on st st' dom))
        (ensures  (agree_on (evalCirc circ st) (evalCirc circ st') dom))
let rec evalCirc_state_swap circ st st' dom = match circ with
  | [] -> ()
  | x::xs ->
    applyGate_state_swap x st st' dom;
    evalCirc_state_swap xs (applyGate st x) (applyGate st' x) dom

(* Lemmas for uncomputing after copying to a target *)
val bennett : comp:circuit -> copy:circuit -> st:state ->
  Lemma (requires (wfCirc comp /\ disjoint (uses comp) (mods copy)))
        (ensures  (agree_on st (evalCirc (comp@copy@(FStar.List.Tot.rev comp)) st) (uses comp)))
let bennett comp copy st =
  let st'   = evalCirc comp st in
  let st''  = evalCirc copy st' in
    eval_mod st' copy;
    ctrls_sub_uses (FStar.List.Tot.rev comp);
    evalCirc_state_swap (FStar.List.Tot.rev comp) st' st'' (uses comp);
    rev_inverse comp st

val uncompute_targ : circ:circuit -> targ:int ->
  Lemma (not (mem targ (mods (uncompute circ targ))))
let rec uncompute_targ circ targ = match circ with
  | [] -> ()
  | x::xs -> uncompute_targ xs targ

val uncompute_wf : circ:circuit -> targ:int ->
  Lemma (requires (wfCirc circ))
        (ensures  (wfCirc (uncompute circ targ)))
  [SMTPat (wfCirc (uncompute circ targ))]
let rec uncompute_wf circ targ = match circ with
  | [] -> ()
  | x::xs -> uncompute_wf xs targ

val uncompute_uses_subset : circ:circuit -> targ:int ->
  Lemma (requires (wfCirc circ))
        (ensures  (subset (uses (uncompute circ targ)) (uses circ)))
let rec uncompute_uses_subset circ targ = match circ with
  | [] -> ()
  | x::xs -> uncompute_uses_subset xs targ

val uncompute_ctrls_subset : circ:circuit -> targ:int ->
  Lemma (requires (wfCirc circ))
        (ensures  (subset (ctrls (uncompute circ targ)) (ctrls circ)))
let rec uncompute_ctrls_subset circ targ = match circ with
  | [] -> ()
  | x::xs -> uncompute_ctrls_subset xs targ

val uncompute_agree : circ:circuit -> targ:int -> st:state ->
  Lemma (requires (wfCirc circ /\ not (mem targ (ctrls circ))))
        (ensures  (agree_on (evalCirc circ st)
                            (evalCirc (uncompute circ targ) st)
                            (complement (singleton targ))))
let rec uncompute_agree circ targ st = match circ with
  | [] -> ()
  | x::xs ->
    if (mem targ (uses [x]))
    then
      (evalCirc_state_swap xs (applyGate st x) st (complement (singleton targ));
       uncompute_agree xs targ st;
       agree_on_trans (evalCirc xs (applyGate st x))
                      (evalCirc xs st)
                      (evalCirc (uncompute xs targ) st)
                      (complement (singleton targ)))
    else uncompute_agree xs targ (applyGate st x)


val uncompute_mixed_inverse : circ:circuit -> targ:int -> st:state ->
  Lemma (requires (wfCirc circ /\ not (mem targ (ctrls circ))))
        (ensures  (agree_on st (evalCirc (FStar.List.Tot.rev (uncompute circ targ))
                                         (evalCirc circ st))
                               (complement (singleton targ))))
let uncompute_mixed_inverse circ targ st =
  uncompute_agree circ targ st;
  uncompute_ctrls_subset circ targ;
  evalCirc_state_swap (FStar.List.Tot.rev (uncompute circ targ))
                      (evalCirc circ st)
                      (evalCirc (uncompute circ targ) st)
                      (complement (singleton targ));
  rev_inverse (uncompute circ targ) st

//let tmp = assert(forall st x. equal (applyGate st x) st)
