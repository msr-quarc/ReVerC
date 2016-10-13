(** Extra set operations *)
module SetExtra
open FStar.Set

val full      : #a:eqtype -> Tot (set a)
val diff      : #a:eqtype -> set a -> set a -> Tot (set a)
val symdiff   : #a:eqtype -> set a -> set a -> Tot (set a)
val ins       : #a:eqtype -> a -> set a -> Tot (set a)
val rem       : #a:eqtype -> a -> set a -> Tot (set a)

(* This is poor design. Computational sets are needed elsewhere... *)
val fold      : #a:eqtype -> #b:eqtype -> (b -> a -> b) -> b -> set a -> b

(* Specific instances *)
val greaterEq : int -> Tot (set int)

let full #a         = complement (empty #a)
let diff #a s s'    = intersect s (complement s')
let symdiff #a s s' = diff (union s s') (intersect s s')
let ins #a x s      = union (singleton x) s 
let rem #a x s      = diff s (singleton x)

let fold #a #b f b s = admit()

let greaterEq i = admit()

(** Verification utilities *)

val greaterEq_elts : i:int -> j:int ->
  Lemma (requires True)
        (ensures (mem i (greaterEq j) <==> i >= j))
  [SMTPat (mem i (greaterEq j))]
let greaterEq_elts i j = admit()

(* Subset relation & lemmas *)
type disjoint (#a:eqtype) (s:set a) (s':set a) = forall x. ~(mem x s /\ mem x s')

val subset_trans : #a:eqtype -> s:set a -> s':set a -> s'':set a ->
  Lemma (requires (subset s s' /\ subset s' s''))
        (ensures  (subset s s''))
let subset_trans #a s s' s'' = ()

val subset_ins : #a:eqtype -> x:a -> s:set a ->
  Lemma (subset s (ins x s))
let subset_ins #a x s = ()

val ins_rem_equal : #a:eqtype -> x:a -> s:set a ->
  Lemma (requires True)
	(ensures (ins x (rem x s) == (ins x s)))
  [SMTPat (ins x (rem x s))]
let ins_rem_equal #a x s =
  lemma_equal_intro (ins x (rem x s)) (ins x s)

val ins_subset_pres : #a:eqtype -> x:a -> s:set a -> s':set a ->
  Lemma (requires (subset s s'))
        (ensures  (subset (ins x s) (ins x s')))
let ins_subset_pres #a x s s' = ()

val disjoint_subset : #a:eqtype -> s:set a -> s':set a -> s'':set a ->
  Lemma (requires (subset s s' /\ disjoint s' s''))
        (ensures  (disjoint s s''))
let disjoint_subset #a s s' s'' = ()

val disjoint_union : #a:eqtype -> s:set a -> s':set a -> s'':set a ->
  Lemma (requires (disjoint s s' /\ disjoint s s''))
        (ensures  (disjoint s (union s' s'')))
let disjoint_union #a s s' s'' = ()

val disjoint_is_subset_compl : #a:eqtype -> s:set a -> s':set a ->
  Lemma (disjoint s s' <==> subset s (complement s'))
let disjoint_is_subset_compl #a s s' = ()

val subset_compl_reverse : #a:eqtype -> s:set a -> s':set a ->
  Lemma (subset s s' <==> subset (complement s') (complement s))
let subset_compl_reverse #a s s' = ()

val union_equal : #a:eqtype ->
  Lemma (equal (empty #a) (union (empty #a) (empty #a)))
let union_equal #a = ()
