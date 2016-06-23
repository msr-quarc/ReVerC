(** Functional sets *)
module Set

(* Strictly for proofs. Mostly identical to Set.fst but
   it compiles, hides some definitions, and defines subsets propositionally
   rather than computationally *)
type set (a:Type) = a -> Tot bool

val mem          : #a:Type -> a -> set a -> Tot bool
val empty        : #a:Type -> Tot (set a)
val full         : #a:Type -> Tot (set a)
val singleton    : #a:Type -> a -> Tot (set a)
val union        : #a:Type -> set a -> set a -> Tot (set a)
val intersection : #a:Type -> set a -> set a -> Tot (set a)
val diff         : #a:Type -> set a -> set a -> Tot (set a)
val symdiff      : #a:Type -> set a -> set a -> Tot (set a)
val complement   : #a:Type -> set a -> Tot (set a)
val ins          : #a:Type -> a -> set a -> Tot (set a)

let mem i s          = s i
let empty            = fun _ -> false
let full             = fun _ -> true
let singleton a      = fun b -> b = a
let union a b        = fun c -> a c || b c
let intersection a b = fun c -> a c && b c
let diff a b         = fun c -> a c && not (b c)
let symdiff a b      = fun c -> (a c && not (b c)) || (not (a c) && b c)
let complement s     = fun x -> not (s x)
let ins a b          = union (singleton a) b

(** Verification utilities *)

(* Extensionality-based equality *)
open FStar.FunctionalExtensionality
type Equal (#a:Type) (s1:set a) (s2:set a) = FEq s1 s2
val lemma_equal_intro: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (Equal s1 s2))
    [SMTPatT (Equal s1 s2)]
val lemma_equal_elim: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (Equal s1 s2))
    (ensures  (s1 = s2))
    [SMTPatT (Equal s1 s2)]
val lemma_equal_refl: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (s1 = s2))
    (ensures  (Equal s1 s2))
    [SMTPatT (Equal s1 s2)]
let lemma_equal_intro s1 s2 = ()
let lemma_equal_elim s1 s2 = ()
let lemma_equal_refl s1 s2 = ()

(* Subset relation & lemmas *)
type subset (#a:Type) (s:set a) (s':set a) =
  forall i. s i ==> s' i
type disjoint (#a:Type) (s:set a) (s':set a) =
  forall i. ~(s i /\ s' i)

val subset_trans : #a:Type -> s:set a -> s':set a -> s'':set a ->
  Lemma (requires (subset s s' /\ subset s' s''))
        (ensures  (subset s s''))
let subset_trans s s' s'' = ()

val subset_ins : #a:Type -> i:a -> s:set a ->
  Lemma (subset s (ins i s))
let subset_ins i s = ()

val ins_subset_pres : #a:Type -> i:a -> s:set a -> s':set a ->
  Lemma (requires (subset s s'))
        (ensures  (subset (ins i s) (ins i s')))
let ins_subset_pres i s s' = ()

val disjoint_subset : #a:Type -> s:set a -> s':set a -> s'':set a ->
  Lemma (requires (subset s s' /\ disjoint s' s''))
        (ensures  (disjoint s s''))
let disjoint_subset s s' s'' = ()

val disjoint_union : #a:Type -> s:set a -> s':set a -> s'':set a ->
  Lemma (requires (disjoint s s' /\ disjoint s s''))
        (ensures  (disjoint s (union s' s'')))
let disjoint_union s s' s'' = ()
