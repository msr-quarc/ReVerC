module Util

(* Util - General utilities. Sets & set lemmas, monads, list functions *)

type fin (n:nat) = m:nat{m <= n}

// Functional sets, strictly for proofs. Mostly identical to Set.fst but
//   it compiles, hides some definitions, and defines subsets propositionally
//   rather than computationally
type set (a:Type) = a -> Tot bool

val mem          : #a:Type -> a -> set a -> Tot bool
val empty        : #a:Type -> Tot (set a)
val singleton    : #a:Type -> a -> Tot (set a)
val union        : #a:Type -> set a -> set a -> Tot (set a)
val intersection : #a:Type -> set a -> set a -> Tot (set a)
val complement   : #a:Type -> set a -> Tot (set a)
val ins          : #a:Type -> a -> set a -> Tot (set a)

let mem i s          = s i
let empty            = fun _ -> false
let singleton a      = fun b -> b = a
let union a b        = fun c -> a c || b c
let intersection a b = fun c -> a c && b c
let complement s     = fun x -> not (s x)
let ins a b          = union (singleton a) b

open FunctionalExtensionality
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

// Error reporting monads
type result 'a =
  | Val : 'a -> result 'a
  | Err : string -> result 'a

val get_Val : r:(result 'a){is_Val r} -> Tot 'a
let get_Val r = match r with
  | Val v -> v

val bind : result 'a -> ('a -> result 'b) -> result 'b
val bindT : result 'a -> ('a -> Tot (result 'b)) -> Tot (result 'b)
let bind v f = match v with
  | Val x -> f x
  | Err s -> Err s
let bindT v f = match v with
  | Val x -> f x
  | Err s -> Err s

val foldM : ('a -> 'b -> result 'a) -> 'a -> l:(list 'b) -> result 'a
let rec foldM f a lst = match lst with
  | [] -> Val a
  | x::xs -> bind (f a x) (fun res -> foldM f res xs)

// Extra list operations
val mems : #a:Type -> list a -> Tot (set a)
let mems l = fun i -> List.mem i l

val nthT : l:list 'a -> i:int{i >= 0 && i < List.lengthT l} -> Tot 'a
let rec nthT l i = match l with
  | x::xs -> if i = 0 then x else nthT xs (i-1)

val for_someT: ('a -> Tot bool) -> list 'a -> Tot bool
let rec for_someT f l = match l with
    | [] -> false
    | hd::tl -> if f hd then true else for_someT f tl

val take : l:(list 'a) -> i:int{i < List.length l} -> Tot (list 'a) (decreases i)
let rec take l i =
  if i <= 0 then []
  else match l with
    | x::xs -> x::(take xs (i - 1))

val remove : l:(list 'a) -> i:nat{i < List.length l} ->
  Tot (l':(list 'a){List.length l' = List.length l - i}) (decreases i)
let rec remove l i =
  if i = 0 then l
  else match l with
    | _::xs -> remove xs (i - 1)

val rotate_rec : acc:(list 'a) -> l:(list 'a) -> i:nat{i < List.length l} -> Tot (list 'a) (decreases i)
let rec rotate_rec acc l i =
  if i = 0 then acc@(List.rev l)
  else match l with
    | x::xs -> rotate_rec (x::acc) xs (i-1)

// Rotates a list by i indices
val rotate : l:(list 'a) -> i:nat{i < List.length l} -> Tot (list 'a) (decreases i)
let rotate l i =
  ListProperties.rev_length l;
  rotate_rec [] (List.rev l) i

val slice : l:(list 'a) -> i:nat -> j:nat{i <= j && j < List.length l} -> Tot (list 'a)
let slice l i j = take (remove l i) (j - i + 1)

// Generates a list of j Booleans representing the number i mod 2^j
val of_int : i:nat -> j:int -> Tot (list bool) (decreases j)
let rec of_int i j =
  if j <= 0 then []
  else (i % 2 = 1)::(of_int (i / 2) (j - 1))
