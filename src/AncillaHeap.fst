(** Ancilla heaps with an infinite supply of unique ancillas *)
module AncillaHeap

(* Heaps of integers along with an allocator. The allocator gives
   a value greater than every previously allocated value if the
   user tries to get the min of an empty heap. Used to implement
   bit allocation & retrieval *)

open Set
open Total
open PairHeap

type AncHeapRecord = { hp:intHeap; max:int }
type cond (ah:AncHeapRecord) = 
  is_heap ah.hp /\ (forall i. (PairHeap.mem i ah.hp ==> i < ah.max))
(* Correctness is encoded in the type *)
type AncHeap = ah:AncHeapRecord{cond ah}

val emptyHeap : AncHeap
val above     : int -> Tot AncHeap
val maxUsed   : AncHeap -> Tot int
val dat       : AncHeap -> Tot intHeap
val insert    : AncHeap -> int -> Tot AncHeap
val popMin    : AncHeap -> Tot (AncHeap * int)
val getn      : AncHeap -> nat -> Tot (AncHeap * list int)
val getn_acc  : AncHeap -> (list int) -> n:nat -> Tot (AncHeap * list int) (decreases n)
val mem       : int -> AncHeap -> Tot bool

let emptyHeap = { hp = Empty; max = 0 }
let above n   = { hp = Empty; max = n }

let maxUsed ah = ah.max
let dat ah = ah.hp

let insert ah i =
  let newMax = if i < ah.max then ah.max else i + 1 in
    { hp = PairHeap.insert ah.hp i;
      max = newMax }

let popMin ah = match ah.hp with
  | Empty -> ({ ah with max = ah.max + 1 }, ah.max)
  | Heap (r, l) ->
    let hp' = deleteMin_heap ah.hp;
              mem_mergePairs l;
              deleteMin ah.hp
    in
      ({ ah with hp = hp' }, getMin ah.hp)
let rec getn_acc ah acc n = match n with
  | 0 -> (ah, acc)
  | n -> let (newah, v) = popMin ah in getn_acc newah (v::acc) (n-1)
let getn ah n = getn_acc ah [] n

let mem i ah = if i >= ah.max then true else PairHeap.mem i ah.hp

(** Verification utilities *)
val elts      : AncHeap -> Tot (set int)
val get_min    : AncHeap -> Tot int
val delete_min : AncHeap -> Tot AncHeap

let get_min ah = snd (popMin ah)
let delete_min ah = fst (popMin ah)
let elts ah = fun i -> mem i ah

(* Ancilla heaps with all zero values *)
type zeroHeap (st:state) (ah:AncHeap) = 
  forall i. (mem i ah) ==> (lookup st i = false)

val pop_is_zero : st:state -> ah:AncHeap ->
  Lemma (requires (zeroHeap st ah))
        (ensures (lookup st (snd (popMin ah)) = false)) 
  [SMTPat (lookup st (snd (popMin ah)))]
let pop_is_zero st ah = ()

val max_increasing : ah:AncHeap ->
  Lemma (requires true)
        (ensures (fst (popMin ah)).max >= ah.max)
let max_increasing ah = ()

val pop_not_elt : ah:AncHeap ->
  Lemma (not (mem (get_min ah) (delete_min ah)))
let pop_not_elt ah = match ah.hp with
  | Empty -> ()
  | Heap (r, lst) -> deleteMin_not_in_heap ah.hp

val pop_elt : ah:AncHeap ->
  Lemma (mem (get_min ah) ah)
let pop_elt ah = ()

val pop_subset : ah:AncHeap ->
  Lemma (subset (elts (delete_min ah)) (elts ah))
let pop_subset ah = match ah.hp with
  | Empty -> ()
  | Heap (r, lst) -> mem_mergePairs lst

val pop_proper_subset : ah:AncHeap ->
  Lemma (subset (elts (delete_min ah)) (elts ah) /\
         not (mem (get_min ah) (delete_min ah)))
let pop_proper_subset ah = pop_not_elt ah; pop_subset ah

val zeroHeap_subset : st:state -> ah:AncHeap -> ah':AncHeap ->
  Lemma (requires (zeroHeap st ah /\ subset (elts ah') (elts ah)))
        (ensures  (zeroHeap st ah'))
let zeroHeap_subset st ah ah' = ()

val zeroHeap_insert : st:state -> ah:AncHeap -> i:int ->
  Lemma (requires (zeroHeap st ah /\ lookup st i = false))
        (ensures  (zeroHeap st (insert ah i)))
let zeroHeap_insert st ah i = ()

val zeroHeap_insert_list : st:state -> ah:AncHeap -> lst:list int ->
  Lemma (requires (zeroHeap st ah /\ (forall i. List.mem i lst ==> lookup st i = false)))
        (ensures  (zeroHeap st (List.fold_leftT insert ah lst)))
  (decreases lst)
let rec zeroHeap_insert_list st ah lst = match lst with
  | [] -> ()
  | x::xs -> zeroHeap_insert st ah x; zeroHeap_insert_list st (insert ah x) xs

(*
type PairHeap_mem (i:int) (ah:AncHeap) =
  | Ge_max : i':int -> ah':AncHeap -> b:(i' >= ah'.max) -> PairHeap_mem i' ah'
  | Mem_heap : i':int -> ah':AncHeap -> b:b2t (Heap.mem i ah.hp) -> PairHeap_mem i' ah'
*)

val elts_insert : ah:AncHeap -> i:int ->
  Lemma (requires true)
	(ensures  (elts (insert ah i) = ins i (elts ah)))
let elts_insert ah i =
