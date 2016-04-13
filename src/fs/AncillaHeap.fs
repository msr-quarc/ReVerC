(** Ancilla heaps with an infinite supply of unique ancillas *)
module AncillaHeap

(* Heaps of integers along with an allocator. The allocator gives
   a value greater than every previously allocated value if the
   user tries to get the min of an empty heap. Used to implement
   bit allocation & retrieval *)

open Total
open PairHeap

type AncHeapRecord = { hp:intHeap; max:int }
type AncHeap = AncHeapRecord

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
    let hp' = deleteMin ah.hp in
      ({ ah with hp = hp' }, getMin ah.hp)
let rec getn_acc ah acc n = match n with
  | 0 -> (ah, acc)
  | n -> let (newah, v) = popMin ah in getn_acc newah (v::acc) (n-1)
let getn ah n = getn_acc ah [] n

let mem i ah = if i >= ah.max then true else PairHeap.mem i ah.hp

