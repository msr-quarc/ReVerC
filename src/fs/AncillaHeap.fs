module AncillaHeap
open Util
open PairHeap
open Maps.Total

// (Effectively) infinite sets of address

type AncHeap = { hp:intHeap; max:int }

//val emptyHeap : AncHeap
//val above : int -> Tot AncHeap

//val maxUsed   : AncHeap -> Tot int
//val dat       : AncHeap -> Tot intHeap
//val insert    : AncHeap -> int -> Tot AncHeap
//val popMin    : AncHeap -> Tot (AncHeap * int)
//val getn      : AncHeap -> nat -> Tot (AncHeap * list int)
//val getn_acc  : AncHeap -> (list int) -> n:nat -> Tot (AncHeap * list int) (decreases n)
//val mem       : int -> AncHeap -> Tot bool
//val elts      : AncHeap -> Tot (set int)

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
let elts ah = fun i -> mem i ah

