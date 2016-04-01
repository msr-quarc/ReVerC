module PairHeap

open Util

// Pairing heaps with no duplicate elements
type heap<'a> =
  | Empty
  | Heap of 'a * list<heap<'a>>
type intHeap = heap<int>

//val subheaps : hp:intHeap{~(is_Empty hp)} -> Tot (list intHeap)
let subheaps hp = match hp with
  | Heap (r, lst) -> lst

//val merge : intHeap -> intHeap -> Tot intHeap
let merge hp1 hp2 = match (hp1, hp2) with
  | (Empty, _) -> hp2
  | (_, Empty) -> hp1
  | (Heap (r1, h1), Heap (r2, h2)) ->
    if r1 = r2 then      Heap (r1, (h2@h1))
    else if r1 < r2 then Heap (r1, (hp2::h1))
    else                 Heap (r2, (hp1::h2))

//val insert : intHeap -> int -> Tot intHeap
let insert hp i = merge hp (Heap (i, []))

//val mergePairs : list intHeap -> Tot intHeap
let rec mergePairs hplst = match hplst with
  | [] -> Empty
  | x::[] -> x
  | x::y::xs -> merge (merge x y) (mergePairs xs)

//val deleteMin : hp:intHeap{~(is_Empty hp)} -> Tot intHeap
let deleteMin hp = match hp with
  | Heap (_, lst) -> mergePairs lst

//val getMin : hp:intHeap{~(is_Empty hp)} -> Tot int
let getMin hp = match hp with
  | Heap (r, _) -> r

//val mem : int -> hp:intHeap -> Tot bool (decreases %[hp;1])
//val mem_lst : int -> l:(list intHeap) -> Tot bool (decreases %[l;0])
let rec mem i hp = match hp with
  | Empty -> false
  | Heap (r, lst) -> i = r || mem_lst i lst
and mem_lst i lst = match lst with
  | [] -> false
  | x::xs -> mem i x || mem_lst i xs

//val elts : intHeap -> Tot (set int)
let elts hp = fun i -> mem i hp
