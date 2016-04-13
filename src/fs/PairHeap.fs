(** Pairing heaps *)
module PairHeap

(* An implementation of pairing heaps (see wikipedia). 
   There are no duplicates allowed, and proven properties include 
   that all operations preserve the heap property (get min is the min). 
   Note that the is_heap property isn't this exactly -- is_heap means 
   the root is less than the root of each subheap. It is later proven 
   that this property implies the actual heap property. *)

type heap<'a> =
  | Empty
  | Heap of 'a * list<heap<'a> >
type intHeap = heap<int>

let subheaps hp = match hp with
  | Heap (r, lst) -> lst

let merge hp1 hp2 = match (hp1, hp2) with
  | (Empty, _) -> hp2
  | (_, Empty) -> hp1
  | (Heap (r1, h1), Heap (r2, h2)) ->
    if r1 = r2 then      Heap (r1, (h2@h1))
    else if r1 < r2 then Heap (r1, (hp2::h1))
    else                 Heap (r2, (hp1::h2))

let insert hp i = merge hp (Heap (i, []))

let rec mergePairs hplst = match hplst with
  | [] -> Empty
  | x::[] -> x
  | x::y::xs -> merge (merge x y) (mergePairs xs)

let deleteMin hp = match hp with
  | Heap (_, lst) -> mergePairs lst

let getMin hp = match hp with
  | Heap (r, _) -> r

let rec mem i hp = match hp with
  | Empty -> false
  | Heap (r, lst) -> i = r || mem_lst i lst
and mem_lst i lst = match lst with
  | [] -> false
  | x::xs -> mem i x || mem_lst i xs

let elts hp = fun i -> mem i hp

