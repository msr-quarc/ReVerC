#light "off"
module PairHeap
open Prims

type 'a heap =
| Empty
| Heap of ('a * 'a heap Prims.list)


let is_Empty = (fun ( _discr_  :  'a heap ) -> (match (_discr_) with
| Empty (_) -> begin
true
end
| _ -> begin
false
end))


let is_Heap = (fun ( _discr_  :  'a heap ) -> (match (_discr_) with
| Heap (_) -> begin
true
end
| _ -> begin
false
end))


let ___Heap____0 = (fun ( projectee  :  'a heap ) -> (match (projectee) with
| Heap (_12_4) -> begin
_12_4
end))


type intHeap =
Prims.int heap


let subheaps : intHeap  ->  intHeap Prims.list = (fun ( hp  :  intHeap ) -> (match (hp) with
| Heap (r, lst) -> begin
lst
end))


let merge : intHeap  ->  intHeap  ->  intHeap = (fun ( hp1  :  intHeap ) ( hp2  :  intHeap ) -> (match ((hp1, hp2)) with
| (Empty, _12_16) -> begin
hp2
end
| (_12_19, Empty) -> begin
hp1
end
| (Heap (r1, h1), Heap (r2, h2)) -> begin
if (r1 = r2) then begin
Heap ((r1, (FStar.List.append h2 h1)))
end else begin
if (r1 < r2) then begin
Heap ((r1, (hp2)::h1))
end else begin
Heap ((r2, (hp1)::h2))
end
end
end))


let insert : intHeap  ->  Prims.int  ->  intHeap = (fun ( hp  :  intHeap ) ( i  :  Prims.int ) -> (merge hp (Heap ((i, [])))))


let rec mergePairs : intHeap Prims.list  ->  intHeap = (fun ( hplst  :  intHeap Prims.list ) -> (match (hplst) with
| [] -> begin
Empty
end
| x::[] -> begin
x
end
| x::y::xs -> begin
(merge (merge x y) (mergePairs xs))
end))


let deleteMin : intHeap  ->  intHeap = (fun ( hp  :  intHeap ) -> (match (hp) with
| Heap (_12_47, lst) -> begin
(mergePairs lst)
end))


let getMin : intHeap  ->  Prims.int = (fun ( hp  :  intHeap ) -> (match (hp) with
| Heap (r, _12_56) -> begin
r
end))


let rec mem : Prims.int  ->  intHeap  ->  Prims.bool = (fun ( i  :  Prims.int ) ( hp  :  intHeap ) -> (match (hp) with
| Empty -> begin
false
end
| Heap (r, lst) -> begin
((i = r) || (mem_lst i lst))
end))
and mem_lst : Prims.int  ->  intHeap Prims.list  ->  Prims.bool = (fun ( i  :  Prims.int ) ( lst  :  intHeap Prims.list ) -> (match (lst) with
| [] -> begin
false
end
| x::xs -> begin
((mem i x) || (mem_lst i xs))
end))


let elts : intHeap  ->  Prims.int Util.set = (fun ( hp  :  intHeap ) ( i  :  Prims.int ) -> (mem i hp))


let leq_heap : Prims.int  ->  intHeap  ->  Prims.bool = (fun ( i  :  Prims.int ) ( hp  :  intHeap ) -> (match (hp) with
| Empty -> begin
true
end
| Heap (j, _12_83) -> begin
(i < j)
end))


let rec is_heap : intHeap  ->  Prims.bool = (fun ( hp  :  intHeap ) -> (match (hp) with
| Empty -> begin
true
end
| Heap (i, lst) -> begin
((is_heap_list lst) && (FStar.List.for_all (leq_heap i) lst))
end))
and is_heap_list : intHeap Prims.list  ->  Prims.bool = (fun ( lst  :  intHeap Prims.list ) -> (match (lst) with
| [] -> begin
true
end
| x::xs -> begin
((is_heap x) && (is_heap_list xs))
end))


let rec is_heap_app : intHeap Prims.list  ->  intHeap Prims.list  ->  Prims.unit = (fun ( l1  :  intHeap Prims.list ) ( l2  :  intHeap Prims.list ) -> ())


let rec leq_heap_trans : Prims.int  ->  Prims.int  ->  intHeap Prims.list  ->  Prims.unit = (fun ( i  :  Prims.int ) ( j  :  Prims.int ) ( l  :  intHeap Prims.list ) -> ())


let rec leq_heap_app : Prims.int  ->  intHeap Prims.list  ->  intHeap Prims.list  ->  Prims.unit = (fun ( i  :  Prims.int ) ( l1  :  intHeap Prims.list ) ( l2  :  intHeap Prims.list ) -> ())


let swap_root : intHeap  ->  Prims.int  ->  intHeap = (fun ( h  :  intHeap ) ( i  :  Prims.int ) -> (match (h) with
| Heap (r, lst) -> begin
Heap ((i, lst))
end))


let merge_heap : intHeap  ->  intHeap  ->  Prims.unit = (fun ( hp1  :  intHeap ) ( hp2  :  intHeap ) -> ())


let insert_heap : intHeap  ->  Prims.int  ->  Prims.unit = (fun ( _12_166  :  intHeap ) ( _12_168  :  Prims.int ) -> ())


let rec mergePairs_heap : intHeap Prims.list  ->  Prims.unit = (fun ( lst  :  intHeap Prims.list ) -> ())


let deleteMin_heap : intHeap  ->  Prims.unit = (fun ( hp  :  intHeap ) -> ())


let leq_tree_trans : Prims.int  ->  Prims.int  ->  Prims.unit = (fun ( i  :  Prims.int ) ( j  :  Prims.int ) -> ())


let leq_all_trans : Prims.int  ->  Prims.int  ->  intHeap  ->  Prims.unit = (fun ( i  :  Prims.int ) ( j  :  Prims.int ) ( hp  :  intHeap ) -> ())


let rec mem_app : intHeap Prims.list  ->  intHeap Prims.list  ->  Prims.unit = (fun ( l1  :  intHeap Prims.list ) ( l2  :  intHeap Prims.list ) -> ())


let mem_merge : intHeap  ->  intHeap  ->  Prims.unit = (fun ( h1  :  intHeap ) ( h2  :  intHeap ) -> ())


let rec mem_mergePairs : intHeap Prims.list  ->  Prims.unit = (fun ( l  :  intHeap Prims.list ) -> ())


let mem_insert : intHeap  ->  Prims.int  ->  Prims.unit = (fun ( h  :  intHeap ) ( i  :  Prims.int ) -> ())


let rec leq_is_min : Prims.int  ->  intHeap  ->  Prims.unit = (fun ( i  :  Prims.int ) ( h  :  intHeap ) -> ())
and leq_is_min_list : Prims.int  ->  intHeap Prims.list  ->  Prims.unit = (fun ( i  :  Prims.int ) ( l  :  intHeap Prims.list ) -> ())


let deleteMin_not_in_heap : intHeap  ->  Prims.unit = (fun ( h  :  intHeap ) -> ())




