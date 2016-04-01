#light "off"
module FStar.Util
open Prims

let op_Plus_Plus = (fun ( x  :  'A_18_42 FStar.Set.set ) ( y  :  'A_18_42 FStar.Set.set ) -> (FStar.Set.union x y))


let op_Plus_Plus_Hat = (fun ( x  :  'A_18_88 FStar.Set.set ) ( y  :  'A_18_88 ) -> (op_Plus_Plus x (FStar.Set.singleton y)))


let op_Hat_Plus_Hat = (fun ( x  :  'A_18_158 ) ( y  :  'A_18_158 ) -> (op_Plus_Plus (FStar.Set.singleton x) (FStar.Set.singleton y)))


let op_At_Plus_At = (fun ( r  :  FStar.HyperHeap.rid ) ( b  :  Prims.unit ) ( s  :  FStar.HyperHeap.rid ) ( x  :  (Prims.unit, 'Aa) FStar.HyperHeap.rref ) ( y  :  (Prims.unit, obj) FStar.HyperHeap.rref ) -> (Prims.checked_cast()))


let op_Plus_Plus_At = (fun ( r  :  FStar.HyperHeap.rid ) ( x  :  FStar.Heap.aref FStar.Set.set ) ( y  :  (Prims.unit, 'Aa) FStar.HyperHeap.rref ) -> (Prims.checked_cast()))




