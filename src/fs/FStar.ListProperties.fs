#light "off"
module FStar.ListProperties
open Prims

let mem_empty = (fun ( x  :  'a ) -> ())


let rec rev_acc_length = (fun ( l  :  'a Prims.list ) ( acc  :  'a Prims.list ) -> ())


let rev_length = (fun ( l  :  'a Prims.list ) -> ())


let rec rev_acc_mem = (fun ( l  :  'a Prims.list ) ( acc  :  'a Prims.list ) ( x  :  'a ) -> ())


let rev_mem = (fun ( l  :  'a Prims.list ) ( x  :  'a ) -> ())


let append_nil_l = (fun ( l  :  'a Prims.list ) -> ())


let rec append_l_nil = (fun ( _7_1  :  'a Prims.list ) -> ())


let append_cons_l = (fun ( hd  :  'a ) ( tl  :  'a Prims.list ) ( l  :  'a Prims.list ) -> ())


let rec append_l_cons = (fun ( hd  :  'a ) ( tl  :  'a Prims.list ) ( l  :  'a Prims.list ) -> ())


let rec append_assoc = (fun ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) ( l3  :  'a Prims.list ) -> ())


let rec append_length = (fun ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) -> ())


let rec append_mem = (fun ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) ( a  :  'a ) -> ())


let rec append_mem_forall = (fun ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) -> ())


let rec append_count = (fun ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) ( a  :  'a ) -> ())


let rec append_count_forall = (fun ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) -> ())


let append_eq_nil = (fun ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) -> ())


let append_eq_singl = (fun ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) ( x  :  'a ) -> ())


let rec append_inv_head = (fun ( l  :  'a Prims.list ) ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) -> ())


let rec append_inv_tail = (fun ( l  :  'a Prims.list ) ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) -> ())


let rec rev' = (fun ( _7_2  :  'a Prims.list ) -> (match (_7_2) with
| [] -> begin
[]
end
| hd::tl -> begin
(FStar.List.append (rev' tl) ((hd)::[]))
end))


let rev'T = rev'


let rec rev_acc_rev' = (fun ( l  :  'a Prims.list ) ( acc  :  'a Prims.list ) -> ())


let rev_rev' = (fun ( l  :  'a Prims.list ) -> ())


let rec rev'_append = (fun ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) -> ())


let rev_append = (fun ( l1  :  'a Prims.list ) ( l2  :  'a Prims.list ) -> ())


let rec rev'_involutive = (fun ( _7_3  :  'a Prims.list ) -> ())


let rev_involutive = (fun ( l  :  'a Prims.list ) -> ())


let rec rev'_list_ind = (fun ( p  :  'a Prims.list  ->  Prims.bool ) ( _7_4  :  'a Prims.list ) -> ())


let rev_ind = (fun ( p  :  'a Prims.list  ->  Prims.bool ) ( l  :  'a Prims.list ) -> ())


let rec mapT_lemma = (fun ( f  :  'a  ->  'b ) ( l  :  'a Prims.list ) -> ())


let partition_length = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> ())


let rec partition_mem = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) ( x  :  'a ) -> ())


let rec partition_mem_forall = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> ())


let rec partition_mem_p_forall = (fun ( p  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> ())


let rec partition_count = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) ( x  :  'a ) -> ())


let rec partition_count_forall = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> ())


let rec sortWithT_permutation = (fun ( f  :  'a  ->  'a  ->  Prims.int ) ( l  :  'a Prims.list ) -> ())


let rec sorted = (fun ( f  :  'a  ->  'a  ->  Prims.bool ) ( _7_5  :  'a Prims.list ) -> (match (_7_5) with
| ([]) | (_::[]) -> begin
true
end
| x::y::tl -> begin
((f x y) && (sorted f ((y)::tl)))
end))


let rec append_sorted = (fun ( f  :  'Aa  ->  'Aa  ->  Prims.bool ) ( l1  :  'Aa Prims.list ) ( l2  :  'Aa Prims.list ) ( pivot  :  'Aa ) -> ())


let rec sortWithT_sorted = (fun ( f  :  'Aa  ->  'Aa  ->  Prims.int ) ( l  :  'Aa Prims.list ) -> ())




