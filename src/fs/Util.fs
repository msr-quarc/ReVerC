#light "off"
module Util
open Prims

type 'An fin =
Prims.nat


type 'Aa set =
'Aa  ->  Prims.bool


let mem = (fun ( i  :  'Aa ) ( s  :  'Aa set ) -> (s i))


let empty = (fun ( _12_13  :  'Aa ) -> false)


let singleton = (fun ( a  :  'Aa ) ( b  :  'Aa ) -> (b = a))


let union = (fun ( a  :  'Aa set ) ( b  :  'Aa set ) ( c  :  'Aa ) -> ((a c) || (b c)))


let intersection = (fun ( a  :  'Aa set ) ( b  :  'Aa set ) ( c  :  'Aa ) -> ((a c) && (b c)))


let complement = (fun ( s  :  'Aa set ) ( x  :  'Aa ) -> (not ((s x))))


let ins = (fun ( a  :  'Aa ) ( b  :  'Aa set ) -> (union (singleton a) b))


type ('Aa, 'As1, 'As2) l__Equal =
('Aa, Prims.bool, Prims.unit, Prims.unit) FStar.FunctionalExtensionality.l__FEq


let lemma_equal_intro = (fun ( s1  :  'Aa set ) ( s2  :  'Aa set ) -> ())


let lemma_equal_elim = (fun ( s1  :  'Aa set ) ( s2  :  'Aa set ) -> ())


let lemma_equal_refl = (fun ( s1  :  'Aa set ) ( s2  :  'Aa set ) -> ())


let subset_trans = (fun ( s  :  'Aa set ) ( s'  :  'Aa set ) ( s''  :  'Aa set ) -> ())


let subset_ins = (fun ( i  :  'Aa ) ( s  :  'Aa set ) -> ())


let ins_subset_pres = (fun ( i  :  'Aa ) ( s  :  'Aa set ) ( s'  :  'Aa set ) -> ())


let disjoint_subset = (fun ( s  :  'Aa set ) ( s'  :  'Aa set ) ( s''  :  'Aa set ) -> ())


let disjoint_union = (fun ( s  :  'Aa set ) ( s'  :  'Aa set ) ( s''  :  'Aa set ) -> ())


type 'a result =
| Val of 'a
| Err of Prims.string


let is_Val = (fun ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Val (_) -> begin
true
end
| _ -> begin
false
end))


let is_Err = (fun ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))


let ___Val____0 = (fun ( projectee  :  'a result ) -> (match (projectee) with
| Val (_12_90) -> begin
_12_90
end))


let ___Err____0 = (fun ( projectee  :  'a result ) -> (match (projectee) with
| Err (_12_93) -> begin
_12_93
end))


let get_Val = (fun ( r  :  'a result ) -> (match (r) with
| Val (v) -> begin
v
end))


let bind = (fun ( v  :  'a result ) ( f  :  'a  ->  'b result ) -> (match (v) with
| Val (x) -> begin
(f x)
end
| Err (s) -> begin
Err (s)
end))


let bindT = (fun ( v  :  'a result ) ( f  :  'a  ->  'b result ) -> (match (v) with
| Val (x) -> begin
(f x)
end
| Err (s) -> begin
Err (s)
end))


let rec foldM = (fun ( f  :  'a  ->  'b  ->  'a result ) ( a  :  'a ) ( lst  :  'b Prims.list ) -> (match (lst) with
| [] -> begin
Val (a)
end
| x::xs -> begin
(bind (f a x) (fun ( res  :  'a ) -> (foldM f res xs)))
end))


let mems = (fun ( l  :  'Aa Prims.list ) ( i  :  'Aa ) -> (FStar.List.mem i l))


let rec nthT = (fun ( l  :  'a Prims.list ) ( i  :  Prims.int ) -> (match (l) with
| x::xs -> begin
if (i = (Prims.parse_int "0")) then begin
x
end else begin
(nthT xs (i - (Prims.parse_int "1")))
end
end))


let rec for_someT = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
false
end
| hd::tl -> begin
if (f hd) then begin
true
end else begin
(for_someT f tl)
end
end))


let rec take = (fun ( l  :  'a Prims.list ) ( i  :  Prims.int ) -> if (i <= (Prims.parse_int "0")) then begin
[]
end else begin
(match (l) with
| x::xs -> begin
(x)::(take xs (i - (Prims.parse_int "1")))
end)
end)


let rec remove = (fun ( l  :  'a Prims.list ) ( i  :  Prims.nat ) -> if (i = (Prims.parse_int "0")) then begin
l
end else begin
(match (l) with
| _12_164::xs -> begin
(remove xs (i - (Prims.parse_int "1")))
end)
end)


let rec rotate_rec = (fun ( acc  :  'a Prims.list ) ( l  :  'a Prims.list ) ( i  :  Prims.nat ) -> if (i = (Prims.parse_int "0")) then begin
(FStar.List.append acc (FStar.List.rev l))
end else begin
(match (l) with
| x::xs -> begin
(rotate_rec ((x)::acc) xs (i - (Prims.parse_int "1")))
end)
end)


let rotate = (fun ( l  :  'a Prims.list ) ( i  :  Prims.nat ) -> (

let _12_183 = ()
in (rotate_rec [] (FStar.List.rev l) i)))


let slice = (fun ( l  :  'a Prims.list ) ( i  :  Prims.nat ) ( j  :  Prims.nat ) -> (take (remove l i) ((j - i) + (Prims.parse_int "1"))))


let rec of_int : Prims.nat  ->  Prims.int  ->  Prims.bool Prims.list = (fun ( i  :  Prims.nat ) ( j  :  Prims.int ) -> if (j <= (Prims.parse_int "0")) then begin
[]
end else begin
(((i % (Prims.parse_int "2")) = (Prims.parse_int "1")))::(of_int (i / (Prims.parse_int "2")) (j - (Prims.parse_int "1")))
end)




