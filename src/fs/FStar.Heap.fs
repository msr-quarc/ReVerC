#light "off"
module FStar.Heap
open Prims

type heap =
Prims.unit


type 'A_ ref =
Prims.unit


type aref =
| Ref of Prims.unit * obj ref


let is_Ref = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| Ref (_) -> begin
true
end
| _ -> begin
false
end))


let ___Ref___r = (fun ( projectee  :  aref ) -> (Prims.checked_cast(match (projectee) with
| Ref (_, _3_4) -> begin
_3_4
end)))


let sel = (Prims.checked_cast(fun ( _  :  heap ) ( _  :  'Aa ref ) -> (FStar.All.failwith "Not yet implemented:sel")))


let upd = (Prims.checked_cast(fun ( _  :  heap ) ( _  :  'Aa ref ) ( _  :  'Aa ) -> (FStar.All.failwith "Not yet implemented:upd")))


let emp : heap = (FStar.All.failwith "Not yet implemented:emp")


let contains = (Prims.checked_cast(fun ( _  :  heap ) ( _  :  'Aa ref ) -> (FStar.All.failwith "Not yet implemented:contains")))


let equal : heap  ->  heap  ->  Prims.bool = (Prims.checked_cast(fun ( _  :  heap ) ( _  :  heap ) -> (FStar.All.failwith "Not yet implemented:equal")))


let restrict : heap  ->  aref FStar.Set.set  ->  heap = (Prims.checked_cast(fun ( _  :  heap ) ( _  :  aref FStar.Set.set ) -> (FStar.All.failwith "Not yet implemented:restrict")))


let concat : heap  ->  heap  ->  heap = (Prims.checked_cast(fun ( _  :  heap ) ( _  :  heap ) -> (FStar.All.failwith "Not yet implemented:concat")))


type ('Ar, 'Ap, 'Ah) l__On =
'Ap


let only = (fun ( x  :  'A_3_2055 ref ) -> (FStar.Set.singleton (Ref ((), (Prims.checked_castx)))))


let op_Hat_Plus_Plus = (fun ( r  :  'Aa ref ) ( s  :  aref FStar.Set.set ) -> (FStar.Set.union (FStar.Set.singleton (Ref ((), (Prims.checked_castr)))) s))


let op_Plus_Plus_Hat = (fun ( s  :  aref FStar.Set.set ) ( r  :  'Aa ref ) -> (FStar.Set.union s (FStar.Set.singleton (Ref ((), (Prims.checked_castr))))))


let op_Hat_Plus_Hat = (fun ( r1  :  'Aa ref ) ( r2  :  'Ab ref ) -> (FStar.Set.union (FStar.Set.singleton (Ref ((), (Prims.checked_castr1)))) (FStar.Set.singleton (Ref ((), (Prims.checked_castr2))))))




