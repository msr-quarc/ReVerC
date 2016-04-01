#light "off"
module AncillaHeap
open Prims

type l__AncHeapRecord =
{hp : PairHeap.intHeap; max : Prims.int}


let is_MkAncHeapRecord : l__AncHeapRecord  ->  Prims.bool = (Prims.checked_cast(fun ( _  :  l__AncHeapRecord ) -> (FStar.All.failwith "Not yet implemented:is_MkAncHeapRecord")))


type l__AncHeap =
l__AncHeapRecord


let emptyHeap : l__AncHeap = {hp = PairHeap.Empty; max = (Prims.parse_int "0")}


let above : Prims.int  ->  l__AncHeap = (fun ( n  :  Prims.int ) -> {hp = PairHeap.Empty; max = n})


let maxUsed : l__AncHeap  ->  Prims.int = (fun ( ah  :  l__AncHeap ) -> ah.max)


let dat : l__AncHeap  ->  PairHeap.intHeap = (fun ( ah  :  l__AncHeap ) -> ah.hp)


let insert : l__AncHeap  ->  Prims.int  ->  l__AncHeap = (fun ( ah  :  l__AncHeap ) ( i  :  Prims.int ) -> (

let newMax = if (i < ah.max) then begin
ah.max
end else begin
(i + (Prims.parse_int "1"))
end
in {hp = (PairHeap.insert ah.hp i); max = newMax}))


let popMin : l__AncHeap  ->  (l__AncHeap * Prims.int) = (fun ( ah  :  l__AncHeap ) -> (match (ah.hp) with
| PairHeap.Empty -> begin
((

let _13_16 = ah
in {hp = _13_16.hp; max = (ah.max + (Prims.parse_int "1"))}), ah.max)
end
| PairHeap.Heap (r, l) -> begin
(

let hp' = (

let _13_22 = ()
in (

let _13_24 = ()
in (PairHeap.deleteMin ah.hp)))
in ((

let _13_27 = ah
in {hp = hp'; max = _13_27.max}), (PairHeap.getMin ah.hp)))
end))


let rec getn_acc : l__AncHeap  ->  Prims.int Prims.list  ->  Prims.nat  ->  (l__AncHeap * Prims.int Prims.list) = (fun ( ah  :  l__AncHeap ) ( acc  :  Prims.int Prims.list ) ( n  :  Prims.nat ) -> (match (n) with
| _35_32 when (_35_32 = (Prims.parse_int "0")) -> begin
(ah, acc)
end
| n -> begin
(

let _13_36 = (popMin ah)
in (match (_13_36) with
| (newah, v) -> begin
(getn_acc newah ((v)::acc) (n - (Prims.parse_int "1")))
end))
end))


let getn : l__AncHeap  ->  Prims.nat  ->  (l__AncHeap * Prims.int Prims.list) = (fun ( ah  :  l__AncHeap ) ( n  :  Prims.nat ) -> (getn_acc ah [] n))


let mem : Prims.int  ->  l__AncHeap  ->  Prims.bool = (fun ( i  :  Prims.int ) ( ah  :  l__AncHeap ) -> if (i >= ah.max) then begin
true
end else begin
(PairHeap.mem i ah.hp)
end)


let elts : l__AncHeap  ->  Prims.int Util.set = (fun ( ah  :  l__AncHeap ) ( i  :  Prims.int ) -> (mem i ah))


let get_min : l__AncHeap  ->  Prims.int = (fun ( ah  :  l__AncHeap ) -> (Prims.snd (popMin ah)))


let delete_min : l__AncHeap  ->  l__AncHeap = (fun ( ah  :  l__AncHeap ) -> (Prims.fst (popMin ah)))


let pop_is_zero : Total.state  ->  l__AncHeap  ->  Prims.unit = (fun ( st  :  Total.state ) ( ah  :  l__AncHeap ) -> ())


let max_increasing : l__AncHeap  ->  Prims.unit = (fun ( ah  :  l__AncHeap ) -> ())


let pop_not_elt : l__AncHeap  ->  Prims.unit = (fun ( ah  :  l__AncHeap ) -> ())


let pop_elt : l__AncHeap  ->  Prims.unit = (fun ( ah  :  l__AncHeap ) -> ())


let pop_subset : l__AncHeap  ->  Prims.unit = (fun ( ah  :  l__AncHeap ) -> ())


let pop_proper_subset : l__AncHeap  ->  Prims.unit = (fun ( ah  :  l__AncHeap ) -> ())


let zeroHeap_subset : Total.state  ->  l__AncHeap  ->  l__AncHeap  ->  Prims.unit = (fun ( st  :  Total.state ) ( ah  :  l__AncHeap ) ( ah'  :  l__AncHeap ) -> ())


let zeroHeap_insert : Total.state  ->  l__AncHeap  ->  Prims.int  ->  Prims.unit = (fun ( st  :  Total.state ) ( ah  :  l__AncHeap ) ( i  :  Prims.int ) -> ())


let rec zeroHeap_insert_list : Total.state  ->  l__AncHeap  ->  Prims.int Prims.list  ->  Prims.unit = (fun ( st  :  Total.state ) ( ah  :  l__AncHeap ) ( lst  :  Prims.int Prims.list ) -> ())




