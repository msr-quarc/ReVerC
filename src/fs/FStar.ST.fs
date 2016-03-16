#light "off"
module FStar.ST
open Prims

type 'Aa ref =
'Aa FStar.Heap.ref


let recall = (fun ( r  :  'Aa ref ) -> (FStar.All.failwith "Not yet implemented:recall"))


let alloc = (fun ( init  :  'Aa ) -> (FStar.All.failwith "Not yet implemented:alloc"))


let read = (fun ( r  :  'Aa ref ) -> (FStar.All.failwith "Not yet implemented:read"))


let write = (fun ( r  :  'Aa ref ) ( v  :  'Aa ) -> (FStar.All.failwith "Not yet implemented:write"))


let op_Colon_Equals = (fun ( r  :  'Aa ref ) ( v  :  'Aa ) -> (FStar.All.failwith "Not yet implemented:op_Colon_Equals"))


let get : Prims.unit  ->  FStar.Heap.heap = (fun ( _  :  Prims.unit ) -> (FStar.All.failwith "Not yet implemented:get"))




