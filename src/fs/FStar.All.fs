#light "off"
module FStar.All
open Prims

let pipe_right = (fun ( _  :  'a ) ( _  :  'a  ->  'b ) -> (failwith "Not yet implemented:pipe_right"))


let pipe_left = (fun ( _  :  'a  ->  'b ) ( _  :  'a ) -> (failwith "Not yet implemented:pipe_left"))


let failwith = (fun ( _  :  Prims.string ) -> (failwith "Not yet implemented:failwith"))


let exit = (fun ( _  :  Prims.int ) -> (failwith "Not yet implemented:exit"))


let try_with = (fun ( _  :  Prims.unit  ->  'a ) ( _  :  Prims.exn  ->  'a ) -> (failwith "Not yet implemented:try_with"))


let op_Less_Less = (fun ( _  :  'b  ->  'c ) ( _  :  'a  ->  'b ) ( _  :  'a ) -> (failwith "Not yet implemented:op_Less_Less"))


let op_Greater_Greater = (fun ( _  :  'a  ->  'b ) ( _  :  'b  ->  'c ) ( _  :  'a ) -> (failwith "Not yet implemented:op_Greater_Greater"))




