#light "off"
module Circuit
open Prims

type l__Gate =
| RCNOT of (Prims.int * Prims.int)
| RTOFF of (Prims.int * Prims.int * Prims.int)
| RNOT of Prims.int


let is_RCNOT = (fun ( _discr_  :  l__Gate ) -> (match (_discr_) with
| RCNOT (_) -> begin
true
end
| _ -> begin
false
end))


let is_RTOFF = (fun ( _discr_  :  l__Gate ) -> (match (_discr_) with
| RTOFF (_) -> begin
true
end
| _ -> begin
false
end))


let is_RNOT = (fun ( _discr_  :  l__Gate ) -> (match (_discr_) with
| RNOT (_) -> begin
true
end
| _ -> begin
false
end))


let ___RCNOT____0 = (fun ( projectee  :  l__Gate ) -> (match (projectee) with
| RCNOT (_11_3) -> begin
_11_3
end))


let ___RTOFF____0 = (fun ( projectee  :  l__Gate ) -> (match (projectee) with
| RTOFF (_11_6) -> begin
_11_6
end))


let ___RNOT____0 = (fun ( projectee  :  l__Gate ) -> (match (projectee) with
| RNOT (_11_9) -> begin
_11_9
end))


type l__Circuit =
{gates : l__Gate Prims.list; inputs : (Prims.string * Prims.int) Prims.list; outputs : Prims.int Prims.list; ancilla : Prims.int}


let is_MkCircuit : l__Circuit  ->  Prims.bool = (Prims.checked_cast(fun ( _  :  l__Circuit ) -> (FStar.All.failwith "Not yet implemented:is_MkCircuit")))


let prettyPrintGate : l__Gate  ->  Prims.string = (fun ( gate  :  l__Gate ) -> (match (gate) with
| RCNOT (a, b) -> begin
(FStar.String.strcat "tof " (FStar.String.strcat (Prims.string_of_int a) (FStar.String.strcat " " (Prims.string_of_int b))))
end
| RTOFF (a, b, c) -> begin
(FStar.String.strcat "tof " (FStar.String.strcat (Prims.string_of_int a) (FStar.String.strcat " " (FStar.String.strcat (Prims.string_of_int b) (FStar.String.strcat " " (Prims.string_of_int c))))))
end
| RNOT (a) -> begin
(FStar.String.strcat "tof " (Prims.string_of_int a))
end))


let prettyPrintCircuit : l__Gate Prims.list  ->  Prims.string Prims.list = (FStar.List.map prettyPrintGate)


let applyGate : Total.state  ->  l__Gate  ->  Total.state = (fun ( st  :  Total.state ) ( gate  :  l__Gate ) -> (match (gate) with
| RCNOT (a, b) -> begin
(Total.update st b ((st a) <> (st b)))
end
| RTOFF (a, b, c) -> begin
(Total.update st c ((st c) <> ((st a) && (st b))))
end
| RNOT (a) -> begin
(Total.update st a (not ((st a))))
end))


let rec evalCirc : l__Gate Prims.list  ->  Total.state  ->  Total.state = (fun ( gates  :  l__Gate Prims.list ) ( st  :  Total.state ) -> (match (gates) with
| [] -> begin
st
end
| x::xs -> begin
(evalCirc xs (applyGate st x))
end))


let wfGate : l__Gate  ->  Prims.bool = (fun ( gate  :  l__Gate ) -> (match (gate) with
| RCNOT (a, b) -> begin
(not ((a = b)))
end
| RTOFF (a, b, c) -> begin
((not ((a = c))) && (not ((b = c))))
end
| RNOT (a) -> begin
true
end))


let rec wfCirc : l__Gate Prims.list  ->  Prims.bool = (fun ( circ  :  l__Gate Prims.list ) -> (match (circ) with
| [] -> begin
true
end
| x::xs -> begin
((wfGate x) && (wfCirc xs))
end))


let rec used : Prims.int  ->  l__Gate Prims.list  ->  Prims.bool = (fun ( i  :  Prims.int ) ( lst  :  l__Gate Prims.list ) -> (match (lst) with
| [] -> begin
false
end
| RCNOT (a, b)::xs -> begin
(((a = i) || (b = i)) || (used i xs))
end
| RTOFF (a, b, c)::xs -> begin
((((a = i) || (b = i)) || (c = i)) || (used i xs))
end
| RNOT (a)::xs -> begin
((a = i) || (used i xs))
end))


let uses : l__Gate Prims.list  ->  Prims.int Util.set = (fun ( lst  :  l__Gate Prims.list ) ( i  :  Prims.int ) -> (used i lst))


let rec modded : Prims.int  ->  l__Gate Prims.list  ->  Prims.bool = (fun ( i  :  Prims.int ) ( gates  :  l__Gate Prims.list ) -> (match (gates) with
| [] -> begin
false
end
| (RCNOT (_, t)::xs) | (RTOFF (_, _, t)::xs) | (RNOT (t)::xs) -> begin
((i = t) || (modded i xs))
end))


let mods : l__Gate Prims.list  ->  Prims.int Util.set = (fun ( gates  :  l__Gate Prims.list ) ( i  :  Prims.int ) -> (modded i gates))


let rec ctrl : Prims.int  ->  l__Gate Prims.list  ->  Prims.bool = (fun ( i  :  Prims.int ) ( lst  :  l__Gate Prims.list ) -> (match (lst) with
| [] -> begin
false
end
| RCNOT (a, b)::xs -> begin
((a = i) || (ctrl i xs))
end
| RTOFF (a, b, c)::xs -> begin
(((a = i) || (b = i)) || (ctrl i xs))
end
| RNOT (a)::xs -> begin
(ctrl i xs)
end))


let ctrls : l__Gate Prims.list  ->  Prims.int Util.set = (fun ( gates  :  l__Gate Prims.list ) ( i  :  Prims.int ) -> (ctrl i gates))


let rec uncompute : l__Gate Prims.list  ->  Prims.int  ->  l__Gate Prims.list = (fun ( circ  :  l__Gate Prims.list ) ( targ  :  Prims.int ) -> (match (circ) with
| [] -> begin
[]
end
| x::xs -> begin
if (used targ ((x)::[])) then begin
(uncompute xs targ)
end else begin
(x)::(uncompute xs targ)
end
end))


let rec ref_imp_use : l__Gate Prims.list  ->  Prims.unit = (fun ( gates  :  l__Gate Prims.list ) -> ())


let mods_sub_uses : l__Gate Prims.list  ->  Prims.unit = (fun ( gates  :  l__Gate Prims.list ) -> ())


let ctrls_sub_uses : l__Gate Prims.list  ->  Prims.unit = (fun ( gates  :  l__Gate Prims.list ) -> ())


let apply_mod : Total.state  ->  l__Gate  ->  Prims.unit = (fun ( st  :  Total.state ) ( x  :  l__Gate ) -> ())


let rec eval_mod : Total.state  ->  l__Gate Prims.list  ->  Prims.unit = (fun ( st  :  Total.state ) ( gates  :  l__Gate Prims.list ) -> ())


let rec evalCirc_append : l__Gate Prims.list  ->  l__Gate Prims.list  ->  Total.state  ->  Prims.unit = (fun ( l1  :  l__Gate Prims.list ) ( l2  :  l__Gate Prims.list ) ( st  :  Total.state ) -> ())


let rec use_append : Prims.int  ->  l__Gate Prims.list  ->  l__Gate Prims.list  ->  Prims.unit = (fun ( i  :  Prims.int ) ( x  :  l__Gate Prims.list ) ( y  :  l__Gate Prims.list ) -> ())


let rec uses_append : l__Gate Prims.list  ->  l__Gate Prims.list  ->  Prims.unit = (fun ( x  :  l__Gate Prims.list ) ( y  :  l__Gate Prims.list ) -> ())


let rec mod_append : Prims.int  ->  l__Gate Prims.list  ->  l__Gate Prims.list  ->  Prims.unit = (fun ( i  :  Prims.int ) ( l1  :  l__Gate Prims.list ) ( l2  :  l__Gate Prims.list ) -> ())


let rec mods_append : l__Gate Prims.list  ->  l__Gate Prims.list  ->  Prims.unit = (fun ( x  :  l__Gate Prims.list ) ( y  :  l__Gate Prims.list ) -> ())


let rec ctrl_append : Prims.int  ->  l__Gate Prims.list  ->  l__Gate Prims.list  ->  Prims.unit = (fun ( i  :  Prims.int ) ( x  :  l__Gate Prims.list ) ( y  :  l__Gate Prims.list ) -> ())


let rec ctrls_append : l__Gate Prims.list  ->  l__Gate Prims.list  ->  Prims.unit = (fun ( x  :  l__Gate Prims.list ) ( y  :  l__Gate Prims.list ) -> ())


let rec wf_append : l__Gate Prims.list  ->  l__Gate Prims.list  ->  Prims.unit = (fun ( x  :  l__Gate Prims.list ) ( y  :  l__Gate Prims.list ) -> ())


let rec rev_uses : l__Gate Prims.list  ->  Prims.unit = (fun ( circ  :  l__Gate Prims.list ) -> ())


let rec rev_mods : l__Gate Prims.list  ->  Prims.unit = (fun ( circ  :  l__Gate Prims.list ) -> ())


let rec rev_ctrls : l__Gate Prims.list  ->  Prims.unit = (fun ( circ  :  l__Gate Prims.list ) -> ())


let evalCirc_append_rev : l__Gate Prims.list  ->  l__Gate Prims.list  ->  Total.state  ->  Prims.unit = (fun ( x  :  l__Gate Prims.list ) ( y  :  l__Gate Prims.list ) ( st  :  Total.state ) -> ())


let rev_gate : l__Gate  ->  Total.state  ->  Prims.unit = (fun ( gate  :  l__Gate ) ( st  :  Total.state ) -> ())


let rec rev_inverse : l__Gate Prims.list  ->  Total.state  ->  Prims.unit = (fun ( circ  :  l__Gate Prims.list ) ( st  :  Total.state ) -> ())


let applyGate_state_swap : l__Gate  ->  Total.state  ->  Total.state  ->  Prims.int Util.set  ->  Prims.unit = (fun ( x  :  l__Gate ) ( st  :  Total.state ) ( st'  :  Total.state ) ( dom  :  Prims.int Util.set ) -> ())


let rec evalCirc_state_swap : l__Gate Prims.list  ->  Total.state  ->  Total.state  ->  Prims.int Util.set  ->  Prims.unit = (fun ( circ  :  l__Gate Prims.list ) ( st  :  Total.state ) ( st'  :  Total.state ) ( dom  :  Prims.int Util.set ) -> ())


let bennett : l__Gate Prims.list  ->  l__Gate Prims.list  ->  Total.state  ->  Prims.unit = (fun ( comp  :  l__Gate Prims.list ) ( copy  :  l__Gate Prims.list ) ( st  :  Total.state ) -> ())


let rec uncompute_targ : l__Gate Prims.list  ->  Prims.int  ->  Prims.unit = (fun ( circ  :  l__Gate Prims.list ) ( targ  :  Prims.int ) -> ())


let rec uncompute_wf : l__Gate Prims.list  ->  Prims.int  ->  Prims.unit = (fun ( circ  :  l__Gate Prims.list ) ( targ  :  Prims.int ) -> ())


let rec uncompute_uses_subset : l__Gate Prims.list  ->  Prims.int  ->  Prims.unit = (fun ( circ  :  l__Gate Prims.list ) ( targ  :  Prims.int ) -> ())


let rec uncompute_ctrls_subset : l__Gate Prims.list  ->  Prims.int  ->  Prims.unit = (fun ( circ  :  l__Gate Prims.list ) ( targ  :  Prims.int ) -> ())


let rec uncompute_agree : l__Gate Prims.list  ->  Prims.int  ->  Total.state  ->  Prims.unit = (fun ( circ  :  l__Gate Prims.list ) ( targ  :  Prims.int ) ( st  :  Total.state ) -> ())


let uncompute_mixed_inverse : l__Gate Prims.list  ->  Prims.int  ->  Total.state  ->  Prims.unit = (fun ( circ  :  l__Gate Prims.list ) ( targ  :  Prims.int ) ( st  :  Total.state ) -> ())




