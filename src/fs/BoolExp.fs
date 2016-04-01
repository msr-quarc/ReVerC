#light "off"
module BoolExp
open Prims

type l__BoolExp =
| BFalse
| BVar of Prims.int
| BNot of l__BoolExp
| BAnd of (l__BoolExp * l__BoolExp)
| BXor of (l__BoolExp * l__BoolExp)


let is_BFalse = (fun ( _discr_  :  l__BoolExp ) -> (match (_discr_) with
| BFalse (_) -> begin
true
end
| _ -> begin
false
end))


let is_BVar = (fun ( _discr_  :  l__BoolExp ) -> (match (_discr_) with
| BVar (_) -> begin
true
end
| _ -> begin
false
end))


let is_BNot = (fun ( _discr_  :  l__BoolExp ) -> (match (_discr_) with
| BNot (_) -> begin
true
end
| _ -> begin
false
end))


let is_BAnd = (fun ( _discr_  :  l__BoolExp ) -> (match (_discr_) with
| BAnd (_) -> begin
true
end
| _ -> begin
false
end))


let is_BXor = (fun ( _discr_  :  l__BoolExp ) -> (match (_discr_) with
| BXor (_) -> begin
true
end
| _ -> begin
false
end))


let ___BVar____0 = (fun ( projectee  :  l__BoolExp ) -> (match (projectee) with
| BVar (_19_3) -> begin
_19_3
end))


let ___BNot____0 = (fun ( projectee  :  l__BoolExp ) -> (match (projectee) with
| BNot (_19_6) -> begin
_19_6
end))


let ___BAnd____0 = (fun ( projectee  :  l__BoolExp ) -> (match (projectee) with
| BAnd (_19_9) -> begin
_19_9
end))


let ___BXor____0 = (fun ( projectee  :  l__BoolExp ) -> (match (projectee) with
| BXor (_19_12) -> begin
_19_12
end))


let rec prettyPrintBexp : l__BoolExp  ->  Prims.string = (fun ( bexp  :  l__BoolExp ) -> (match (bexp) with
| BFalse -> begin
"false"
end
| BVar (i) -> begin
(Prims.string_of_int i)
end
| BNot (x) -> begin
(FStar.String.strcat "~" (prettyPrintBexp x))
end
| BAnd (x, y) -> begin
(FStar.String.strcat "(" (FStar.String.strcat (prettyPrintBexp x) (FStar.String.strcat " && " (FStar.String.strcat (prettyPrintBexp y) ")"))))
end
| BXor (x, y) -> begin
(FStar.String.strcat "(" (FStar.String.strcat (prettyPrintBexp x) (FStar.String.strcat " <> " (FStar.String.strcat (prettyPrintBexp y) ")"))))
end))


let rec occursInBexp : Prims.int  ->  l__BoolExp  ->  Prims.bool = (fun ( i  :  Prims.int ) ( exp  :  l__BoolExp ) -> (match (exp) with
| BFalse -> begin
false
end
| BVar (n) -> begin
(n = i)
end
| BAnd (x, y) -> begin
((occursInBexp i x) || (occursInBexp i y))
end
| BXor (x, y) -> begin
((occursInBexp i x) || (occursInBexp i y))
end
| BNot (x) -> begin
(occursInBexp i x)
end))


let vars : l__BoolExp  ->  Prims.int Util.set = (fun ( exp  :  l__BoolExp ) ( i  :  Prims.int ) -> (occursInBexp i exp))


let rec getVars_acc : Prims.int Prims.list  ->  l__BoolExp  ->  Prims.int Prims.list = (fun ( acc  :  Prims.int Prims.list ) ( exp  :  l__BoolExp ) -> (match (exp) with
| BFalse -> begin
[]
end
| BVar (n) -> begin
if (FStar.List.memT n acc) then begin
acc
end else begin
(n)::acc
end
end
| BAnd (x, y) -> begin
(getVars_acc (getVars_acc acc x) y)
end
| BXor (x, y) -> begin
(getVars_acc (getVars_acc acc x) y)
end
| BNot (exp) -> begin
(getVars_acc acc exp)
end))


let getVars : l__BoolExp  ->  Prims.int Prims.list = (fun ( exp  :  l__BoolExp ) -> (getVars_acc [] exp))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun ( x  :  Prims.int ) ( y  :  Prims.int ) -> if (x > y) then begin
x
end else begin
y
end)


let rec listMax : Prims.int Prims.list  ->  Prims.int = (fun ( lst  :  Prims.int Prims.list ) -> (match (lst) with
| [] -> begin
(Prims.parse_int "0")
end
| x::xs -> begin
(max x (listMax xs))
end))


let varCount : l__BoolExp  ->  Prims.int = (fun ( exp  :  l__BoolExp ) -> (FStar.List.length (getVars exp)))


let varMax : l__BoolExp  ->  Prims.int = (fun ( exp  :  l__BoolExp ) -> (listMax (getVars exp)))


let rec gtVars : Prims.int  ->  l__BoolExp  ->  Prims.bool = (fun ( i  :  Prims.int ) ( bexp  :  l__BoolExp ) -> (match (bexp) with
| BFalse -> begin
false
end
| BVar (j) -> begin
(i > j)
end
| BNot (x) -> begin
(gtVars i x)
end
| (BXor (x, y)) | (BAnd (x, y)) -> begin
((gtVars i x) && (gtVars i y))
end))


let rec substBexp : l__BoolExp  ->  (Prims.int, l__BoolExp) Total.map  ->  l__BoolExp = (fun ( bexp  :  l__BoolExp ) ( sub  :  (Prims.int, l__BoolExp) Total.map ) -> (match (bexp) with
| BFalse -> begin
BFalse
end
| BVar (i) -> begin
(sub i)
end
| BNot (x) -> begin
BNot ((substBexp x sub))
end
| BAnd (x, y) -> begin
BAnd (((substBexp x sub), (substBexp y sub)))
end
| BXor (x, y) -> begin
BXor (((substBexp x sub), (substBexp y sub)))
end))


let rec substVar : l__BoolExp  ->  (Prims.int, Prims.int) Total.map  ->  l__BoolExp = (fun ( bexp  :  l__BoolExp ) ( sub  :  (Prims.int, Prims.int) Total.map ) -> (match (bexp) with
| BFalse -> begin
BFalse
end
| BVar (i) -> begin
BVar ((sub i))
end
| BNot (x) -> begin
BNot ((substVar x sub))
end
| BAnd (x, y) -> begin
BAnd (((substVar x sub), (substVar y sub)))
end
| BXor (x, y) -> begin
BXor (((substVar x sub), (substVar y sub)))
end))


let rec evalBexp : l__BoolExp  ->  Total.state  ->  Prims.bool = (fun ( bexp  :  l__BoolExp ) ( st  :  Total.state ) -> (match (bexp) with
| BFalse -> begin
false
end
| BVar (i) -> begin
(st i)
end
| BNot (x) -> begin
(not ((evalBexp x st)))
end
| BAnd (x, y) -> begin
((evalBexp x st) && (evalBexp y st))
end
| BXor (x, y) -> begin
((evalBexp x st) <> (evalBexp y st))
end))


let rec simplify : l__BoolExp  ->  l__BoolExp = (fun ( exp  :  l__BoolExp ) -> (match (exp) with
| BFalse -> begin
BFalse
end
| BVar (x) -> begin
exp
end
| BAnd (x, y) -> begin
(

let x' = (simplify x)
in (

let y' = (simplify y)
in (match ((x', y')) with
| ((BFalse, _)) | ((_, BFalse)) -> begin
BFalse
end
| _19_150 -> begin
BAnd ((x', y'))
end)))
end
| BXor (x, y) -> begin
(

let x' = (simplify x)
in (

let y' = (simplify y)
in (match ((x', y')) with
| ((BFalse, z)) | ((z, BFalse)) -> begin
z
end
| _19_163 -> begin
BXor ((x', y'))
end)))
end
| BNot (x) -> begin
(

let x' = (simplify x)
in (match (x') with
| BNot (y) -> begin
y
end
| _19_170 -> begin
BNot (x')
end))
end))


let rec factorAs : l__BoolExp  ->  Prims.int  ->  l__BoolExp Prims.option = (fun ( exp  :  l__BoolExp ) ( targ  :  Prims.int ) -> (match (exp) with
| BFalse -> begin
None
end
| BVar (i) -> begin
if (i = targ) then begin
Some (BFalse)
end else begin
None
end
end
| BNot (x) -> begin
(match ((factorAs x targ)) with
| None -> begin
None
end
| Some (x') -> begin
Some (BNot (x'))
end)
end
| BAnd (x, y) -> begin
None
end
| BXor (x, y) -> begin
if (not ((occursInBexp targ y))) then begin
(match ((factorAs x targ)) with
| None -> begin
None
end
| Some (x') -> begin
Some (BXor ((x', y)))
end)
end else begin
if (not ((occursInBexp targ x))) then begin
(match ((factorAs y targ)) with
| None -> begin
None
end
| Some (y') -> begin
Some (BXor ((x, y')))
end)
end else begin
None
end
end
end))


let rec distributeAnds : l__BoolExp  ->  l__BoolExp = (fun ( exp  :  l__BoolExp ) -> (match (exp) with
| BFalse -> begin
BFalse
end
| BVar (v) -> begin
BVar (v)
end
| BNot (x) -> begin
BNot ((distributeAnds x))
end
| BAnd (x, y) -> begin
(match (((distributeAnds x), (distributeAnds y))) with
| (BXor (a, b), BXor (c, d)) -> begin
BXor ((BXor ((BAnd ((a, c)), BAnd ((b, c)))), BXor ((BAnd ((a, d)), BAnd ((b, d))))))
end
| (x', BXor (c, d)) -> begin
BXor ((BAnd ((x', c)), BAnd ((x', d))))
end
| (BXor (a, b), y') -> begin
BXor ((BAnd ((a, y')), BAnd ((b, y'))))
end
| (x', y') -> begin
BAnd ((x', y'))
end)
end
| BXor (x, y) -> begin
BXor (((distributeAnds x), (distributeAnds y)))
end))


let rec undistributeAnds : l__BoolExp  ->  l__BoolExp = (fun ( exp  :  l__BoolExp ) -> (match (exp) with
| BFalse -> begin
BFalse
end
| BVar (v) -> begin
BVar (v)
end
| BNot (x) -> begin
BNot ((undistributeAnds x))
end
| BAnd (x, y) -> begin
BAnd (((undistributeAnds x), (undistributeAnds y)))
end
| BXor (x, y) -> begin
(match (((undistributeAnds x), (undistributeAnds y))) with
| (BAnd (a, b), BAnd (c, d)) -> begin
if (a = c) then begin
BAnd ((a, BXor ((b, d))))
end else begin
if (a = d) then begin
BAnd ((a, BXor ((b, c))))
end else begin
if (b = c) then begin
BAnd ((b, BXor ((a, d))))
end else begin
if (b = d) then begin
BAnd ((b, BXor ((a, c))))
end else begin
BXor ((BAnd ((a, b)), BAnd ((c, d))))
end
end
end
end
end
| (x', y') -> begin
BXor ((x', y'))
end)
end))


type compilerResult =
(AncillaHeap.l__AncHeap * Prims.int * Prims.int Prims.list * Circuit.l__Gate Prims.list)


let rec compileBexp : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  compilerResult = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) -> (match (exp) with
| BFalse -> begin
(ah, targ, [], [])
end
| BVar (v) -> begin
(ah, targ, [], (Circuit.RCNOT ((v, targ)))::[])
end
| BAnd (x, y) -> begin
(

let _19_279 = (compileBexp_oop ah x)
in (match (_19_279) with
| (ah', xres, xanc, xgate) -> begin
(

let _19_284 = (compileBexp_oop ah' y)
in (match (_19_284) with
| (ah'', yres, yanc, ygate) -> begin
(ah'', targ, (FStar.List.append xanc yanc), (FStar.List.append (FStar.List.append xgate ygate) ((Circuit.RTOFF ((xres, yres, targ)))::[])))
end))
end))
end
| BXor (x, y) -> begin
(

let _19_293 = (compileBexp ah targ x)
in (match (_19_293) with
| (ah', xres, xanc, xgate) -> begin
(

let _19_298 = (compileBexp ah' targ y)
in (match (_19_298) with
| (ah'', yres, yanc, ygate) -> begin
(ah'', targ, (FStar.List.append xanc yanc), (FStar.List.append xgate ygate))
end))
end))
end
| BNot (exp) -> begin
(

let _19_305 = (compileBexp ah targ exp)
in (match (_19_305) with
| (ah', xres, xanc, xgate) -> begin
(ah', targ, xanc, (FStar.List.append xgate ((Circuit.RNOT (xres))::[])))
end))
end))
and compileBexp_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  compilerResult = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( exp  :  l__BoolExp ) -> (match (exp) with
| BVar (v) -> begin
(ah, v, [], [])
end
| _19_311 -> begin
(

let _19_314 = (AncillaHeap.popMin ah)
in (match (_19_314) with
| (ah', targ) -> begin
(

let _19_319 = (compileBexp ah' targ exp)
in (match (_19_319) with
| (ah'', res, anc, gate) -> begin
(ah'', res, (targ)::anc, gate)
end))
end))
end))


let compileBexpClean : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  compilerResult = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) -> (

let _19_327 = (compileBexp ah targ exp)
in (match (_19_327) with
| (ah', res, anc, circ) -> begin
(

let cleanup = (Circuit.uncompute circ res)
in (

let ah'' = (FStar.List.fold_left AncillaHeap.insert ah' anc)
in (ah'', res, [], (FStar.List.append circ (FStar.List.rev cleanup)))))
end)))


let compileBexpClean_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  compilerResult = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( exp  :  l__BoolExp ) -> (match (exp) with
| BVar (v) -> begin
(ah, v, [], [])
end
| _19_335 -> begin
(

let _19_338 = (AncillaHeap.popMin ah)
in (match (_19_338) with
| (ah', targ) -> begin
(

let _19_343 = (compileBexpClean ah' targ exp)
in (match (_19_343) with
| (ah'', res, anc, gate) -> begin
(ah'', res, (targ)::anc, gate)
end))
end))
end))


let rec compileBexpPebbled : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  compilerResult = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) -> (match (exp) with
| BFalse -> begin
(ah, targ, [], [])
end
| BVar (v) -> begin
(ah, targ, [], (Circuit.RCNOT ((v, targ)))::[])
end
| BAnd (x, y) -> begin
(

let _19_360 = (compileBexpPebbled_oop ah x)
in (match (_19_360) with
| (ah', xres, xanc, xgate) -> begin
(

let _19_365 = (compileBexpPebbled_oop ah' y)
in (match (_19_365) with
| (ah'', yres, yanc, ygate) -> begin
(

let cleanup = (Circuit.uncompute (FStar.List.append xgate ygate) targ)
in (

let ah''' = (FStar.List.fold_left AncillaHeap.insert ah'' (FStar.List.append xanc yanc))
in (ah''', targ, [], (FStar.List.append (FStar.List.append (FStar.List.append xgate ygate) ((Circuit.RTOFF ((xres, yres, targ)))::[])) (FStar.List.rev cleanup)))))
end))
end))
end
| BXor (x, y) -> begin
(

let _19_376 = (compileBexpPebbled ah targ x)
in (match (_19_376) with
| (ah', xres, xanc, xgate) -> begin
(

let _19_381 = (compileBexpPebbled ah' targ y)
in (match (_19_381) with
| (ah'', yres, yanc, ygate) -> begin
(ah'', targ, (FStar.List.append xanc yanc), (FStar.List.append xgate ygate))
end))
end))
end
| BNot (exp) -> begin
(

let _19_388 = (compileBexpPebbled ah targ exp)
in (match (_19_388) with
| (ah', xres, xanc, xgate) -> begin
(ah', targ, xanc, (FStar.List.append xgate ((Circuit.RNOT (xres))::[])))
end))
end))
and compileBexpPebbled_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  compilerResult = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( exp  :  l__BoolExp ) -> (match (exp) with
| BVar (v) -> begin
(ah, v, [], [])
end
| _19_394 -> begin
(

let _19_397 = (AncillaHeap.popMin ah)
in (match (_19_397) with
| (ah', targ) -> begin
(

let _19_402 = (compileBexpPebbled ah' targ exp)
in (match (_19_402) with
| (ah'', res, anc, gate) -> begin
(ah'', res, (targ)::anc, gate)
end))
end))
end))


let first = (fun ( _19_410  :  ('A_19_82024 * 'A_19_82023 * 'A_19_82022 * 'A_19_82021) ) -> (match (_19_410) with
| (x, _19_405, _19_407, _19_409) -> begin
x
end))


let second = (fun ( _19_418  :  ('A_19_82160 * 'A_19_82159 * 'A_19_82158 * 'A_19_82157) ) -> (match (_19_418) with
| (_19_412, x, _19_415, _19_417) -> begin
x
end))


let third = (fun ( _19_426  :  ('A_19_82296 * 'A_19_82295 * 'A_19_82294 * 'A_19_82293) ) -> (match (_19_426) with
| (_19_420, _19_422, x, _19_425) -> begin
x
end))


let last = (fun ( _19_434  :  ('A_19_82432 * 'A_19_82431 * 'A_19_82430 * 'A_19_82429) ) -> (match (_19_434) with
| (_19_428, _19_430, _19_432, x) -> begin
x
end))


let compileBexpEval : AncillaHeap.l__AncHeapRecord  ->  Prims.int  ->  l__BoolExp  ->  Total.state  ->  Prims.bool = (fun ( ah  :  AncillaHeap.l__AncHeapRecord ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) ( st  :  Total.state ) -> (

let _19_443 = (compileBexp ah targ exp)
in (match (_19_443) with
| (ah', res, anc, circ) -> begin
(Circuit.evalCirc circ st res)
end)))


let compileBexpEval_oop : AncillaHeap.l__AncHeapRecord  ->  l__BoolExp  ->  Total.state  ->  Prims.bool = (fun ( ah  :  AncillaHeap.l__AncHeapRecord ) ( exp  :  l__BoolExp ) ( st  :  Total.state ) -> (

let _19_451 = (compileBexp_oop ah exp)
in (match (_19_451) with
| (ah', res, anc, circ) -> begin
(Circuit.evalCirc circ st res)
end)))


let compileBexpCleanEval : AncillaHeap.l__AncHeapRecord  ->  Prims.int  ->  l__BoolExp  ->  Total.state  ->  Prims.bool = (fun ( ah  :  AncillaHeap.l__AncHeapRecord ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) ( st  :  Total.state ) -> (

let _19_460 = (compileBexpClean ah targ exp)
in (match (_19_460) with
| (ah', res, anc, circ) -> begin
(Circuit.evalCirc circ st res)
end)))


let compileBexpCleanEval_oop : AncillaHeap.l__AncHeapRecord  ->  l__BoolExp  ->  Total.state  ->  Prims.bool = (fun ( ah  :  AncillaHeap.l__AncHeapRecord ) ( exp  :  l__BoolExp ) ( st  :  Total.state ) -> (

let _19_468 = (compileBexpClean_oop ah exp)
in (match (_19_468) with
| (ah', res, anc, circ) -> begin
(Circuit.evalCirc circ st res)
end)))


let compileBexpCleanEvalSt : AncillaHeap.l__AncHeapRecord  ->  Prims.int  ->  l__BoolExp  ->  Total.state  ->  Total.state = (fun ( ah  :  AncillaHeap.l__AncHeapRecord ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) ( st  :  Total.state ) -> (

let _19_477 = (compileBexpClean ah targ exp)
in (match (_19_477) with
| (ah', res, anc, circ) -> begin
(Circuit.evalCirc circ st)
end)))


let compileBexpCleanEvalSt_oop : AncillaHeap.l__AncHeapRecord  ->  l__BoolExp  ->  Total.state  ->  Total.state = (fun ( ah  :  AncillaHeap.l__AncHeapRecord ) ( exp  :  l__BoolExp ) ( st  :  Total.state ) -> (

let _19_485 = (compileBexpClean_oop ah exp)
in (match (_19_485) with
| (ah', res, anc, circ) -> begin
(Circuit.evalCirc circ st)
end)))


let rec simplify_preserves_semantics : l__BoolExp  ->  Prims.unit = (fun ( exp  :  l__BoolExp ) -> ())


let rec factorAs_correct : l__BoolExp  ->  Prims.int  ->  Total.state  ->  Prims.unit = (fun ( exp  :  l__BoolExp ) ( targ  :  Prims.int ) ( st  :  Total.state ) -> ())


let rec factorAs_vars : l__BoolExp  ->  Prims.int  ->  Prims.unit = (fun ( exp  :  l__BoolExp ) ( targ  :  Prims.int ) -> ())


let idempotentAnd : l__BoolExp  ->  Prims.unit = (fun ( x  :  l__BoolExp ) -> ())


let commutativityAnd : l__BoolExp  ->  l__BoolExp  ->  Prims.unit = (fun ( x  :  l__BoolExp ) ( y  :  l__BoolExp ) -> ())


let commutativityXor : l__BoolExp  ->  l__BoolExp  ->  Prims.unit = (fun ( x  :  l__BoolExp ) ( y  :  l__BoolExp ) -> ())


let distributivityAndXor : l__BoolExp  ->  l__BoolExp  ->  l__BoolExp  ->  Prims.unit = (fun ( x  :  l__BoolExp ) ( y  :  l__BoolExp ) ( z  :  l__BoolExp ) -> ())


let rec distribute_preserves_semantics : l__BoolExp  ->  Prims.unit = (fun ( exp  :  l__BoolExp ) -> ())


let rec undistribute_preserves_semantics : l__BoolExp  ->  Prims.unit = (fun ( exp  :  l__BoolExp ) -> ())


let rec compile_decreases_heap : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) -> ())
and compile_decreases_heap_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( exp  :  l__BoolExp ) -> ())


let rec compileClean_decreases_heap : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) -> ())
and compileClean_decreases_heap_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( exp  :  l__BoolExp ) -> ())


let compile_output : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( x  :  l__BoolExp ) -> ())


let compile_output_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( x  :  l__BoolExp ) -> ())


let rec compile_partition : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( x  :  l__BoolExp ) -> ())
and compile_partition_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( x  :  l__BoolExp ) -> ())


let rec compile_mods : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) -> ())
and compile_mods_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( x  :  l__BoolExp ) -> ())


let rec eval_state_swap : l__BoolExp  ->  Total.state  ->  Total.state  ->  Prims.unit = (fun ( x  :  l__BoolExp ) ( st  :  Total.state ) ( st'  :  Total.state ) -> ())


let zeroHeap_st_impl : Total.state  ->  AncillaHeap.l__AncHeap  ->  Circuit.l__Gate Prims.list  ->  Prims.unit = (fun ( st  :  Total.state ) ( ah  :  AncillaHeap.l__AncHeap ) ( gates  :  Circuit.l__Gate Prims.list ) -> ())


let rec compile_bexp_correct : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  Total.state  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) ( st  :  Total.state ) -> ())
and compile_bexp_correct_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  Total.state  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( exp  :  l__BoolExp ) ( st  :  Total.state ) -> ())


let rec compileBexp_wf : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) -> ())
and compileBexp_wf_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( exp  :  l__BoolExp ) -> ())


let rec compile_anc : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) -> ())
and compile_anc_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( exp  :  l__BoolExp ) -> ())


let rec compile_ctrls : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( x  :  l__BoolExp ) -> ())
and compile_ctrls_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( x  :  l__BoolExp ) -> ())


let compile_with_cleanup : AncillaHeap.l__AncHeap  ->  Prims.int  ->  l__BoolExp  ->  Total.state  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( targ  :  Prims.int ) ( exp  :  l__BoolExp ) ( st  :  Total.state ) -> ())


let compile_with_cleanup_oop : AncillaHeap.l__AncHeap  ->  l__BoolExp  ->  Total.state  ->  Prims.unit = (fun ( ah  :  AncillaHeap.l__AncHeap ) ( exp  :  l__BoolExp ) ( st  :  Total.state ) -> ())




