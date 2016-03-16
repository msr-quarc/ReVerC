#light "off"
module Interpreter
open Prims

type 'Astate interpretation =
{alloc : 'Astate  ->  BoolExp.l__BoolExp  ->  (Prims.int * 'Astate); assign : 'Astate  ->  Prims.int  ->  BoolExp.l__BoolExp  ->  'Astate; eval : 'Astate  ->  Total.state  ->  Prims.int  ->  Prims.bool}


let is_Mkinterpretation = (Prims.checked_cast(fun ( _  :  'Astate interpretation ) -> (FStar.All.failwith "Not yet implemented:is_Mkinterpretation")))


let rec isVal : ExprTypes.l__GExpr  ->  Prims.bool = (fun ( tm  :  ExprTypes.l__GExpr ) -> (match (tm) with
| ExprTypes.UNIT -> begin
true
end
| ExprTypes.LAMBDA (s, ty, t) -> begin
true
end
| ExprTypes.LOC (i) -> begin
true
end
| ExprTypes.ARRAY (lst) -> begin
(isVal_lst lst)
end
| _18_20 -> begin
false
end))
and isVal_lst : ExprTypes.l__GExpr Prims.list  ->  Prims.bool = (fun ( lst  :  ExprTypes.l__GExpr Prims.list ) -> (match (lst) with
| [] -> begin
true
end
| ExprTypes.LOC (l)::xs -> begin
(isVal_lst xs)
end
| _18_28 -> begin
false
end))


let isBexp : ExprTypes.l__GExpr  ->  Prims.bool = (fun ( tm  :  ExprTypes.l__GExpr ) -> (match (tm) with
| ExprTypes.LOC (i) -> begin
true
end
| ExprTypes.BEXP (bexp) -> begin
true
end
| ExprTypes.BOOL (b) -> begin
true
end
| _18_37 -> begin
false
end))


type 'Astate config =
(ExprTypes.l__GExpr * 'Astate)


type 'Astate valconfig =
'Astate config


type 'Astate listconfig =
(ExprTypes.l__GExpr Prims.list * 'Astate)


let get_bexp : ExprTypes.l__GExpr  ->  BoolExp.l__BoolExp = (fun ( gexp  :  ExprTypes.l__GExpr ) -> (match (gexp) with
| ExprTypes.LOC (i) -> begin
BoolExp.BVar (i)
end
| ExprTypes.BEXP (bexp) -> begin
bexp
end
| ExprTypes.BOOL (b) -> begin
if b then begin
BoolExp.BNot (BoolExp.BFalse)
end else begin
BoolExp.BFalse
end
end))


let rec step = (fun ( _18_57  :  'Astate config ) ( interp  :  'Astate interpretation ) -> (match (_18_57) with
| (tm, st) -> begin
(match (tm) with
| ExprTypes.LET (x, t1, t2) -> begin
if (isVal t1) then begin
Util.Val (((ExprTypes.substGExpr t2 x t1), st))
end else begin
(Util.bindT (step (t1, st) interp) (fun ( _18_66  :  'Astate config ) -> (match (_18_66) with
| (t1', st') -> begin
Util.Val ((ExprTypes.LET ((x, t1', t2)), st'))
end)))
end
end
| ExprTypes.APPLY (t1, t2) -> begin
if (not ((isVal t1))) then begin
(Util.bindT (step (t1, st) interp) (fun ( _18_73  :  'Astate config ) -> (match (_18_73) with
| (t1', st') -> begin
Util.Val ((ExprTypes.APPLY ((t1', t2)), st'))
end)))
end else begin
if (not ((isVal t2))) then begin
(Util.bindT (step (t2, st) interp) (fun ( _18_76  :  'Astate config ) -> (match (_18_76) with
| (t2', st') -> begin
Util.Val ((ExprTypes.APPLY ((t1, t2')), st'))
end)))
end else begin
(match (t1) with
| ExprTypes.LAMBDA (x, ty, t) -> begin
Util.Val (((ExprTypes.substGExpr t x t2), st))
end
| _18_83 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce application: " (ExprTypes.show tm)))
end)
end
end
end
| ExprTypes.SEQUENCE (t1, t2) -> begin
if (not ((isVal t1))) then begin
(Util.bindT (step (t1, st) interp) (fun ( _18_90  :  'Astate config ) -> (match (_18_90) with
| (t1', st') -> begin
Util.Val ((ExprTypes.SEQUENCE ((t1', t2)), st'))
end)))
end else begin
(match (t1) with
| ExprTypes.UNIT -> begin
Util.Val ((t2, st))
end
| _18_93 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce sequence: " (ExprTypes.show tm)))
end)
end
end
| ExprTypes.ASSIGN (t1, t2) -> begin
if (not ((isVal t1))) then begin
(Util.bindT (step (t1, st) interp) (fun ( _18_100  :  'Astate config ) -> (match (_18_100) with
| (t1', st') -> begin
Util.Val ((ExprTypes.ASSIGN ((t1', t2)), st'))
end)))
end else begin
if (not ((isBexp t2))) then begin
(Util.bindT (step (t2, st) interp) (fun ( _18_103  :  'Astate config ) -> (match (_18_103) with
| (t2', st') -> begin
Util.Val ((ExprTypes.ASSIGN ((t1, t2')), st'))
end)))
end else begin
(match (t1) with
| ExprTypes.LOC (l) -> begin
Util.Val ((ExprTypes.UNIT, (interp.assign st l (get_bexp t2))))
end
| _18_107 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce assignment: " (ExprTypes.show tm)))
end)
end
end
end
| ExprTypes.XOR (t1, t2) -> begin
if (not ((isBexp t1))) then begin
(Util.bindT (step (t1, st) interp) (fun ( _18_114  :  'Astate config ) -> (match (_18_114) with
| (t1', st') -> begin
Util.Val ((ExprTypes.XOR ((t1', t2)), st'))
end)))
end else begin
if (not ((isBexp t2))) then begin
(Util.bindT (step (t2, st) interp) (fun ( _18_117  :  'Astate config ) -> (match (_18_117) with
| (t2', st') -> begin
Util.Val ((ExprTypes.XOR ((t1, t2')), st'))
end)))
end else begin
Util.Val ((ExprTypes.BEXP (BoolExp.BXor (((get_bexp t1), (get_bexp t2)))), st))
end
end
end
| ExprTypes.AND (t1, t2) -> begin
if (not ((isBexp t1))) then begin
(Util.bindT (step (t1, st) interp) (fun ( _18_124  :  'Astate config ) -> (match (_18_124) with
| (t1', st') -> begin
Util.Val ((ExprTypes.AND ((t1', t2)), st'))
end)))
end else begin
if (not ((isBexp t2))) then begin
(Util.bindT (step (t2, st) interp) (fun ( _18_127  :  'Astate config ) -> (match (_18_127) with
| (t2', st') -> begin
Util.Val ((ExprTypes.AND ((t1, t2')), st'))
end)))
end else begin
Util.Val ((ExprTypes.BEXP (BoolExp.BAnd (((get_bexp t1), (get_bexp t2)))), st))
end
end
end
| ExprTypes.BOOL (b) -> begin
(

let bexp = if b then begin
BoolExp.BNot (BoolExp.BFalse)
end else begin
BoolExp.BFalse
end
in Util.Val ((ExprTypes.BEXP (bexp), st)))
end
| ExprTypes.APPEND (t1, t2) -> begin
if (not ((isVal t1))) then begin
(Util.bindT (step (t1, st) interp) (fun ( _18_137  :  'Astate config ) -> (match (_18_137) with
| (t1', st') -> begin
Util.Val ((ExprTypes.APPLY ((t1', t2)), st'))
end)))
end else begin
if (not ((isVal t2))) then begin
(Util.bindT (step (t2, st) interp) (fun ( _18_140  :  'Astate config ) -> (match (_18_140) with
| (t2', st') -> begin
Util.Val ((ExprTypes.APPLY ((t1, t2')), st'))
end)))
end else begin
(match ((t1, t2)) with
| (ExprTypes.ARRAY (l), ExprTypes.ARRAY (l')) -> begin
Util.Val ((ExprTypes.ARRAY ((FStar.List.append l l')), st))
end
| _18_147 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce append: " (ExprTypes.show tm)))
end)
end
end
end
| ExprTypes.ROT (i, t) -> begin
if (not ((isVal t))) then begin
(Util.bindT (step (t, st) interp) (fun ( _18_154  :  'Astate config ) -> (match (_18_154) with
| (t', st') -> begin
Util.Val ((ExprTypes.ROT ((i, t')), st'))
end)))
end else begin
(match (t) with
| ExprTypes.ARRAY (lst) -> begin
if ((0 <= i) && (i < (FStar.List.lengthT lst))) then begin
Util.Val ((ExprTypes.ARRAY ((Util.rotate lst i)), st))
end else begin
Util.Err ((FStar.String.strcat "Array out of bounds: " (ExprTypes.show tm)))
end
end
| _18_158 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce rotation: " (ExprTypes.show tm)))
end)
end
end
| ExprTypes.SLICE (t, i, j) -> begin
if (not ((isVal t))) then begin
(Util.bindT (step (t, st) interp) (fun ( _18_166  :  'Astate config ) -> (match (_18_166) with
| (t', st') -> begin
Util.Val ((ExprTypes.SLICE ((t', i, j)), st'))
end)))
end else begin
(match (t) with
| ExprTypes.ARRAY (lst) -> begin
if (((0 <= i) && (i <= j)) && (j < (FStar.List.lengthT lst))) then begin
Util.Val ((ExprTypes.ARRAY ((Util.slice lst i j)), st))
end else begin
Util.Err ((FStar.String.strcat "Array out of bounds: " (ExprTypes.show tm)))
end
end
| _18_170 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce slice: " (ExprTypes.show tm)))
end)
end
end
| ExprTypes.ARRAY (lst) -> begin
(Util.bindT (step_lst (lst, st) interp) (fun ( _18_175  :  'Astate listconfig ) -> (match (_18_175) with
| (lst, st') -> begin
Util.Val ((ExprTypes.ARRAY (lst), st'))
end)))
end
| ExprTypes.GET_ARRAY (t, i) -> begin
if (not ((isVal t))) then begin
(Util.bindT (step (t, st) interp) (fun ( _18_182  :  'Astate config ) -> (match (_18_182) with
| (t', st') -> begin
Util.Val ((ExprTypes.GET_ARRAY ((t', i)), st'))
end)))
end else begin
(match (t) with
| ExprTypes.ARRAY (lst) -> begin
if ((0 <= i) && (i < (FStar.List.lengthT lst))) then begin
Util.Val (((Util.nthT lst i), st))
end else begin
Util.Err ((FStar.String.strcat "Array out of bounds: " (ExprTypes.show tm)))
end
end
| _18_186 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce array index: " (ExprTypes.show tm)))
end)
end
end
| ExprTypes.ASSERT (t) -> begin
if (not ((isVal t))) then begin
(Util.bindT (step (t, st) interp) (fun ( _18_191  :  'Astate config ) -> (match (_18_191) with
| (t', st') -> begin
Util.Val ((ExprTypes.ASSERT (t'), st'))
end)))
end else begin
(match (t) with
| ExprTypes.LOC (l) -> begin
Util.Val ((ExprTypes.UNIT, st))
end
| _18_195 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce assertion: " (ExprTypes.show tm)))
end)
end
end
| ExprTypes.BEXP (bexp) -> begin
(

let _18_200 = (interp.alloc st bexp)
in (match (_18_200) with
| (l, st') -> begin
Util.Val ((ExprTypes.LOC (l), st'))
end))
end
| _18_202 -> begin
Util.Err ((FStar.String.strcat "No rule applies: " (ExprTypes.show tm)))
end)
end))
and step_lst = (fun ( _18_205  :  'Astate listconfig ) ( interp  :  'Astate interpretation ) -> (match (_18_205) with
| (lst, st) -> begin
(match (lst) with
| [] -> begin
Util.Val (([], st))
end
| x::xs -> begin
if (not ((isVal x))) then begin
(Util.bindT (step (x, st) interp) (fun ( _18_213  :  'Astate config ) -> (match (_18_213) with
| (x', st') -> begin
Util.Val (((x')::xs, st'))
end)))
end else begin
(Util.bindT (step_lst (xs, st) interp) (fun ( _18_216  :  'Astate listconfig ) -> (match (_18_216) with
| (xs', st') -> begin
Util.Val (((x)::xs', st'))
end)))
end
end)
end))


let rec eval_rec = (fun ( _18_221  :  'Astate config ) ( interp  :  'Astate interpretation ) -> (match (_18_221) with
| (tm, st) -> begin
(match (tm) with
| ExprTypes.LET (x, t1, t2) -> begin
(Util.bind (eval_rec (t1, st) interp) (fun ( _18_230  :  'Astate config ) -> (match (_18_230) with
| (v1, st') -> begin
(eval_rec ((ExprTypes.substGExpr t2 x v1), st') interp)
end)))
end
| ExprTypes.LAMBDA (x, ty, t) -> begin
Util.Val ((tm, st))
end
| ExprTypes.APPLY (t1, t2) -> begin
(Util.bind (eval_rec (t1, st) interp) (fun ( _18_242  :  'Astate config ) -> (match (_18_242) with
| (v1, st') -> begin
(Util.bind (eval_rec (t2, st') interp) (fun ( _18_245  :  'Astate config ) -> (match (_18_245) with
| (v2, st'') -> begin
(match (v1) with
| ExprTypes.LAMBDA (x, ty, t) -> begin
(eval_rec ((ExprTypes.substGExpr t x v2), st'') interp)
end
| _18_252 -> begin
Util.Err ((FStar.String.strcat "LHS is not a lambda: " (ExprTypes.show tm)))
end)
end)))
end)))
end
| ExprTypes.SEQUENCE (t1, t2) -> begin
(Util.bind (eval_rec (t1, st) interp) (fun ( _18_259  :  'Astate config ) -> (match (_18_259) with
| (v1, st') -> begin
(eval_rec (t2, st') interp)
end)))
end
| ExprTypes.ASSIGN (t1, t2) -> begin
(Util.bind (eval_rec (t1, st) interp) (fun ( _18_266  :  'Astate config ) -> (match (_18_266) with
| (v1, st') -> begin
(Util.bind (eval_rec (t2, st') interp) (fun ( _18_269  :  'Astate config ) -> (match (_18_269) with
| (v2, st'') -> begin
(match ((v1, v2)) with
| (ExprTypes.LOC (l), ExprTypes.BEXP (bexp)) -> begin
Util.Val ((ExprTypes.UNIT, (interp.assign st' l bexp)))
end
| _18_276 -> begin
Util.Err ((FStar.String.strcat "Invalid parameters: " (ExprTypes.show tm)))
end)
end)))
end)))
end
| (ExprTypes.XOR (_)) | (ExprTypes.AND (_)) | (ExprTypes.BOOL (_)) -> begin
(Util.bind (eval_to_bexp (tm, st) interp) (fun ( c  :  'Astate config ) -> (eval_rec c interp)))
end
| ExprTypes.APPEND (t1, t2) -> begin
(Util.bind (eval_rec (t1, st) interp) (fun ( _18_293  :  'Astate config ) -> (match (_18_293) with
| (v1, st') -> begin
(Util.bind (eval_rec (t2, st') interp) (fun ( _18_296  :  'Astate config ) -> (match (_18_296) with
| (v2, st'') -> begin
(match ((v1, v2)) with
| (ExprTypes.ARRAY (l1), ExprTypes.ARRAY (l2)) -> begin
Util.Val ((ExprTypes.ARRAY ((FStar.List.append l1 l2)), st''))
end
| _18_303 -> begin
Util.Err ((FStar.String.strcat "Append of non-array argument: " (ExprTypes.show tm)))
end)
end)))
end)))
end
| ExprTypes.ROT (i, t) -> begin
(Util.bind (eval_rec (t, st) interp) (fun ( _18_310  :  'Astate config ) -> (match (_18_310) with
| (v, st') -> begin
(match (v) with
| ExprTypes.ARRAY (lst) -> begin
if ((0 <= i) && (i < (FStar.List.length lst))) then begin
Util.Val ((ExprTypes.ARRAY ((Util.rotate lst i)), st'))
end else begin
Util.Err ((FStar.String.strcat "Rotation out of array bounds: " (ExprTypes.show tm)))
end
end
| _18_314 -> begin
Util.Err ((FStar.String.strcat "Rotation of non-array argument: " (ExprTypes.show tm)))
end)
end)))
end
| ExprTypes.SLICE (t, i, j) -> begin
(Util.bind (eval_rec (t, st) interp) (fun ( _18_322  :  'Astate config ) -> (match (_18_322) with
| (v, st') -> begin
(match (v) with
| ExprTypes.ARRAY (lst) -> begin
if (((0 <= i) && (i <= j)) && (j < (FStar.List.length lst))) then begin
Util.Val ((ExprTypes.ARRAY ((Util.slice lst i j)), st'))
end else begin
Util.Err ((FStar.String.strcat "Invalid slice bounds: " (ExprTypes.show tm)))
end
end
| _18_326 -> begin
Util.Err ((FStar.String.strcat "Slice of non-array argument: " (ExprTypes.show tm)))
end)
end)))
end
| ExprTypes.ARRAY (tlst) -> begin
(

let f = (fun ( _18_332  :  (ExprTypes.l__GExpr Prims.list * 'Astate) ) ( t  :  ExprTypes.l__GExpr ) -> (match (_18_332) with
| (acc, st) -> begin
(Util.bind (eval_rec (t, st) interp) (fun ( _18_336  :  'Astate config ) -> (match (_18_336) with
| (v, st') -> begin
(match (v) with
| ExprTypes.LOC (l) -> begin
Util.Val (((v)::acc, st'))
end
| _18_340 -> begin
Util.Err ((FStar.String.strcat "Array argument not boolean: " (ExprTypes.show t)))
end)
end)))
end))
in (Util.bind (Util.foldM f ([], st) tlst) (fun ( _18_343  :  (ExprTypes.l__GExpr Prims.list * 'Astate) ) -> (match (_18_343) with
| (llst, st') -> begin
Util.Val ((ExprTypes.ARRAY ((FStar.List.rev llst)), st'))
end))))
end
| ExprTypes.GET_ARRAY (t, i) -> begin
(Util.bind (eval_rec (t, st) interp) (fun ( _18_350  :  'Astate config ) -> (match (_18_350) with
| (v, st') -> begin
(match (v) with
| ExprTypes.ARRAY (lst) -> begin
if ((0 <= i) && (i < (FStar.List.length lst))) then begin
(match ((FStar.List.total_nth lst i)) with
| Some (ExprTypes.LOC (l)) -> begin
Util.Val ((ExprTypes.LOC (l), st'))
end
| Some (_18_357) -> begin
Util.Err ("Impossible")
end
| None -> begin
Util.Err ((FStar.String.strcat "Array out of bounds: " (ExprTypes.show tm)))
end)
end else begin
Util.Err ((FStar.String.strcat "Array out of bounds: " (ExprTypes.show tm)))
end
end
| _18_361 -> begin
Util.Err ((FStar.String.strcat "Invalid parameters: " (ExprTypes.show tm)))
end)
end)))
end
| ExprTypes.VAR (x) -> begin
Util.Val ((tm, st))
end
| ExprTypes.ASSERT (t) -> begin
(Util.bind (eval_rec (t, st) interp) (fun ( _18_368  :  'Astate config ) -> (match (_18_368) with
| (v, st') -> begin
(match (v) with
| ExprTypes.LOC (l) -> begin
Util.Val ((ExprTypes.UNIT, st'))
end
| _18_372 -> begin
Util.Err ((FStar.String.strcat "Assert of non-boolean argument: " (ExprTypes.show tm)))
end)
end)))
end
| ExprTypes.BEXP (bexp) -> begin
(

let _18_377 = (interp.alloc st bexp)
in (match (_18_377) with
| (l, st') -> begin
Util.Val ((ExprTypes.LOC (l), st'))
end))
end
| _18_379 -> begin
Util.Err ((FStar.String.strcat "Unimplemented case: " (ExprTypes.show tm)))
end)
end))
and eval_to_bexp = (fun ( _18_382  :  'Astate config ) ( interp  :  'Astate interpretation ) -> (match (_18_382) with
| (tm, st) -> begin
(match (tm) with
| ExprTypes.XOR (x, y) -> begin
(Util.bind (eval_to_bexp (x, st) interp) (fun ( _18_390  :  'Astate config ) -> (match (_18_390) with
| (x', st') -> begin
(Util.bind (eval_to_bexp (y, st') interp) (fun ( _18_393  :  'Astate config ) -> (match (_18_393) with
| (y', st'') -> begin
(match ((x', y')) with
| (ExprTypes.BEXP (b), ExprTypes.BEXP (b')) -> begin
Util.Val ((ExprTypes.BEXP (BoolExp.BXor ((b, b'))), st''))
end
| _18_400 -> begin
Util.Err ((FStar.String.strcat "Could not reduce parameters to booleans: " (ExprTypes.show tm)))
end)
end)))
end)))
end
| ExprTypes.AND (x, y) -> begin
(Util.bind (eval_to_bexp (x, st) interp) (fun ( _18_407  :  'Astate config ) -> (match (_18_407) with
| (x', st') -> begin
(Util.bind (eval_to_bexp (y, st') interp) (fun ( _18_410  :  'Astate config ) -> (match (_18_410) with
| (y', st'') -> begin
(match ((x', y')) with
| (ExprTypes.BEXP (b), ExprTypes.BEXP (b')) -> begin
Util.Val ((ExprTypes.BEXP (BoolExp.BAnd ((b, b'))), st''))
end
| _18_417 -> begin
Util.Err ((FStar.String.strcat "Could not reduce parameters to booleans: " (ExprTypes.show tm)))
end)
end)))
end)))
end
| ExprTypes.BOOL (b) -> begin
if b then begin
Util.Val ((ExprTypes.BEXP (BoolExp.BNot (BoolExp.BFalse)), st))
end else begin
Util.Val ((ExprTypes.BEXP (BoolExp.BFalse), st))
end
end
| _18_421 -> begin
(Util.bind (eval_rec (tm, st) interp) (fun ( _18_424  :  'Astate config ) -> (match (_18_424) with
| (v, st') -> begin
(match (v) with
| ExprTypes.LOC (l) -> begin
Util.Val ((ExprTypes.BEXP (BoolExp.BVar (l)), st'))
end
| _18_428 -> begin
Util.Err ((FStar.String.strcat "Could not reduce expression to boolean: " (ExprTypes.show tm)))
end)
end)))
end)
end))


type boolState =
(Prims.int * (Prims.int, Prims.bool) Total.map)


let boolInit : (Prims.int * (Prims.int  ->  Prims.bool)) = (0, (Total.const false))


let boolAlloc : boolState  ->  BoolExp.l__BoolExp  ->  (Prims.int * boolState) = (fun ( _18_431  :  boolState ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_18_431) with
| (top, st) -> begin
(top, ((top + 1), (Total.update st top (BoolExp.evalBexp bexp st))))
end))


let boolAssign : boolState  ->  Prims.int  ->  BoolExp.l__BoolExp  ->  boolState = (fun ( _18_435  :  boolState ) ( l  :  Prims.int ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_18_435) with
| (top, st) -> begin
(top, (Total.update st l (BoolExp.evalBexp bexp st)))
end))


let boolEval : boolState  ->  Total.state  ->  Prims.int  ->  Prims.bool = (fun ( _18_440  :  boolState ) ( ivals  :  Total.state ) ( i  :  Prims.int ) -> (match (_18_440) with
| (top, st) -> begin
(Total.lookup st i)
end))


let boolInterp : boolState interpretation = {alloc = boolAlloc; assign = boolAssign; eval = boolEval}


let rec substVal : ExprTypes.l__GExpr  ->  boolState  ->  ExprTypes.l__GExpr = (fun ( v  :  ExprTypes.l__GExpr ) ( st  :  boolState ) -> (match (v) with
| (ExprTypes.UNIT) | (ExprTypes.LAMBDA (_)) -> begin
v
end
| ExprTypes.LOC (l) -> begin
ExprTypes.BOOL ((Total.lookup (Prims.snd st) l))
end
| ExprTypes.ARRAY (lst) -> begin
ExprTypes.ARRAY ((substVal_lst lst st))
end))
and substVal_lst : ExprTypes.l__GExpr Prims.list  ->  boolState  ->  ExprTypes.l__GExpr Prims.list = (fun ( lst  :  ExprTypes.l__GExpr Prims.list ) ( st  :  boolState ) -> (match (lst) with
| [] -> begin
[]
end
| ExprTypes.LOC (l)::xs -> begin
(ExprTypes.BOOL ((Total.lookup (Prims.snd st) l)))::(substVal_lst xs st)
end))


let rec evalBool : (ExprTypes.l__GExpr * (Prims.int * (Prims.int  ->  Prims.bool)))  ->  Prims.string Prims.list = (fun ( _18_468  :  (ExprTypes.l__GExpr * (Prims.int * (Prims.int  ->  Prims.bool))) ) -> (match (_18_468) with
| (gexp, st) -> begin
if (isVal gexp) then begin
(ExprTypes.prettyPrint (substVal gexp st))
end else begin
(match ((step (gexp, st) boolInterp)) with
| Util.Err (s) -> begin
(s)::[]
end
| Util.Val (c') -> begin
(evalBool c')
end)
end
end))


let eval : ExprTypes.l__GExpr  ->  Prims.string Prims.list = (fun ( gexp  :  ExprTypes.l__GExpr ) -> (evalBool (gexp, boolInit)))


type l__BExpState =
(Prims.int * (Prims.int, BoolExp.l__BoolExp) Total.map)


let bexpInit : (Prims.int * (Prims.int  ->  BoolExp.l__BoolExp)) = (0, (Total.const BoolExp.BFalse))


let bexpAlloc : l__BExpState  ->  BoolExp.l__BoolExp  ->  (Prims.int * l__BExpState) = (fun ( _18_476  :  l__BExpState ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_18_476) with
| (top, st) -> begin
(top, ((top + 1), (Total.update st top (BoolExp.substBexp bexp st))))
end))


let bexpAssign : l__BExpState  ->  Prims.int  ->  BoolExp.l__BoolExp  ->  l__BExpState = (fun ( _18_480  :  l__BExpState ) ( l  :  Prims.int ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_18_480) with
| (top, st) -> begin
(top, (Total.update st l (BoolExp.substBexp bexp st)))
end))


let bexpEval : l__BExpState  ->  Total.state  ->  Prims.int  ->  Prims.bool = (fun ( _18_485  :  l__BExpState ) ( ivals  :  Total.state ) ( i  :  Prims.int ) -> (match (_18_485) with
| (top, st) -> begin
(BoolExp.evalBexp (Total.lookup st i) ivals)
end))


let bexpInterp : l__BExpState interpretation = {alloc = bexpAlloc; assign = bexpAssign; eval = bexpEval}


type l__CleanupStrategy =
| Pebbled
| Boundaries
| Bennett


let is_Pebbled = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| Pebbled (_) -> begin
true
end
| _ -> begin
false
end))


let is_Boundaries = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| Boundaries (_) -> begin
true
end
| _ -> begin
false
end))


let is_Bennett = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| Bennett (_) -> begin
true
end
| _ -> begin
false
end))


let simps : BoolExp.l__BoolExp  ->  BoolExp.l__BoolExp = (fun ( bexp  :  BoolExp.l__BoolExp ) -> (BoolExp.simplify (BoolExp.distributeAnds bexp)))


let rec allocN : (ExprTypes.l__GExpr Prims.list * l__BExpState)  ->  Prims.int  ->  (ExprTypes.l__GExpr Prims.list * l__BExpState) = (fun ( _18_494  :  (ExprTypes.l__GExpr Prims.list * l__BExpState) ) ( i  :  Prims.int ) -> (match (_18_494) with
| (locs, (top, st)) -> begin
if (i <= 0) then begin
((FStar.List.rev locs), (top, st))
end else begin
(allocN ((ExprTypes.LOC (top))::locs, ((top + 1), (Total.update st top (BoolExp.BVar (top))))) (i - 1))
end
end))


let allocTy : ExprTypes.l__GType  ->  l__BExpState  ->  (ExprTypes.l__GExpr * l__BExpState) Util.result = (fun ( ty  :  ExprTypes.l__GType ) ( _18_499  :  l__BExpState ) -> (match (_18_499) with
| (top, st) -> begin
(match (ty) with
| ExprTypes.GBool -> begin
Util.Val ((ExprTypes.LOC (top), ((top + 1), (Total.update st top (BoolExp.BVar (top))))))
end
| ExprTypes.GArray (n) -> begin
(

let _18_505 = (allocN ([], (top, st)) n)
in (match (_18_505) with
| (locs, st') -> begin
Util.Val ((ExprTypes.ARRAY (locs), st'))
end))
end
| _18_507 -> begin
Util.Err ("Invalid parameter type for circuit generation")
end)
end))


let rec lookupLst : ExprTypes.l__GExpr Prims.list  ->  l__BExpState  ->  BoolExp.l__BoolExp Prims.list = (fun ( lst  :  ExprTypes.l__GExpr Prims.list ) ( st  :  l__BExpState ) -> (match (lst) with
| [] -> begin
[]
end
| ExprTypes.LOC (l)::xs -> begin
((Total.lookup (Prims.snd st) l))::(lookupLst xs st)
end))


let foldPebble : (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list)  ->  BoolExp.l__BoolExp  ->  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list) = (fun ( _18_522  :  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list) ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_18_522) with
| (ah, outs, anc, circ) -> begin
(

let _18_528 = (BoolExp.compileBexpPebbled_oop ah (simps bexp))
in (match (_18_528) with
| (ah', res, anc', circ') -> begin
(ah', (res)::outs, (FStar.List.append anc' anc), (FStar.List.append circ circ'))
end))
end))


let foldClean : (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list)  ->  BoolExp.l__BoolExp  ->  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list) = (fun ( _18_533  :  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list) ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_18_533) with
| (ah, outs, anc, circ) -> begin
(

let _18_539 = (BoolExp.compileBexpClean_oop ah (simps bexp))
in (match (_18_539) with
| (ah', res, anc', circ') -> begin
(ah', (res)::outs, (FStar.List.append anc' anc), (FStar.List.append circ circ'))
end))
end))


let foldBennett : (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list * Circuit.l__Gate Prims.list)  ->  BoolExp.l__BoolExp  ->  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list * Circuit.l__Gate Prims.list) = (fun ( _18_545  :  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list * Circuit.l__Gate Prims.list) ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_18_545) with
| (ah, outs, anc, circ, ucirc) -> begin
(

let _18_551 = (BoolExp.compileBexp_oop ah (simps bexp))
in (match (_18_551) with
| (ah', res, anc', circ') -> begin
(ah', (res)::outs, (FStar.List.append anc' anc), (FStar.List.append circ circ'), (FStar.List.append (FStar.List.rev (Circuit.uncompute circ' res)) ucirc))
end))
end))


let rec compile : l__BExpState config  ->  l__CleanupStrategy  ->  (Prims.int Prims.list * Circuit.l__Gate Prims.list) Util.result = (fun ( _18_554  :  l__BExpState config ) ( strategy  :  l__CleanupStrategy ) -> (match (_18_554) with
| (gexp, st) -> begin
if (isVal gexp) then begin
(match (gexp) with
| ExprTypes.UNIT -> begin
Util.Val (([], []))
end
| ExprTypes.LAMBDA (x, ty, t) -> begin
(match ((allocTy ty st)) with
| Util.Err (s) -> begin
Util.Err (s)
end
| Util.Val (v, st') -> begin
(compile ((ExprTypes.substGExpr t x v), st') strategy)
end)
end
| ExprTypes.LOC (l) -> begin
(

let bexp = (Total.lookup (Prims.snd st) l)
in (

let max = (BoolExp.varMax bexp)
in (

let _18_579 = (match (strategy) with
| Pebbled -> begin
(BoolExp.compileBexpPebbled_oop (AncillaHeap.above (max + 1)) (simps bexp))
end
| Boundaries -> begin
(BoolExp.compileBexpClean_oop (AncillaHeap.above (max + 1)) (simps bexp))
end
| Bennett -> begin
(BoolExp.compileBexpClean_oop (AncillaHeap.above (max + 1)) (simps bexp))
end)
in (match (_18_579) with
| (ah, res, anc, circ) -> begin
Util.Val (((res)::[], circ))
end))))
end
| ExprTypes.ARRAY (lst) -> begin
(

let blst = (lookupLst lst st)
in (

let max = (BoolExp.listMax (FStar.List.mapT BoolExp.varMax blst))
in (

let _18_607 = (match (strategy) with
| Pebbled -> begin
(

let _18_589 = (FStar.List.fold_leftT foldPebble ((AncillaHeap.above (max + 1)), [], [], []) blst)
in (match (_18_589) with
| (ah, outs, anc, circ) -> begin
(ah, (FStar.List.rev outs), (FStar.List.rev anc), circ)
end))
end
| Boundaries -> begin
(

let _18_595 = (FStar.List.fold_leftT foldClean ((AncillaHeap.above (max + 1)), [], [], []) blst)
in (match (_18_595) with
| (ah, outs, anc, circ) -> begin
(ah, (FStar.List.rev outs), (FStar.List.rev anc), circ)
end))
end
| Bennett -> begin
(

let _18_602 = (FStar.List.fold_leftT foldBennett ((AncillaHeap.above (max + 1)), [], [], [], []) blst)
in (match (_18_602) with
| (ah, outs, anc, circ, ucirc) -> begin
(ah, (FStar.List.rev outs), (FStar.List.rev anc), (FStar.List.append circ ucirc))
end))
end)
in (match (_18_607) with
| (ah, outs, anc, circ) -> begin
Util.Val ((outs, circ))
end))))
end)
end else begin
(match ((step (gexp, st) bexpInterp)) with
| Util.Err (s) -> begin
Util.Err (s)
end
| Util.Val (c') -> begin
(compile c' strategy)
end)
end
end))


type circState =
{top : Prims.int; ah : AncillaHeap.l__AncHeap; gates : Circuit.l__Gate Prims.list; subs : (Prims.int, Prims.int) Total.map}


let is_MkcircState : circState  ->  Prims.bool = (Prims.checked_cast(fun ( _  :  circState ) -> (FStar.All.failwith "Not yet implemented:is_MkcircState")))


let circInit : circState = {top = 0; ah = AncillaHeap.emptyHeap; gates = []; subs = (Total.const 0)}


let circAlloc : circState  ->  BoolExp.l__BoolExp  ->  (Prims.int * circState) = (fun ( cs  :  circState ) ( bexp  :  BoolExp.l__BoolExp ) -> (

let _18_623 = (BoolExp.compileBexp_oop cs.ah (BoolExp.substVar bexp cs.subs))
in (match (_18_623) with
| (ah', res, ancs, circ') -> begin
(

let top' = (cs.top + 1)
in (

let gates' = (FStar.List.append cs.gates circ')
in (

let subs' = (Total.update cs.subs cs.top res)
in (cs.top, {top = top'; ah = ah'; gates = gates'; subs = subs'}))))
end)))


let circAssign : circState  ->  Prims.int  ->  BoolExp.l__BoolExp  ->  circState = (fun ( cs  :  circState ) ( l  :  Prims.int ) ( bexp  :  BoolExp.l__BoolExp ) -> (

let l' = (Total.lookup cs.subs l)
in (

let bexp' = (BoolExp.substVar bexp cs.subs)
in (

let _18_639 = (match ((BoolExp.factorAs bexp' l')) with
| None -> begin
(BoolExp.compileBexp_oop cs.ah bexp')
end
| Some (bexp'') -> begin
(BoolExp.compileBexp cs.ah l' bexp'')
end)
in (match (_18_639) with
| (ah', res, ancs, circ') -> begin
{top = cs.top; ah = ah'; gates = (FStar.List.append cs.gates circ'); subs = (Total.update cs.subs l res)}
end)))))


let circEval : circState  ->  Total.state  ->  Prims.int  ->  Prims.bool = (fun ( cs  :  circState ) ( ivals  :  Total.state ) ( i  :  Prims.int ) -> (Circuit.evalCirc cs.gates ivals (Total.lookup cs.subs i)))


let circInterp : circState interpretation = {alloc = circAlloc; assign = circAssign; eval = circEval}


let rec allocNcirc : (ExprTypes.l__GExpr Prims.list * circState)  ->  Prims.int  ->  (ExprTypes.l__GExpr Prims.list * circState) = (fun ( _18_646  :  (ExprTypes.l__GExpr Prims.list * circState) ) ( i  :  Prims.int ) -> (match (_18_646) with
| (locs, cs) -> begin
if (i <= 0) then begin
((FStar.List.rev locs), cs)
end else begin
(

let _18_650 = (AncillaHeap.popMin cs.ah)
in (match (_18_650) with
| (ah', res) -> begin
(

let cs' = {top = (cs.top + 1); ah = ah'; gates = cs.gates; subs = (Total.update cs.subs cs.top res)}
in (allocNcirc ((ExprTypes.LOC (cs.top))::locs, cs') (i - 1)))
end))
end
end))


let allocTycirc : ExprTypes.l__GType  ->  circState  ->  (ExprTypes.l__GExpr * circState) Util.result = (fun ( ty  :  ExprTypes.l__GType ) ( cs  :  circState ) -> (match (ty) with
| ExprTypes.GBool -> begin
(

let _18_657 = (AncillaHeap.popMin cs.ah)
in (match (_18_657) with
| (ah', res) -> begin
(

let cs' = {top = (cs.top + 1); ah = ah'; gates = cs.gates; subs = (Total.update cs.subs cs.top res)}
in Util.Val ((ExprTypes.LOC (cs.top), cs')))
end))
end
| ExprTypes.GArray (n) -> begin
(

let _18_663 = (allocNcirc ([], cs) n)
in (match (_18_663) with
| (locs, st') -> begin
Util.Val ((ExprTypes.ARRAY (locs), st'))
end))
end
| _18_665 -> begin
Util.Err ("Invalid parameter type for circuit generation")
end))


let rec lookup_Lst : (Prims.int, Prims.int) Total.map  ->  ExprTypes.l__GExpr Prims.list  ->  Prims.int Prims.list = (fun ( st  :  (Prims.int, Prims.int) Total.map ) ( lst  :  ExprTypes.l__GExpr Prims.list ) -> (match (lst) with
| [] -> begin
[]
end
| ExprTypes.LOC (l)::xs -> begin
((Total.lookup st l))::(lookup_Lst st xs)
end))


let rec compileCirc : circState config  ->  (Prims.int Prims.list * Circuit.l__Gate Prims.list) Util.result = (fun ( _18_678  :  circState config ) -> (match (_18_678) with
| (gexp, cs) -> begin
if (isVal gexp) then begin
(match (gexp) with
| ExprTypes.UNIT -> begin
Util.Val (([], []))
end
| ExprTypes.LAMBDA (x, ty, t) -> begin
(match ((allocTycirc ty cs)) with
| Util.Err (s) -> begin
Util.Err (s)
end
| Util.Val (v, cs') -> begin
(compileCirc ((ExprTypes.substGExpr t x v), cs'))
end)
end
| ExprTypes.LOC (l) -> begin
(

let res = (Total.lookup cs.subs l)
in Util.Val (((res)::[], cs.gates)))
end
| ExprTypes.ARRAY (lst) -> begin
(

let res = (lookup_Lst cs.subs lst)
in Util.Val ((res, cs.gates)))
end)
end else begin
(match ((step (gexp, cs) circInterp)) with
| Util.Err (s) -> begin
Util.Err (s)
end
| Util.Val (c') -> begin
(compileCirc c')
end)
end
end))


let rec eval_bexp_swap : boolState  ->  l__BExpState  ->  BoolExp.l__BoolExp  ->  Total.state  ->  Prims.unit = (fun ( st  :  boolState ) ( st'  :  l__BExpState ) ( bexp  :  BoolExp.l__BoolExp ) ( init  :  Total.state ) -> ())


let state_equiv_alloc : boolState  ->  l__BExpState  ->  Total.state  ->  BoolExp.l__BoolExp  ->  Prims.unit = (fun ( st  :  boolState ) ( st'  :  l__BExpState ) ( init  :  Total.state ) ( bexp  :  BoolExp.l__BoolExp ) -> ())


let state_equiv_assign : boolState  ->  l__BExpState  ->  Total.state  ->  Prims.int  ->  BoolExp.l__BoolExp  ->  Prims.unit = (fun ( st  :  boolState ) ( st'  :  l__BExpState ) ( init  :  Total.state ) ( l  :  Prims.int ) ( bexp  :  BoolExp.l__BoolExp ) -> ())


let rec state_equiv_step : ExprTypes.l__GExpr  ->  boolState  ->  l__BExpState  ->  Total.state  ->  Prims.unit = (fun ( gexp  :  ExprTypes.l__GExpr ) ( st  :  boolState ) ( st'  :  l__BExpState ) ( init  :  Total.state ) -> ())
and state_equiv_step_lst : ExprTypes.l__GExpr Prims.list  ->  boolState  ->  l__BExpState  ->  Total.state  ->  Prims.unit = (fun ( lst  :  ExprTypes.l__GExpr Prims.list ) ( st  :  boolState ) ( st'  :  l__BExpState ) ( init  :  Total.state ) -> ())


let rec eval_bexp_swap2 : boolState  ->  circState  ->  BoolExp.l__BoolExp  ->  BoolExp.l__BoolExp  ->  Total.state  ->  Prims.unit = (fun ( st  :  boolState ) ( cs  :  circState ) ( bexp  :  BoolExp.l__BoolExp ) ( bexp'  :  BoolExp.l__BoolExp ) ( init  :  Total.state ) -> ())


let eval_commutes_subst_circ : boolState  ->  circState  ->  BoolExp.l__BoolExp  ->  BoolExp.l__BoolExp  ->  Total.state  ->  Prims.int  ->  Prims.int  ->  Prims.unit = (fun ( st  :  boolState ) ( cs  :  circState ) ( bexp  :  BoolExp.l__BoolExp ) ( bexp'  :  BoolExp.l__BoolExp ) ( init  :  Total.state ) ( targ  :  Prims.int ) ( targ'  :  Prims.int ) -> ())


let eval_commutes_subst_circ_oop : boolState  ->  circState  ->  BoolExp.l__BoolExp  ->  BoolExp.l__BoolExp  ->  Total.state  ->  Prims.unit = (fun ( st  :  boolState ) ( cs  :  circState ) ( bexp  :  BoolExp.l__BoolExp ) ( bexp'  :  BoolExp.l__BoolExp ) ( init  :  Total.state ) -> ())


let circ_equiv_alloc : boolState  ->  circState  ->  Total.state  ->  BoolExp.l__BoolExp  ->  Prims.unit = (fun ( st  :  boolState ) ( cs  :  circState ) ( init  :  Total.state ) ( bexp  :  BoolExp.l__BoolExp ) -> ())


let circ_equiv_assign : boolState  ->  circState  ->  Total.state  ->  Prims.int  ->  BoolExp.l__BoolExp  ->  Prims.unit = (fun ( st  :  boolState ) ( cs  :  circState ) ( init  :  Total.state ) ( l  :  Prims.int ) ( bexp  :  BoolExp.l__BoolExp ) -> ())


let rec circ_equiv_step : ExprTypes.l__GExpr  ->  boolState  ->  circState  ->  Total.state  ->  Prims.unit = (fun ( gexp  :  ExprTypes.l__GExpr ) ( st  :  boolState ) ( st'  :  circState ) ( init  :  Total.state ) -> ())
and circ_equiv_step_lst : ExprTypes.l__GExpr Prims.list  ->  boolState  ->  circState  ->  Total.state  ->  Prims.unit = (fun ( lst  :  ExprTypes.l__GExpr Prims.list ) ( st  :  boolState ) ( st'  :  circState ) ( init  :  Total.state ) -> ())




