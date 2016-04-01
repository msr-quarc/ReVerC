#light "off"
module Interpreter
open Prims

type 'Astate interpretation =
{alloc : 'Astate  ->  BoolExp.l__BoolExp  ->  (Prims.int * 'Astate); assign : 'Astate  ->  Prims.int  ->  BoolExp.l__BoolExp  ->  'Astate; eval : 'Astate  ->  Total.state  ->  Prims.int  ->  Prims.bool}


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
| _21_20 -> begin
false
end))
and isVal_lst : ExprTypes.l__GExpr Prims.list  ->  Prims.bool = (fun ( lst  :  ExprTypes.l__GExpr Prims.list ) -> (match (lst) with
| [] -> begin
true
end
| ExprTypes.LOC (l)::xs -> begin
(isVal_lst xs)
end
| _21_28 -> begin
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
| _21_37 -> begin
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


let rec step = (fun ( _21_57  :  'Astate config ) ( interp  :  'Astate interpretation ) -> (match (_21_57) with
| (tm, st) -> begin
(match (tm) with
| ExprTypes.LET (x, t1, t2) -> begin
if (isVal t1) then begin
Util.Val (((ExprTypes.substGExpr t2 x t1), st))
end else begin
(Util.bindT (step (t1, st) interp) (fun ( _21_66  :  'Astate config ) -> (match (_21_66) with
| (t1', st') -> begin
Util.Val ((ExprTypes.LET ((x, t1', t2)), st'))
end)))
end
end
| ExprTypes.APPLY (t1, t2) -> begin
if (not ((isVal t1))) then begin
(Util.bindT (step (t1, st) interp) (fun ( _21_73  :  'Astate config ) -> (match (_21_73) with
| (t1', st') -> begin
Util.Val ((ExprTypes.APPLY ((t1', t2)), st'))
end)))
end else begin
if (not ((isVal t2))) then begin
(Util.bindT (step (t2, st) interp) (fun ( _21_76  :  'Astate config ) -> (match (_21_76) with
| (t2', st') -> begin
Util.Val ((ExprTypes.APPLY ((t1, t2')), st'))
end)))
end else begin
(match (t1) with
| ExprTypes.LAMBDA (x, ty, t) -> begin
Util.Val (((ExprTypes.substGExpr t x t2), st))
end
| _21_83 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce application: " (ExprTypes.show tm)))
end)
end
end
end
| ExprTypes.SEQUENCE (t1, t2) -> begin
if (not ((isVal t1))) then begin
(Util.bindT (step (t1, st) interp) (fun ( _21_90  :  'Astate config ) -> (match (_21_90) with
| (t1', st') -> begin
Util.Val ((ExprTypes.SEQUENCE ((t1', t2)), st'))
end)))
end else begin
(match (t1) with
| ExprTypes.UNIT -> begin
Util.Val ((t2, st))
end
| _21_93 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce sequence: " (ExprTypes.show tm)))
end)
end
end
| ExprTypes.ASSIGN (t1, t2) -> begin
if (not ((isVal t1))) then begin
(Util.bindT (step (t1, st) interp) (fun ( _21_100  :  'Astate config ) -> (match (_21_100) with
| (t1', st') -> begin
Util.Val ((ExprTypes.ASSIGN ((t1', t2)), st'))
end)))
end else begin
if (not ((isBexp t2))) then begin
(Util.bindT (step (t2, st) interp) (fun ( _21_103  :  'Astate config ) -> (match (_21_103) with
| (t2', st') -> begin
Util.Val ((ExprTypes.ASSIGN ((t1, t2')), st'))
end)))
end else begin
(match (t1) with
| ExprTypes.LOC (l) -> begin
Util.Val ((ExprTypes.UNIT, (interp.assign st l (get_bexp t2))))
end
| _21_107 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce assignment: " (ExprTypes.show tm)))
end)
end
end
end
| ExprTypes.XOR (t1, t2) -> begin
if (not ((isBexp t1))) then begin
(Util.bindT (step (t1, st) interp) (fun ( _21_114  :  'Astate config ) -> (match (_21_114) with
| (t1', st') -> begin
Util.Val ((ExprTypes.XOR ((t1', t2)), st'))
end)))
end else begin
if (not ((isBexp t2))) then begin
(Util.bindT (step (t2, st) interp) (fun ( _21_117  :  'Astate config ) -> (match (_21_117) with
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
(Util.bindT (step (t1, st) interp) (fun ( _21_124  :  'Astate config ) -> (match (_21_124) with
| (t1', st') -> begin
Util.Val ((ExprTypes.AND ((t1', t2)), st'))
end)))
end else begin
if (not ((isBexp t2))) then begin
(Util.bindT (step (t2, st) interp) (fun ( _21_127  :  'Astate config ) -> (match (_21_127) with
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
(Util.bindT (step (t1, st) interp) (fun ( _21_137  :  'Astate config ) -> (match (_21_137) with
| (t1', st') -> begin
Util.Val ((ExprTypes.APPLY ((t1', t2)), st'))
end)))
end else begin
if (not ((isVal t2))) then begin
(Util.bindT (step (t2, st) interp) (fun ( _21_140  :  'Astate config ) -> (match (_21_140) with
| (t2', st') -> begin
Util.Val ((ExprTypes.APPLY ((t1, t2')), st'))
end)))
end else begin
(match ((t1, t2)) with
| (ExprTypes.ARRAY (l), ExprTypes.ARRAY (l')) -> begin
Util.Val ((ExprTypes.ARRAY ((FStar.List.append l l')), st))
end
| _21_147 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce append: " (ExprTypes.show tm)))
end)
end
end
end
| ExprTypes.ROT (i, t) -> begin
if (not ((isVal t))) then begin
(Util.bindT (step (t, st) interp) (fun ( _21_154  :  'Astate config ) -> (match (_21_154) with
| (t', st') -> begin
Util.Val ((ExprTypes.ROT ((i, t')), st'))
end)))
end else begin
(match (t) with
| ExprTypes.ARRAY (lst) -> begin
if (((Prims.parse_int "0") <= i) && (i < (FStar.List.length lst))) then begin
Util.Val ((ExprTypes.ARRAY ((Util.rotate lst i)), st))
end else begin
Util.Err ((FStar.String.strcat "Array out of bounds: " (ExprTypes.show tm)))
end
end
| _21_158 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce rotation: " (ExprTypes.show tm)))
end)
end
end
| ExprTypes.SLICE (t, i, j) -> begin
if (not ((isVal t))) then begin
(Util.bindT (step (t, st) interp) (fun ( _21_166  :  'Astate config ) -> (match (_21_166) with
| (t', st') -> begin
Util.Val ((ExprTypes.SLICE ((t', i, j)), st'))
end)))
end else begin
(match (t) with
| ExprTypes.ARRAY (lst) -> begin
if ((((Prims.parse_int "0") <= i) && (i <= j)) && (j < (FStar.List.length lst))) then begin
Util.Val ((ExprTypes.ARRAY ((Util.slice lst i j)), st))
end else begin
Util.Err ((FStar.String.strcat "Array out of bounds: " (ExprTypes.show tm)))
end
end
| _21_170 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce slice: " (ExprTypes.show tm)))
end)
end
end
| ExprTypes.ARRAY (lst) -> begin
(Util.bindT (step_lst (lst, st) interp) (fun ( _21_175  :  'Astate listconfig ) -> (match (_21_175) with
| (lst, st') -> begin
Util.Val ((ExprTypes.ARRAY (lst), st'))
end)))
end
| ExprTypes.GET_ARRAY (t, i) -> begin
if (not ((isVal t))) then begin
(Util.bindT (step (t, st) interp) (fun ( _21_182  :  'Astate config ) -> (match (_21_182) with
| (t', st') -> begin
Util.Val ((ExprTypes.GET_ARRAY ((t', i)), st'))
end)))
end else begin
(match (t) with
| ExprTypes.ARRAY (lst) -> begin
if (((Prims.parse_int "0") <= i) && (i < (FStar.List.length lst))) then begin
Util.Val (((Util.nthT lst i), st))
end else begin
Util.Err ((FStar.String.strcat "Array out of bounds: " (ExprTypes.show tm)))
end
end
| _21_186 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce array index: " (ExprTypes.show tm)))
end)
end
end
| ExprTypes.ASSERT (t) -> begin
if (not ((isVal t))) then begin
(Util.bindT (step (t, st) interp) (fun ( _21_191  :  'Astate config ) -> (match (_21_191) with
| (t', st') -> begin
Util.Val ((ExprTypes.ASSERT (t'), st'))
end)))
end else begin
(match (t) with
| ExprTypes.LOC (l) -> begin
Util.Val ((ExprTypes.UNIT, st))
end
| _21_195 -> begin
Util.Err ((FStar.String.strcat "Cannot reduce assertion: " (ExprTypes.show tm)))
end)
end
end
| ExprTypes.BEXP (bexp) -> begin
(

let _21_200 = (interp.alloc st bexp)
in (match (_21_200) with
| (l, st') -> begin
Util.Val ((ExprTypes.LOC (l), st'))
end))
end
| _21_202 -> begin
Util.Err ((FStar.String.strcat "No rule applies: " (ExprTypes.show tm)))
end)
end))
and step_lst = (fun ( _21_205  :  'Astate listconfig ) ( interp  :  'Astate interpretation ) -> (match (_21_205) with
| (lst, st) -> begin
(match (lst) with
| [] -> begin
Util.Val (([], st))
end
| x::xs -> begin
if (not ((isVal x))) then begin
(Util.bindT (step (x, st) interp) (fun ( _21_213  :  'Astate config ) -> (match (_21_213) with
| (x', st') -> begin
Util.Val (((x')::xs, st'))
end)))
end else begin
(Util.bindT (step_lst (xs, st) interp) (fun ( _21_216  :  'Astate listconfig ) -> (match (_21_216) with
| (xs', st') -> begin
Util.Val (((x)::xs', st'))
end)))
end
end)
end))


let rec eval_rec = (fun ( _21_221  :  'Astate config ) ( interp  :  'Astate interpretation ) -> (match (_21_221) with
| (tm, st) -> begin
(match (tm) with
| ExprTypes.LET (x, t1, t2) -> begin
(Util.bind (eval_rec (t1, st) interp) (fun ( _21_230  :  'Astate config ) -> (match (_21_230) with
| (v1, st') -> begin
(eval_rec ((ExprTypes.substGExpr t2 x v1), st') interp)
end)))
end
| ExprTypes.LAMBDA (x, ty, t) -> begin
Util.Val ((tm, st))
end
| ExprTypes.APPLY (t1, t2) -> begin
(Util.bind (eval_rec (t1, st) interp) (fun ( _21_242  :  'Astate config ) -> (match (_21_242) with
| (v1, st') -> begin
(Util.bind (eval_rec (t2, st') interp) (fun ( _21_245  :  'Astate config ) -> (match (_21_245) with
| (v2, st'') -> begin
(match (v1) with
| ExprTypes.LAMBDA (x, ty, t) -> begin
(eval_rec ((ExprTypes.substGExpr t x v2), st'') interp)
end
| _21_252 -> begin
Util.Err ((FStar.String.strcat "LHS is not a lambda: " (ExprTypes.show tm)))
end)
end)))
end)))
end
| ExprTypes.SEQUENCE (t1, t2) -> begin
(Util.bind (eval_rec (t1, st) interp) (fun ( _21_259  :  'Astate config ) -> (match (_21_259) with
| (v1, st') -> begin
(eval_rec (t2, st') interp)
end)))
end
| ExprTypes.ASSIGN (t1, t2) -> begin
(Util.bind (eval_rec (t1, st) interp) (fun ( _21_266  :  'Astate config ) -> (match (_21_266) with
| (v1, st') -> begin
(Util.bind (eval_rec (t2, st') interp) (fun ( _21_269  :  'Astate config ) -> (match (_21_269) with
| (v2, st'') -> begin
(match ((v1, v2)) with
| (ExprTypes.LOC (l), ExprTypes.BEXP (bexp)) -> begin
Util.Val ((ExprTypes.UNIT, (interp.assign st' l bexp)))
end
| _21_276 -> begin
Util.Err ((FStar.String.strcat "Invalid parameters: " (ExprTypes.show tm)))
end)
end)))
end)))
end
| (ExprTypes.XOR (_)) | (ExprTypes.AND (_)) | (ExprTypes.BOOL (_)) -> begin
(Util.bind (eval_to_bexp (tm, st) interp) (fun ( c  :  'Astate config ) -> (eval_rec c interp)))
end
| ExprTypes.APPEND (t1, t2) -> begin
(Util.bind (eval_rec (t1, st) interp) (fun ( _21_293  :  'Astate config ) -> (match (_21_293) with
| (v1, st') -> begin
(Util.bind (eval_rec (t2, st') interp) (fun ( _21_296  :  'Astate config ) -> (match (_21_296) with
| (v2, st'') -> begin
(match ((v1, v2)) with
| (ExprTypes.ARRAY (l1), ExprTypes.ARRAY (l2)) -> begin
Util.Val ((ExprTypes.ARRAY ((FStar.List.append l1 l2)), st''))
end
| _21_303 -> begin
Util.Err ((FStar.String.strcat "Append of non-array argument: " (ExprTypes.show tm)))
end)
end)))
end)))
end
| ExprTypes.ROT (i, t) -> begin
(Util.bind (eval_rec (t, st) interp) (fun ( _21_310  :  'Astate config ) -> (match (_21_310) with
| (v, st') -> begin
(match (v) with
| ExprTypes.ARRAY (lst) -> begin
if (((Prims.parse_int "0") <= i) && (i < (FStar.List.length lst))) then begin
Util.Val ((ExprTypes.ARRAY ((Util.rotate lst i)), st'))
end else begin
Util.Err ((FStar.String.strcat "Rotation out of array bounds: " (ExprTypes.show tm)))
end
end
| _21_314 -> begin
Util.Err ((FStar.String.strcat "Rotation of non-array argument: " (ExprTypes.show tm)))
end)
end)))
end
| ExprTypes.SLICE (t, i, j) -> begin
(Util.bind (eval_rec (t, st) interp) (fun ( _21_322  :  'Astate config ) -> (match (_21_322) with
| (v, st') -> begin
(match (v) with
| ExprTypes.ARRAY (lst) -> begin
if ((((Prims.parse_int "0") <= i) && (i <= j)) && (j < (FStar.List.length lst))) then begin
Util.Val ((ExprTypes.ARRAY ((Util.slice lst i j)), st'))
end else begin
Util.Err ((FStar.String.strcat "Invalid slice bounds: " (ExprTypes.show tm)))
end
end
| _21_326 -> begin
Util.Err ((FStar.String.strcat "Slice of non-array argument: " (ExprTypes.show tm)))
end)
end)))
end
| ExprTypes.ARRAY (tlst) -> begin
(

let f = (fun ( _21_332  :  (ExprTypes.l__GExpr Prims.list * 'Astate) ) ( t  :  ExprTypes.l__GExpr ) -> (match (_21_332) with
| (acc, st) -> begin
(Util.bind (eval_rec (t, st) interp) (fun ( _21_336  :  'Astate config ) -> (match (_21_336) with
| (v, st') -> begin
(match (v) with
| ExprTypes.LOC (l) -> begin
Util.Val (((v)::acc, st'))
end
| _21_340 -> begin
Util.Err ((FStar.String.strcat "Array argument not boolean: " (ExprTypes.show t)))
end)
end)))
end))
in (Util.bind (Util.foldM f ([], st) tlst) (fun ( _21_343  :  (ExprTypes.l__GExpr Prims.list * 'Astate) ) -> (match (_21_343) with
| (llst, st') -> begin
Util.Val ((ExprTypes.ARRAY ((FStar.List.rev llst)), st'))
end))))
end
| ExprTypes.GET_ARRAY (t, i) -> begin
(Util.bind (eval_rec (t, st) interp) (fun ( _21_350  :  'Astate config ) -> (match (_21_350) with
| (v, st') -> begin
(match (v) with
| ExprTypes.ARRAY (lst) -> begin
if (((Prims.parse_int "0") <= i) && (i < (FStar.List.length lst))) then begin
(match ((FStar.List.nth lst i)) with
| ExprTypes.LOC (l) -> begin
Util.Val ((ExprTypes.LOC (l), st'))
end
| _ -> begin
Util.Err ((FStar.String.strcat "Array out of bounds: " (ExprTypes.show tm)))
end)
end else begin
Util.Err ((FStar.String.strcat "Array out of bounds: " (ExprTypes.show tm)))
end
end
| _21_361 -> begin
Util.Err ((FStar.String.strcat "Invalid parameters: " (ExprTypes.show tm)))
end)
end)))
end
| ExprTypes.VAR (x) -> begin
Util.Val ((tm, st))
end
| ExprTypes.ASSERT (t) -> begin
(Util.bind (eval_rec (t, st) interp) (fun ( _21_368  :  'Astate config ) -> (match (_21_368) with
| (v, st') -> begin
(match (v) with
| ExprTypes.LOC (l) -> begin
Util.Val ((ExprTypes.UNIT, st'))
end
| _21_372 -> begin
Util.Err ((FStar.String.strcat "Assert of non-boolean argument: " (ExprTypes.show tm)))
end)
end)))
end
| ExprTypes.BEXP (bexp) -> begin
(

let _21_377 = (interp.alloc st bexp)
in (match (_21_377) with
| (l, st') -> begin
Util.Val ((ExprTypes.LOC (l), st'))
end))
end
| _21_379 -> begin
Util.Err ((FStar.String.strcat "Unimplemented case: " (ExprTypes.show tm)))
end)
end))
and eval_to_bexp = (fun ( _21_382  :  'Astate config ) ( interp  :  'Astate interpretation ) -> (match (_21_382) with
| (tm, st) -> begin
(match (tm) with
| ExprTypes.XOR (x, y) -> begin
(Util.bind (eval_to_bexp (x, st) interp) (fun ( _21_390  :  'Astate config ) -> (match (_21_390) with
| (x', st') -> begin
(Util.bind (eval_to_bexp (y, st') interp) (fun ( _21_393  :  'Astate config ) -> (match (_21_393) with
| (y', st'') -> begin
(match ((x', y')) with
| (ExprTypes.BEXP (b), ExprTypes.BEXP (b')) -> begin
Util.Val ((ExprTypes.BEXP (BoolExp.BXor ((b, b'))), st''))
end
| _21_400 -> begin
Util.Err ((FStar.String.strcat "Could not reduce parameters to booleans: " (ExprTypes.show tm)))
end)
end)))
end)))
end
| ExprTypes.AND (x, y) -> begin
(Util.bind (eval_to_bexp (x, st) interp) (fun ( _21_407  :  'Astate config ) -> (match (_21_407) with
| (x', st') -> begin
(Util.bind (eval_to_bexp (y, st') interp) (fun ( _21_410  :  'Astate config ) -> (match (_21_410) with
| (y', st'') -> begin
(match ((x', y')) with
| (ExprTypes.BEXP (b), ExprTypes.BEXP (b')) -> begin
Util.Val ((ExprTypes.BEXP (BoolExp.BAnd ((b, b'))), st''))
end
| _21_417 -> begin
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
| _21_421 -> begin
(Util.bind (eval_rec (tm, st) interp) (fun ( _21_424  :  'Astate config ) -> (match (_21_424) with
| (v, st') -> begin
(match (v) with
| ExprTypes.LOC (l) -> begin
Util.Val ((ExprTypes.BEXP (BoolExp.BVar (l)), st'))
end
| _21_428 -> begin
Util.Err ((FStar.String.strcat "Could not reduce expression to boolean: " (ExprTypes.show tm)))
end)
end)))
end)
end))


type boolState =
(Prims.int * (Prims.int, Prims.bool) Total.map)


let boolInit : (Prims.int * (Prims.int  ->  Prims.bool)) = ((Prims.parse_int "0"), (Total.const_map false))


let boolAlloc : boolState  ->  BoolExp.l__BoolExp  ->  (Prims.int * boolState) = (fun ( _21_431  :  boolState ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_21_431) with
| (top, st) -> begin
(top, ((top + (Prims.parse_int "1")), (Total.update st top (BoolExp.evalBexp bexp st))))
end))


let boolAssign : boolState  ->  Prims.int  ->  BoolExp.l__BoolExp  ->  boolState = (fun ( _21_435  :  boolState ) ( l  :  Prims.int ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_21_435) with
| (top, st) -> begin
(top, (Total.update st l (BoolExp.evalBexp bexp st)))
end))


let boolEval : boolState  ->  Total.state  ->  Prims.int  ->  Prims.bool = (fun ( _21_440  :  boolState ) ( ivals  :  Total.state ) ( i  :  Prims.int ) -> (match (_21_440) with
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


let rec evalBool : (ExprTypes.l__GExpr * (Prims.int * (Prims.int  ->  Prims.bool)))  ->  Prims.string Prims.list = (fun ( _21_468  :  (ExprTypes.l__GExpr * (Prims.int * (Prims.int  ->  Prims.bool))) ) -> (match (_21_468) with
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


let bexpInit : (Prims.int * (Prims.int  ->  BoolExp.l__BoolExp)) = ((Prims.parse_int "0"), (Total.const_map BoolExp.BFalse))


let bexpAlloc : l__BExpState  ->  BoolExp.l__BoolExp  ->  (Prims.int * l__BExpState) = (fun ( _21_476  :  l__BExpState ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_21_476) with
| (top, st) -> begin
(top, ((top + (Prims.parse_int "1")), (Total.update st top (BoolExp.substBexp bexp st))))
end))


let bexpAssign : l__BExpState  ->  Prims.int  ->  BoolExp.l__BoolExp  ->  l__BExpState = (fun ( _21_480  :  l__BExpState ) ( l  :  Prims.int ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_21_480) with
| (top, st) -> begin
(top, (Total.update st l (BoolExp.substBexp bexp st)))
end))


let bexpEval : l__BExpState  ->  Total.state  ->  Prims.int  ->  Prims.bool = (fun ( _21_485  :  l__BExpState ) ( ivals  :  Total.state ) ( i  :  Prims.int ) -> (match (_21_485) with
| (top, st) -> begin
(BoolExp.evalBexp (Total.lookup st i) ivals)
end))


let bexpInterp : l__BExpState interpretation = {alloc = bexpAlloc; assign = bexpAssign; eval = bexpEval}


type l__CleanupStrategy =
| Pebbled
| Boundaries
| Bennett


let is_Pebbled = (fun ( _discr_  :  l__CleanupStrategy ) -> (match (_discr_) with
| Pebbled (_) -> begin
true
end
| _ -> begin
false
end))


let is_Boundaries = (fun ( _discr_  :  l__CleanupStrategy ) -> (match (_discr_) with
| Boundaries (_) -> begin
true
end
| _ -> begin
false
end))


let is_Bennett = (fun ( _discr_  :  l__CleanupStrategy ) -> (match (_discr_) with
| Bennett (_) -> begin
true
end
| _ -> begin
false
end))


let simps : BoolExp.l__BoolExp  ->  BoolExp.l__BoolExp = (fun ( bexp  :  BoolExp.l__BoolExp ) -> (BoolExp.simplify (BoolExp.distributeAnds bexp)))


let rec allocN : (ExprTypes.l__GExpr Prims.list * l__BExpState)  ->  Prims.int  ->  (ExprTypes.l__GExpr Prims.list * l__BExpState) = (fun ( _21_494  :  (ExprTypes.l__GExpr Prims.list * l__BExpState) ) ( i  :  Prims.int ) -> (match (_21_494) with
| (locs, (top, st)) -> begin
if (i <= (Prims.parse_int "0")) then begin
((FStar.List.rev locs), (top, st))
end else begin
(allocN ((ExprTypes.LOC (top))::locs, ((top + (Prims.parse_int "1")), (Total.update st top (BoolExp.BVar (top))))) (i - (Prims.parse_int "1")))
end
end))


let allocTy : ExprTypes.l__GType  ->  l__BExpState  ->  (ExprTypes.l__GExpr * l__BExpState) Util.result = (fun ( ty  :  ExprTypes.l__GType ) ( _21_499  :  l__BExpState ) -> (match (_21_499) with
| (top, st) -> begin
(match (ty) with
| ExprTypes.GBool -> begin
Util.Val ((ExprTypes.LOC (top), ((top + (Prims.parse_int "1")), (Total.update st top (BoolExp.BVar (top))))))
end
| ExprTypes.GArray (n) -> begin
(

let _21_505 = (allocN ([], (top, st)) n)
in (match (_21_505) with
| (locs, st') -> begin
Util.Val ((ExprTypes.ARRAY (locs), st'))
end))
end
| _21_507 -> begin
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


let foldPebble : (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list)  ->  BoolExp.l__BoolExp  ->  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list) = (fun ( _21_522  :  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list) ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_21_522) with
| (ah, outs, anc, circ) -> begin
(

let _21_528 = (BoolExp.compileBexpPebbled_oop ah (simps bexp))
in (match (_21_528) with
| (ah', res, anc', circ') -> begin
(ah', (res)::outs, (FStar.List.append anc' anc), (FStar.List.append circ circ'))
end))
end))


let foldClean : (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list)  ->  BoolExp.l__BoolExp  ->  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list) = (fun ( _21_533  :  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list) ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_21_533) with
| (ah, outs, anc, circ) -> begin
(

let _21_539 = (BoolExp.compileBexpClean_oop ah (simps bexp))
in (match (_21_539) with
| (ah', res, anc', circ') -> begin
(ah', (res)::outs, (FStar.List.append anc' anc), (FStar.List.append circ circ'))
end))
end))


let foldBennett : (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list * Circuit.l__Gate Prims.list)  ->  BoolExp.l__BoolExp  ->  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list * Circuit.l__Gate Prims.list) = (fun ( _21_545  :  (AncillaHeap.l__AncHeap * Prims.int Prims.list * Prims.int Prims.list * Circuit.l__Gate Prims.list * Circuit.l__Gate Prims.list) ) ( bexp  :  BoolExp.l__BoolExp ) -> (match (_21_545) with
| (ah, outs, anc, circ, ucirc) -> begin
(

let _21_551 = (BoolExp.compileBexp_oop ah (simps bexp))
in (match (_21_551) with
| (ah', res, anc', circ') -> begin
(ah', (res)::outs, (FStar.List.append anc' anc), (FStar.List.append circ circ'), (FStar.List.append (FStar.List.rev (Circuit.uncompute circ' res)) ucirc))
end))
end))


let rec compile : l__BExpState config  ->  l__CleanupStrategy  ->  (Prims.int Prims.list * Circuit.l__Gate Prims.list) Util.result = (fun ( _21_554  :  l__BExpState config ) ( strategy  :  l__CleanupStrategy ) -> (match (_21_554) with
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

let _21_579 = (match (strategy) with
| Pebbled -> begin
(BoolExp.compileBexpPebbled_oop (AncillaHeap.above (max + (Prims.parse_int "1"))) (simps bexp))
end
| Boundaries -> begin
(BoolExp.compileBexpClean_oop (AncillaHeap.above (max + (Prims.parse_int "1"))) (simps bexp))
end
| Bennett -> begin
(BoolExp.compileBexpClean_oop (AncillaHeap.above (max + (Prims.parse_int "1"))) (simps bexp))
end)
in (match (_21_579) with
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

let _21_607 = (match (strategy) with
| Pebbled -> begin
(

let _21_589 = (FStar.List.fold_left foldPebble ((AncillaHeap.above (max + (Prims.parse_int "1"))), [], [], []) blst)
in (match (_21_589) with
| (ah, outs, anc, circ) -> begin
(ah, (FStar.List.rev outs), (FStar.List.rev anc), circ)
end))
end
| Boundaries -> begin
(

let _21_595 = (FStar.List.fold_left foldClean ((AncillaHeap.above (max + (Prims.parse_int "1"))), [], [], []) blst)
in (match (_21_595) with
| (ah, outs, anc, circ) -> begin
(ah, (FStar.List.rev outs), (FStar.List.rev anc), circ)
end))
end
| Bennett -> begin
(

let _21_602 = (FStar.List.fold_left foldBennett ((AncillaHeap.above (max + (Prims.parse_int "1"))), [], [], [], []) blst)
in (match (_21_602) with
| (ah, outs, anc, circ, ucirc) -> begin
(ah, (FStar.List.rev outs), (FStar.List.rev anc), (FStar.List.append circ ucirc))
end))
end)
in (match (_21_607) with
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


let circInit : circState = {top = (Prims.parse_int "0"); ah = AncillaHeap.emptyHeap; gates = []; subs = (Total.const_map (Prims.parse_int "0"))}


let circAlloc : circState  ->  BoolExp.l__BoolExp  ->  (Prims.int * circState) = (fun ( cs  :  circState ) ( bexp  :  BoolExp.l__BoolExp ) -> (

let _21_623 = (BoolExp.compileBexp_oop cs.ah (BoolExp.substVar bexp cs.subs))
in (match (_21_623) with
| (ah', res, ancs, circ') -> begin
(

let top' = (cs.top + (Prims.parse_int "1"))
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

let _21_639 = (match ((BoolExp.factorAs bexp' l')) with
| None -> begin
(BoolExp.compileBexp_oop cs.ah bexp')
end
| Some (bexp'') -> begin
(BoolExp.compileBexp cs.ah l' bexp'')
end)
in (match (_21_639) with
| (ah', res, ancs, circ') -> begin
{top = cs.top; ah = ah'; gates = (FStar.List.append cs.gates circ'); subs = (Total.update cs.subs l res)}
end)))))


let circEval : circState  ->  Total.state  ->  Prims.int  ->  Prims.bool = (fun ( cs  :  circState ) ( ivals  :  Total.state ) ( i  :  Prims.int ) -> (Circuit.evalCirc cs.gates ivals (Total.lookup cs.subs i)))


let circInterp : circState interpretation = {alloc = circAlloc; assign = circAssign; eval = circEval}


let rec allocNcirc : (ExprTypes.l__GExpr Prims.list * circState)  ->  Prims.int  ->  (ExprTypes.l__GExpr Prims.list * circState) = (fun ( _21_646  :  (ExprTypes.l__GExpr Prims.list * circState) ) ( i  :  Prims.int ) -> (match (_21_646) with
| (locs, cs) -> begin
if (i <= (Prims.parse_int "0")) then begin
((FStar.List.rev locs), cs)
end else begin
(

let _21_650 = (AncillaHeap.popMin cs.ah)
in (match (_21_650) with
| (ah', res) -> begin
(

let cs' = {top = (cs.top + (Prims.parse_int "1")); ah = ah'; gates = cs.gates; subs = (Total.update cs.subs cs.top res)}
in (allocNcirc ((ExprTypes.LOC (cs.top))::locs, cs') (i - (Prims.parse_int "1"))))
end))
end
end))


let allocTycirc : ExprTypes.l__GType  ->  circState  ->  (ExprTypes.l__GExpr * circState) Util.result = (fun ( ty  :  ExprTypes.l__GType ) ( cs  :  circState ) -> (match (ty) with
| ExprTypes.GBool -> begin
(

let _21_657 = (AncillaHeap.popMin cs.ah)
in (match (_21_657) with
| (ah', res) -> begin
(

let cs' = {top = (cs.top + (Prims.parse_int "1")); ah = ah'; gates = cs.gates; subs = (Total.update cs.subs cs.top res)}
in Util.Val ((ExprTypes.LOC (cs.top), cs')))
end))
end
| ExprTypes.GArray (n) -> begin
(

let _21_663 = (allocNcirc ([], cs) n)
in (match (_21_663) with
| (locs, st') -> begin
Util.Val ((ExprTypes.ARRAY (locs), st'))
end))
end
| _21_665 -> begin
Util.Err ("Invalid parameter type for circuit generation")
end))


let rec lookup_Lst : (Prims.int, Prims.int) Total.map  ->  ExprTypes.l__GExpr Prims.list  ->  Prims.int Prims.list = (fun ( st  :  (Prims.int, Prims.int) Total.map ) ( lst  :  ExprTypes.l__GExpr Prims.list ) -> (match (lst) with
| [] -> begin
[]
end
| ExprTypes.LOC (l)::xs -> begin
((Total.lookup st l))::(lookup_Lst st xs)
end))


let rec compileCirc : circState config  ->  (Prims.int Prims.list * Circuit.l__Gate Prims.list) Util.result = (fun ( _21_678  :  circState config ) -> (match (_21_678) with
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


type qubit =
{id : Prims.int; ival : BoolExp.l__BoolExp; cval : BoolExp.l__BoolExp}


let is_Mkqubit : qubit  ->  Prims.bool = (Prims.checked_cast(fun ( _  :  qubit ) -> (FStar.All.failwith "Not yet implemented:is_Mkqubit")))


let nullq : qubit = {id = (Prims.parse_int "0"); ival = BoolExp.BFalse; cval = BoolExp.BFalse}


let get_subst : (Prims.int, qubit) Total.map  ->  Prims.int  ->  Prims.int = (fun ( m  :  (Prims.int, qubit) Total.map ) ( i  :  Prims.int ) -> (m i).id)


let data_q : Prims.int  ->  qubit = (fun ( i  :  Prims.int ) -> {id = i; ival = BoolExp.BVar (i); cval = BoolExp.BFalse})


let anc_q : Prims.int  ->  qubit = (fun ( i  :  Prims.int ) -> {id = i; ival = BoolExp.BFalse; cval = BoolExp.BFalse})


type circGCState =
{top : Prims.int; ah : AncillaHeap.l__AncHeap; gates : Circuit.l__Gate Prims.list; symtab : (Prims.int, qubit) Total.map}


let is_MkcircGCState : circGCState  ->  Prims.bool = (Prims.checked_cast(fun ( _  :  circGCState ) -> (FStar.All.failwith "Not yet implemented:is_MkcircGCState")))


let garbageCollect : circGCState  ->  qubit  ->  circGCState = (fun ( cs  :  circGCState ) ( q  :  qubit ) -> (

let _21_720 = (BoolExp.compileBexp cs.ah q.id q.cval)
in (match (_21_720) with
| (ah', res, ancs, circ) -> begin
(

let ah'' = if (q.ival = BoolExp.BFalse) then begin
(AncillaHeap.insert ah' q.id)
end else begin
ah'
end
in (

let f = (fun ( q'  :  qubit ) -> (

let subq = (fun ( v  :  Prims.int ) -> if (v = q.id) then begin
BoolExp.BXor ((q.ival, q.cval))
end else begin
BoolExp.BVar (v)
end)
in {id = q'.id; ival = q'.ival; cval = (BoolExp.simplify (BoolExp.substBexp q'.cval subq))}))
in (

let symtab' = (Total.map_mp f cs.symtab)
in {top = cs.top; ah = ah''; gates = (FStar.List.append cs.gates circ); symtab = symtab'})))
end)))


let circGCInit : circGCState = {top = (Prims.parse_int "0"); ah = AncillaHeap.emptyHeap; gates = []; symtab = (Total.const_map nullq)}


let circGCAlloc : circGCState  ->  BoolExp.l__BoolExp  ->  (Prims.int * circGCState) = (fun ( cs  :  circGCState ) ( bexp  :  BoolExp.l__BoolExp ) -> (

let bexp' = (BoolExp.simplify (BoolExp.substVar bexp (get_subst cs.symtab)))
in (

let _21_732 = (AncillaHeap.popMin cs.ah)
in (match (_21_732) with
| (ah', bit) -> begin
(

let _21_737 = (BoolExp.compileBexp ah' bit bexp')
in (match (_21_737) with
| (ah'', res, ancs, circ') -> begin
(

let q = {id = bit; ival = BoolExp.BFalse; cval = bexp'}
in (

let top' = (cs.top + (Prims.parse_int "1"))
in (

let gates' = (FStar.List.append cs.gates circ')
in (

let symtab' = (Total.update cs.symtab cs.top q)
in (cs.top, {top = top'; ah = ah''; gates = gates'; symtab = symtab'})))))
end))
end))))


let circGCAssign : circGCState  ->  Prims.int  ->  BoolExp.l__BoolExp  ->  circGCState = (fun ( cs  :  circGCState ) ( l  :  Prims.int ) ( bexp  :  BoolExp.l__BoolExp ) -> (

let q = (Total.lookup cs.symtab l)
in (

let bexp' = (BoolExp.simplify (BoolExp.substVar bexp (get_subst cs.symtab)))
in (

let bexpfac = (BoolExp.factorAs bexp' q.id)
in (match ((q.cval, bexpfac)) with
| (BoolExp.BFalse, _21_750) -> begin
(

let bexp'' = (BoolExp.substBexp bexp' (fun ( v  :  Prims.int ) -> if (v = q.id) then begin
BoolExp.BFalse
end else begin
BoolExp.BVar (v)
end))
in (

let _21_758 = (BoolExp.compileBexp cs.ah q.id bexp'')
in (match (_21_758) with
| (ah', res, ancs, circ) -> begin
(

let q' = {id = q.id; ival = q.ival; cval = bexp''}
in {top = cs.top; ah = ah'; gates = (FStar.List.append cs.gates circ); symtab = (Total.update cs.symtab l q')})
end)))
end
| (_21_761, Some (bexp'')) -> begin
(

let _21_769 = (BoolExp.compileBexp cs.ah q.id bexp'')
in (match (_21_769) with
| (ah', res, ancs, circ') -> begin
(

let q' = {id = q.id; ival = q.ival; cval = (BoolExp.simplify (BoolExp.BXor ((q.cval, bexp''))))}
in (

let f = (fun ( b  :  qubit ) -> (

let subq = (fun ( v  :  Prims.int ) -> if (v = q.id) then begin
BoolExp.BXor ((BoolExp.BVar (q.id), bexp''))
end else begin
BoolExp.BVar (v)
end)
in {id = b.id; ival = b.ival; cval = (BoolExp.simplify (BoolExp.substBexp b.cval subq))}))
in (

let symtab' = (Total.update (Total.map_mp f cs.symtab) l q')
in {top = cs.top; ah = ah'; gates = (FStar.List.append cs.gates circ'); symtab = (Total.update cs.symtab l q')})))
end))
end
| _21_777 -> begin
(

let _21_782 = (BoolExp.compileBexp_oop cs.ah bexp')
in (match (_21_782) with
| (ah', res, ancs, circ') -> begin
(

let q' = {id = res; ival = BoolExp.BFalse; cval = bexp'}
in (

let cs' = {top = cs.top; ah = ah'; gates = (FStar.List.append cs.gates circ'); symtab = (Total.update cs.symtab l q')}
in (garbageCollect cs' q)))
end))
end)))))


let circGCEval : circGCState  ->  Total.state  ->  Prims.int  ->  Prims.bool = (fun ( cs  :  circGCState ) ( st  :  Total.state ) ( i  :  Prims.int ) -> false)


let circGCInterp : circGCState interpretation = {alloc = circGCAlloc; assign = circGCAssign; eval = circGCEval}


let rec allocNcircGC : (ExprTypes.l__GExpr Prims.list * circGCState)  ->  Prims.int  ->  (ExprTypes.l__GExpr Prims.list * circGCState) = (fun ( _21_791  :  (ExprTypes.l__GExpr Prims.list * circGCState) ) ( i  :  Prims.int ) -> (match (_21_791) with
| (locs, cs) -> begin
if (i <= (Prims.parse_int "0")) then begin
((FStar.List.rev locs), cs)
end else begin
(

let _21_795 = (AncillaHeap.popMin cs.ah)
in (match (_21_795) with
| (ah', res) -> begin
(

let cs' = {top = (cs.top + (Prims.parse_int "1")); ah = ah'; gates = cs.gates; symtab = (Total.update cs.symtab cs.top (data_q res))}
in (allocNcircGC ((ExprTypes.LOC (cs.top))::locs, cs') (i - (Prims.parse_int "1"))))
end))
end
end))


let allocTycircGC : ExprTypes.l__GType  ->  circGCState  ->  (ExprTypes.l__GExpr * circGCState) Util.result = (fun ( ty  :  ExprTypes.l__GType ) ( cs  :  circGCState ) -> (match (ty) with
| ExprTypes.GBool -> begin
(

let _21_802 = (AncillaHeap.popMin cs.ah)
in (match (_21_802) with
| (ah', res) -> begin
(

let cs' = {top = (cs.top + (Prims.parse_int "1")); ah = ah'; gates = cs.gates; symtab = (Total.update cs.symtab cs.top (data_q res))}
in Util.Val ((ExprTypes.LOC (cs.top), cs')))
end))
end
| ExprTypes.GArray (n) -> begin
(

let _21_808 = (allocNcircGC ([], cs) n)
in (match (_21_808) with
| (locs, st') -> begin
Util.Val ((ExprTypes.ARRAY (locs), st'))
end))
end
| _21_810 -> begin
Util.Err ("Invalid parameter type for circuit generation")
end))


let rec lookup_Lst_gc : (Prims.int, qubit) Total.map  ->  ExprTypes.l__GExpr Prims.list  ->  Prims.int Prims.list = (fun ( symtab  :  (Prims.int, qubit) Total.map ) ( lst  :  ExprTypes.l__GExpr Prims.list ) -> (match (lst) with
| [] -> begin
[]
end
| ExprTypes.LOC (l)::xs -> begin
((Total.lookup symtab l).id)::(lookup_Lst_gc symtab xs)
end))


let rec compileGCCirc : circGCState config  ->  (Prims.int Prims.list * Circuit.l__Gate Prims.list) Util.result = (fun ( _21_822  :  circGCState config ) -> (match (_21_822) with
| (gexp, cs) -> begin
if (isVal gexp) then begin
(match (gexp) with
| ExprTypes.UNIT -> begin
Util.Val (([], []))
end
| ExprTypes.LAMBDA (x, ty, t) -> begin
(match ((allocTycircGC ty cs)) with
| Util.Err (s) -> begin
Util.Err (s)
end
| Util.Val (v, cs') -> begin
(compileGCCirc ((ExprTypes.substGExpr t x v), cs'))
end)
end
| ExprTypes.LOC (l) -> begin
(

let res = (Total.lookup cs.symtab l)
in Util.Val (((res.id)::[], cs.gates)))
end
| ExprTypes.ARRAY (lst) -> begin
(

let res = (lookup_Lst_gc cs.symtab lst)
in Util.Val ((res, cs.gates)))
end)
end else begin
(match ((step (gexp, cs) circGCInterp)) with
| Util.Err (s) -> begin
Util.Err (s)
end
| Util.Val (c') -> begin
(compileGCCirc c')
end)
end
end))


let rec eval_bexp_swap : boolState  ->  l__BExpState  ->  BoolExp.l__BoolExp  ->  Total.state  ->  Prims.unit = (fun ( st  :  boolState ) ( st'  :  l__BExpState ) ( bexp  :  BoolExp.l__BoolExp ) ( init  :  Total.state ) -> ())


let state_equiv_alloc : boolState  ->  l__BExpState  ->  Total.state  ->  BoolExp.l__BoolExp  ->  Prims.unit = (fun ( st  :  boolState ) ( st'  :  l__BExpState ) ( init  :  Total.state ) ( bexp  :  BoolExp.l__BoolExp ) -> ())


let state_equiv_assign : boolState  ->  l__BExpState  ->  Total.state  ->  Prims.int  ->  BoolExp.l__BoolExp  ->  Prims.unit = (fun ( st  :  boolState ) ( st'  :  l__BExpState ) ( init  :  Total.state ) ( l  :  Prims.int ) ( bexp  :  BoolExp.l__BoolExp ) -> ())


let rec state_equiv_step : ExprTypes.l__GExpr  ->  boolState  ->  l__BExpState  ->  Total.state  ->  Prims.unit = (fun ( gexp  :  ExprTypes.l__GExpr ) ( st  :  boolState ) ( st'  :  l__BExpState ) ( init  :  Total.state ) -> ())
and state_equiv_step_lst : ExprTypes.l__GExpr Prims.list  ->  boolState  ->  l__BExpState  ->  Total.state  ->  Prims.unit = (fun ( lst  :  ExprTypes.l__GExpr Prims.list ) ( st  :  boolState ) ( st'  :  l__BExpState ) ( init  :  Total.state ) -> ())




