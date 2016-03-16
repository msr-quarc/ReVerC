#light "off"
module ExprTypes
open Prims

type l__GType =
| GUnit
| GBool
| GArray of Prims.int
| GFun of (l__GType * l__GType)
| GVar of Prims.int


let is_GUnit = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| GUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_GBool = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| GBool (_) -> begin
true
end
| _ -> begin
false
end))


let is_GArray = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| GArray (_) -> begin
true
end
| _ -> begin
false
end))


let is_GFun = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| GFun (_) -> begin
true
end
| _ -> begin
false
end))


let is_GVar = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| GVar (_) -> begin
true
end
| _ -> begin
false
end))


let ___GArray____0 = (fun ( projectee  :  l__GType ) -> (match (projectee) with
| GArray (_17_3) -> begin
_17_3
end))


let ___GFun____0 = (fun ( projectee  :  l__GType ) -> (match (projectee) with
| GFun (_17_6) -> begin
_17_6
end))


let ___GVar____0 = (fun ( projectee  :  l__GType ) -> (match (projectee) with
| GVar (_17_9) -> begin
_17_9
end))


type l__GExpr =
| LET of (Prims.string * l__GExpr * l__GExpr)
| LAMBDA of (Prims.string * l__GType * l__GExpr)
| APPLY of (l__GExpr * l__GExpr)
| IFTHENELSE of (l__GExpr * l__GExpr * l__GExpr)
| SEQUENCE of (l__GExpr * l__GExpr)
| ASSIGN of (l__GExpr * l__GExpr)
| VAR of Prims.string
| UNIT
| BOOL of Prims.bool
| XOR of (l__GExpr * l__GExpr)
| AND of (l__GExpr * l__GExpr)
| ARRAY of l__GExpr Prims.list
| GET_ARRAY of (l__GExpr * Prims.int)
| APPEND of (l__GExpr * l__GExpr)
| ROT of (Prims.int * l__GExpr)
| SLICE of (l__GExpr * Prims.int * Prims.int)
| ASSERT of l__GExpr
| LOC of Prims.int
| BEXP of BoolExp.l__BoolExp


let is_LET = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| LET (_) -> begin
true
end
| _ -> begin
false
end))


let is_LAMBDA = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| LAMBDA (_) -> begin
true
end
| _ -> begin
false
end))


let is_APPLY = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| APPLY (_) -> begin
true
end
| _ -> begin
false
end))


let is_IFTHENELSE = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| IFTHENELSE (_) -> begin
true
end
| _ -> begin
false
end))


let is_SEQUENCE = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| SEQUENCE (_) -> begin
true
end
| _ -> begin
false
end))


let is_ASSIGN = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| ASSIGN (_) -> begin
true
end
| _ -> begin
false
end))


let is_VAR = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| VAR (_) -> begin
true
end
| _ -> begin
false
end))


let is_UNIT = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| UNIT (_) -> begin
true
end
| _ -> begin
false
end))


let is_BOOL = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| BOOL (_) -> begin
true
end
| _ -> begin
false
end))


let is_XOR = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| XOR (_) -> begin
true
end
| _ -> begin
false
end))


let is_AND = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| AND (_) -> begin
true
end
| _ -> begin
false
end))


let is_ARRAY = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| ARRAY (_) -> begin
true
end
| _ -> begin
false
end))


let is_GET_ARRAY = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| GET_ARRAY (_) -> begin
true
end
| _ -> begin
false
end))


let is_APPEND = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| APPEND (_) -> begin
true
end
| _ -> begin
false
end))


let is_ROT = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| ROT (_) -> begin
true
end
| _ -> begin
false
end))


let is_SLICE = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| SLICE (_) -> begin
true
end
| _ -> begin
false
end))


let is_ASSERT = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| ASSERT (_) -> begin
true
end
| _ -> begin
false
end))


let is_LOC = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| LOC (_) -> begin
true
end
| _ -> begin
false
end))


let is_BEXP = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| BEXP (_) -> begin
true
end
| _ -> begin
false
end))


let ___LET____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| LET (_17_12) -> begin
_17_12
end))


let ___LAMBDA____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| LAMBDA (_17_15) -> begin
_17_15
end))


let ___APPLY____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| APPLY (_17_18) -> begin
_17_18
end))


let ___IFTHENELSE____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| IFTHENELSE (_17_21) -> begin
_17_21
end))


let ___SEQUENCE____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| SEQUENCE (_17_24) -> begin
_17_24
end))


let ___ASSIGN____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| ASSIGN (_17_27) -> begin
_17_27
end))


let ___VAR____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| VAR (_17_30) -> begin
_17_30
end))


let ___BOOL____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| BOOL (_17_33) -> begin
_17_33
end))


let ___XOR____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| XOR (_17_36) -> begin
_17_36
end))


let ___AND____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| AND (_17_39) -> begin
_17_39
end))


let ___ARRAY____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| ARRAY (_17_42) -> begin
_17_42
end))


let ___GET_ARRAY____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| GET_ARRAY (_17_45) -> begin
_17_45
end))


let ___APPEND____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| APPEND (_17_48) -> begin
_17_48
end))


let ___ROT____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| ROT (_17_51) -> begin
_17_51
end))


let ___SLICE____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| SLICE (_17_54) -> begin
_17_54
end))


let ___ASSERT____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| ASSERT (_17_57) -> begin
_17_57
end))


let ___LOC____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| LOC (_17_60) -> begin
_17_60
end))


let ___BEXP____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| BEXP (_17_63) -> begin
_17_63
end))


let rec height : l__GExpr  ->  Prims.int = (fun ( tm  :  l__GExpr ) -> (match (tm) with
| LET (s, t1, t2) -> begin
(1 + ((height t1) + (height t2)))
end
| LAMBDA (s, ty, t) -> begin
(1 + (height t))
end
| APPLY (t1, t2) -> begin
(1 + (BoolExp.max (height t1) (height t2)))
end
| IFTHENELSE (t1, t2, t3) -> begin
(1 + (BoolExp.max (BoolExp.max (height t1) (height t2)) (height t3)))
end
| SEQUENCE (t1, t2) -> begin
(1 + (BoolExp.max (height t1) (height t2)))
end
| ASSIGN (t1, t2) -> begin
(1 + (BoolExp.max (height t1) (height t2)))
end
| VAR (s) -> begin
1
end
| UNIT -> begin
1
end
| BOOL (b) -> begin
1
end
| XOR (t1, t2) -> begin
(1 + (BoolExp.max (height t1) (height t2)))
end
| AND (t1, t2) -> begin
(1 + (BoolExp.max (height t1) (height t2)))
end
| ARRAY (tlst) -> begin
(1 + (height_lst tlst))
end
| GET_ARRAY (t, i) -> begin
(1 + (height t))
end
| APPEND (t1, t2) -> begin
(1 + (BoolExp.max (height t1) (height t2)))
end
| ROT (i, t) -> begin
(1 + (height t))
end
| SLICE (t, i, j) -> begin
(1 + (height t))
end
| ASSERT (t) -> begin
(1 + (height t))
end
| LOC (i) -> begin
1
end
| BEXP (bexp) -> begin
1
end
| _17_133 -> begin
0
end))
and height_lst : l__GExpr Prims.list  ->  Prims.int = (fun ( tlst  :  l__GExpr Prims.list ) -> (match (tlst) with
| [] -> begin
0
end
| x::xs -> begin
(BoolExp.max (height x) (height_lst xs))
end))


let rec freeIn : Prims.string  ->  l__GExpr  ->  Prims.bool = (fun ( x  :  Prims.string ) ( tm  :  l__GExpr ) -> (match (tm) with
| LET (s, t1, t2) -> begin
((freeIn x t1) || ((not ((x = s))) && (freeIn x t2)))
end
| LAMBDA (s, ty, t) -> begin
((not ((x = s))) && (freeIn x t))
end
| APPLY (t1, t2) -> begin
((freeIn x t1) || (freeIn x t2))
end
| IFTHENELSE (t1, t2, t3) -> begin
(((freeIn x t1) || (freeIn x t2)) || (freeIn x t3))
end
| SEQUENCE (t1, t2) -> begin
((freeIn x t1) || (freeIn x t2))
end
| ASSIGN (t1, t2) -> begin
((freeIn x t1) || (freeIn x t2))
end
| VAR (s) -> begin
(x = s)
end
| UNIT -> begin
false
end
| BOOL (b) -> begin
false
end
| XOR (t1, t2) -> begin
((freeIn x t1) || (freeIn x t2))
end
| AND (t1, t2) -> begin
((freeIn x t1) || (freeIn x t2))
end
| ARRAY (tlst) -> begin
(freeIn_lst x tlst)
end
| GET_ARRAY (t, i) -> begin
(freeIn x t)
end
| APPEND (t1, t2) -> begin
((freeIn x t1) || (freeIn x t2))
end
| ROT (i, t) -> begin
(freeIn x t)
end
| SLICE (t, i, j) -> begin
(freeIn x t)
end
| ASSERT (t) -> begin
(freeIn x t)
end
| LOC (i) -> begin
false
end
| BEXP (bexp) -> begin
false
end
| _17_211 -> begin
false
end))
and freeIn_lst : Prims.string  ->  l__GExpr Prims.list  ->  Prims.bool = (fun ( x  :  Prims.string ) ( lst  :  l__GExpr Prims.list ) -> (match (lst) with
| [] -> begin
false
end
| t::xs -> begin
((freeIn x t) || (freeIn_lst x xs))
end))


let freeVars : l__GExpr  ->  Prims.string Util.set = (fun ( tm  :  l__GExpr ) ( x  :  Prims.string ) -> (freeIn x tm))


let rec varMaxTy : l__GType  ->  Prims.int = (fun ( ty  :  l__GType ) -> (match (ty) with
| (GUnit) | (GBool) | (GArray (_)) -> begin
0
end
| GVar (i) -> begin
i
end
| GFun (ty1, ty2) -> begin
(BoolExp.max (varMaxTy ty1) (varMaxTy ty2))
end))


let rec varMaxTm : l__GExpr  ->  Prims.int = (fun ( tm  :  l__GExpr ) -> (match (tm) with
| LET (s, t1, t2) -> begin
(BoolExp.max (varMaxTm t1) (varMaxTm t2))
end
| LAMBDA (s, ty, t) -> begin
(BoolExp.max (varMaxTy ty) (varMaxTm t))
end
| APPLY (t1, t2) -> begin
(BoolExp.max (varMaxTm t1) (varMaxTm t2))
end
| IFTHENELSE (t1, t2, t3) -> begin
(BoolExp.max (BoolExp.max (varMaxTm t1) (varMaxTm t2)) (varMaxTm t3))
end
| SEQUENCE (t1, t2) -> begin
(BoolExp.max (varMaxTm t1) (varMaxTm t2))
end
| ASSIGN (t1, t2) -> begin
(BoolExp.max (varMaxTm t1) (varMaxTm t2))
end
| (VAR (_)) | (UNIT) | (BOOL (_)) | (LOC (_)) | (BEXP (_)) -> begin
0
end
| XOR (t1, t2) -> begin
(BoolExp.max (varMaxTm t1) (varMaxTm t2))
end
| AND (t1, t2) -> begin
(BoolExp.max (varMaxTm t1) (varMaxTm t2))
end
| ARRAY (tlst) -> begin
(varMaxTm_lst tlst)
end
| GET_ARRAY (t, i) -> begin
(varMaxTm t)
end
| APPEND (t1, t2) -> begin
(BoolExp.max (varMaxTm t1) (varMaxTm t2))
end
| ROT (i, t) -> begin
(varMaxTm t)
end
| SLICE (t, i, j) -> begin
(varMaxTm t)
end
| ASSERT (t) -> begin
(varMaxTm t)
end
| _17_307 -> begin
0
end))
and varMaxTm_lst : l__GExpr Prims.list  ->  Prims.int = (fun ( lst  :  l__GExpr Prims.list ) -> (match (lst) with
| [] -> begin
0
end
| x::xs -> begin
(BoolExp.max (varMaxTm x) (varMaxTm_lst xs))
end))


let rec replicate : Prims.int  ->  Prims.string  ->  Prims.string = (fun ( i  :  Prims.int ) ( s  :  Prims.string ) -> if (i <= 0) then begin
""
end else begin
(FStar.String.strcat s (replicate (i - 1) s))
end)


let rec append' : Prims.string Prims.list  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun ( lst1  :  Prims.string Prims.list ) ( lst2  :  Prims.string Prims.list ) -> (match ((lst1, lst2)) with
| ([], _17_319) -> begin
lst2
end
| (_17_322, []) -> begin
lst1
end
| (x::[], y::ys) -> begin
((FStar.String.strcat x y))::ys
end
| (x::xs, _17_336) -> begin
(x)::(append' xs lst2)
end))


let appFront : Prims.string  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun ( s  :  Prims.string ) ( lst  :  Prims.string Prims.list ) -> (match (lst) with
| [] -> begin
(s)::[]
end
| x::xs -> begin
((FStar.String.strcat s x))::xs
end))


let rec appBack : Prims.string  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun ( s  :  Prims.string ) ( lst  :  Prims.string Prims.list ) -> (match (lst) with
| [] -> begin
(s)::[]
end
| x::[] -> begin
((FStar.String.strcat x s))::[]
end
| x::xs -> begin
(appBack s xs)
end))


let hdT = (fun ( l  :  'a Prims.list ) -> (match (l) with
| x::xs -> begin
x
end))


let tlT = (fun ( l  :  'a Prims.list ) -> (match (l) with
| x::xs -> begin
xs
end))


let rec prettyPrintTy : l__GType  ->  Prims.string = (fun ( ty  :  l__GType ) -> (match (ty) with
| GUnit -> begin
"unit"
end
| GBool -> begin
"bool"
end
| GVar (i) -> begin
(Prims.string_of_int i)
end
| GArray (n) -> begin
(FStar.String.strcat "vec " (Prims.string_of_int n))
end
| GFun (ty1, ty2) -> begin
(match (ty1) with
| GFun (_17_379) -> begin
(FStar.String.strcat "(" (FStar.String.strcat (prettyPrintTy ty1) (FStar.String.strcat ") -> " (prettyPrintTy ty2))))
end
| _17_382 -> begin
(FStar.String.strcat (prettyPrintTy ty1) (FStar.String.strcat " -> " (prettyPrintTy ty2)))
end)
end))


let rec prettyPrint : l__GExpr  ->  Prims.string Prims.list = (fun ( gexp  :  l__GExpr ) -> (

let indent = (fun ( i  :  Prims.int ) ( l  :  Prims.string Prims.list ) -> (FStar.List.map (fun ( s  :  Prims.string ) -> (FStar.String.strcat (replicate i " ") s)) l))
in (

let brackets = (fun ( s  :  Prims.string Prims.list ) -> (appFront "(" (appBack ")" s)))
in (

let flatten = (fun ( s  :  Prims.string ) ( lst  :  Prims.string Prims.list Prims.list ) -> (FStar.String.concat s (FStar.List.map FStar.List.hd lst)))
in (match (gexp) with
| LET (s, t1, t2) -> begin
(

let st1 = (prettyPrint t1)
in (

let st2 = (prettyPrint t2)
in (FStar.List.append (((FStar.String.strcat "let " (FStar.String.strcat s (FStar.String.strcat " = " (FStar.List.hd st1)))))::[]) (FStar.List.append (indent 2 (FStar.List.tl st1)) st2))))
end
| LAMBDA (s, ty, t) -> begin
(

let st = (prettyPrint t)
in (

let sty = (prettyPrintTy ty)
in (FStar.List.append (((FStar.String.strcat "\\ " (FStar.String.strcat s (FStar.String.strcat ":" (FStar.String.strcat sty (FStar.String.strcat " . " (FStar.List.hd st)))))))::[]) (indent 2 (FStar.List.tl st)))))
end
| APPLY (t1, t2) -> begin
(

let st1 = (prettyPrint t1)
in (

let st2 = (prettyPrint t2)
in if (Util.for_someT (fun ( l  :  Prims.string Prims.list ) -> ((FStar.List.length l) > 1)) ((st1)::(st2)::[])) then begin
(FStar.List.append (brackets st1) (indent 2 st2))
end else begin
((FStar.String.strcat "(" (FStar.String.strcat (FStar.List.hd st1) (FStar.String.strcat ")" (flatten " " ((st2)::[]))))))::[]
end))
end
| IFTHENELSE (t1, t2, t3) -> begin
(

let st1 = (prettyPrint t1)
in (

let st2 = (prettyPrint t2)
in (

let st3 = (prettyPrint t3)
in (FStar.List.append (FStar.List.append (appFront "if " st1) (appFront "then " st2)) (appFront "else " st3)))))
end
| SEQUENCE (t1, t2) -> begin
(

let st1 = (prettyPrint t1)
in (

let st2 = (prettyPrint t2)
in (FStar.List.append st1 st2)))
end
| ASSIGN (t1, t2) -> begin
(

let st1 = (prettyPrint t1)
in (

let st2 = (prettyPrint t2)
in (append' st1 (appFront " <- " st2))))
end
| VAR (s) -> begin
(s)::[]
end
| UNIT -> begin
("()")::[]
end
| BOOL (b) -> begin
if b then begin
("true")::[]
end else begin
("false")::[]
end
end
| XOR (t1, t2) -> begin
(

let st1 = (prettyPrint t1)
in (

let st2 = (prettyPrint t2)
in (FStar.All.pipe_left brackets (append' st1 (appFront " <> " st2)))))
end
| AND (t1, t2) -> begin
(

let st1 = (prettyPrint t1)
in (

let st2 = (prettyPrint t2)
in (FStar.All.pipe_left brackets (append' st1 (appFront " && " st2)))))
end
| ARRAY (tlst) -> begin
(

let stlst = (FStar.List.map prettyPrint tlst)
in if (Util.for_someT (fun ( l  :  Prims.string Prims.list ) -> ((FStar.List.length l) > 1)) stlst) then begin
(FStar.List.append (FStar.List.append (("[")::[]) (FStar.List.fold_right (fun ( lst  :  Prims.string Prims.list ) ( acc  :  Prims.string Prims.list ) -> (FStar.List.append (appBack "," (indent 2 lst)) acc)) stlst [])) (("]")::[]))
end else begin
((FStar.String.strcat "[" (FStar.String.strcat (flatten "," stlst) "]")))::[]
end)
end
| GET_ARRAY (t, i) -> begin
(

let st = (prettyPrint t)
in (appBack (FStar.String.strcat ".[" (FStar.String.strcat (Prims.string_of_int i) "]")) st))
end
| APPEND (t1, t2) -> begin
(

let st1 = (prettyPrint t1)
in (

let st2 = (prettyPrint t2)
in if (Util.for_someT (fun ( l  :  Prims.string Prims.list ) -> ((FStar.List.lengthT l) > 1)) ((st1)::(st2)::[])) then begin
(FStar.List.append (FStar.List.append (("append")::[]) (indent 2 st1)) (indent 2 st2))
end else begin
((FStar.String.strcat "append" (FStar.String.strcat (FStar.List.hd st1) (FStar.String.strcat " " (FStar.List.hd st2)))))::[]
end))
end
| ROT (i, t) -> begin
(

let st = (prettyPrint t)
in (appFront (FStar.String.strcat "rot " (Prims.string_of_int i)) st))
end
| SLICE (t, i, j) -> begin
(

let st = (prettyPrint t)
in (appBack (FStar.String.strcat ".[" (FStar.String.strcat (Prims.string_of_int i) (FStar.String.strcat ".." (FStar.String.strcat (Prims.string_of_int j) "]")))) st))
end
| ASSERT (t) -> begin
(

let st = (prettyPrint t)
in (appFront "allege " st))
end
| LOC (i) -> begin
((FStar.String.strcat "loc " (Prims.string_of_int i)))::[]
end
| BEXP (bexp) -> begin
((BoolExp.prettyPrintBexp bexp))::[]
end
| _17_488 -> begin
[]
end)))))


let show : l__GExpr  ->  Prims.string = (fun ( gexp  :  l__GExpr ) -> "")


let print : l__GExpr  ->  Prims.unit = (fun ( gexp  :  l__GExpr ) -> (

let str = (prettyPrint gexp)
in (FStar.List.iter FStar.IO.print_string str)))


let rec substTy : l__GType  ->  Prims.int  ->  l__GType  ->  l__GType = (fun ( ty  :  l__GType ) ( i  :  Prims.int ) ( ty'  :  l__GType ) -> (match (ty) with
| (GUnit) | (GBool) | (GArray (_)) -> begin
ty
end
| GVar (j) -> begin
if (i = j) then begin
ty'
end else begin
ty
end
end
| GFun (ty1, ty2) -> begin
GFun (((substTy ty1 i ty'), (substTy ty2 i ty')))
end))


let rec substGExpr : l__GExpr  ->  Prims.string  ->  l__GExpr  ->  l__GExpr = (fun ( tm  :  l__GExpr ) ( s  :  Prims.string ) ( tm'  :  l__GExpr ) -> (match (tm) with
| LET (x, t1, t2) -> begin
if (x = s) then begin
LET ((x, (substGExpr t1 s tm'), t2))
end else begin
LET ((x, (substGExpr t1 s tm'), (substGExpr t2 s tm')))
end
end
| LAMBDA (x, ty, t) -> begin
if (x = s) then begin
tm
end else begin
LAMBDA ((x, ty, (substGExpr t s tm')))
end
end
| APPLY (t1, t2) -> begin
APPLY (((substGExpr t1 s tm'), (substGExpr t2 s tm')))
end
| IFTHENELSE (t1, t2, t3) -> begin
IFTHENELSE (((substGExpr t1 s tm'), (substGExpr t2 s tm'), (substGExpr t3 s tm')))
end
| SEQUENCE (t1, t2) -> begin
SEQUENCE (((substGExpr t1 s tm'), (substGExpr t2 s tm')))
end
| ASSIGN (t1, t2) -> begin
ASSIGN (((substGExpr t1 s tm'), (substGExpr t2 s tm')))
end
| VAR (x) -> begin
if (x = s) then begin
tm'
end else begin
tm
end
end
| XOR (t1, t2) -> begin
XOR (((substGExpr t1 s tm'), (substGExpr t2 s tm')))
end
| AND (t1, t2) -> begin
AND (((substGExpr t1 s tm'), (substGExpr t2 s tm')))
end
| ARRAY (tlst) -> begin
ARRAY ((substGExpr_lst tlst s tm'))
end
| GET_ARRAY (t, i) -> begin
GET_ARRAY (((substGExpr t s tm'), i))
end
| APPEND (t1, t2) -> begin
APPEND (((substGExpr t1 s tm'), (substGExpr t2 s tm')))
end
| ROT (i, t) -> begin
ROT ((i, (substGExpr t s tm')))
end
| SLICE (t, i, j) -> begin
SLICE (((substGExpr t s tm'), i, j))
end
| ASSERT (t) -> begin
ASSERT ((substGExpr t s tm'))
end
| _17_571 -> begin
tm
end))
and substGExpr_lst : l__GExpr Prims.list  ->  Prims.string  ->  l__GExpr  ->  l__GExpr Prims.list = (fun ( lst  :  l__GExpr Prims.list ) ( s  :  Prims.string ) ( tm'  :  l__GExpr ) -> (match (lst) with
| [] -> begin
[]
end
| x::xs -> begin
((substGExpr x s tm'))::(substGExpr_lst xs s tm')
end))


let rec substTyInGExpr : l__GExpr  ->  Prims.int  ->  l__GType  ->  l__GExpr = (fun ( tm  :  l__GExpr ) ( k  :  Prims.int ) ( ty  :  l__GType ) -> (match (tm) with
| LET (x, t1, t2) -> begin
LET ((x, (substTyInGExpr t1 k ty), (substTyInGExpr t2 k ty)))
end
| LAMBDA (x, ty', t) -> begin
LAMBDA ((x, (substTy ty' k ty), (substTyInGExpr t k ty)))
end
| APPLY (t1, t2) -> begin
APPLY (((substTyInGExpr t1 k ty), (substTyInGExpr t2 k ty)))
end
| IFTHENELSE (t1, t2, t3) -> begin
IFTHENELSE (((substTyInGExpr t1 k ty), (substTyInGExpr t2 k ty), (substTyInGExpr t3 k ty)))
end
| SEQUENCE (t1, t2) -> begin
SEQUENCE (((substTyInGExpr t1 k ty), (substTyInGExpr t2 k ty)))
end
| ASSIGN (t1, t2) -> begin
ASSIGN (((substTyInGExpr t1 k ty), (substTyInGExpr t2 k ty)))
end
| XOR (t1, t2) -> begin
XOR (((substTyInGExpr t1 k ty), (substTyInGExpr t2 k ty)))
end
| AND (t1, t2) -> begin
AND (((substTyInGExpr t1 k ty), (substTyInGExpr t2 k ty)))
end
| ARRAY (tlst) -> begin
ARRAY ((substTyInGExpr_lst tlst k ty))
end
| GET_ARRAY (t, i) -> begin
GET_ARRAY (((substTyInGExpr t k ty), i))
end
| APPEND (t1, t2) -> begin
APPEND (((substTyInGExpr t1 k ty), (substTyInGExpr t2 k ty)))
end
| ROT (i, t) -> begin
ROT ((i, (substTyInGExpr t k ty)))
end
| SLICE (t, i, j) -> begin
SLICE (((substTyInGExpr t k ty), i, j))
end
| ASSERT (t) -> begin
ASSERT ((substTyInGExpr t k ty))
end
| _17_641 -> begin
tm
end))
and substTyInGExpr_lst : l__GExpr Prims.list  ->  Prims.int  ->  l__GType  ->  l__GExpr Prims.list = (fun ( lst  :  l__GExpr Prims.list ) ( k  :  Prims.int ) ( ty  :  l__GType ) -> (match (lst) with
| [] -> begin
[]
end
| x::xs -> begin
((substTyInGExpr x k ty))::(substTyInGExpr_lst xs k ty)
end))


type ctxt =
(Prims.string, l__GType) Par.map


type ('dummyV3, 'dummyV2, 'dummyV1) wellTypedCtxt =
| Ctxt_zero of Prims.string * l__GType * ctxt
| Ctxt_succ of Prims.string * l__GType * (Prims.string * l__GType) * ctxt * (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt


let is_Ctxt_zero = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Ctxt_zero (_) -> begin
true
end
| _ -> begin
false
end))


let is_Ctxt_succ = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Ctxt_succ (_) -> begin
true
end
| _ -> begin
false
end))


let ___Ctxt_zero___s = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_zero (_17_659, _17_660, _17_661) -> begin
_17_659
end))


let ___Ctxt_zero___ty = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_zero (_17_663, _17_662, _17_664) -> begin
_17_662
end))


let ___Ctxt_zero___xs = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_zero (_17_666, _17_667, _17_665) -> begin
_17_665
end))


let ___Ctxt_succ___s = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_succ (_17_670, _17_671, _17_672, _17_673, _17_674) -> begin
_17_670
end))


let ___Ctxt_succ___ty = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_succ (_17_676, _17_675, _17_677, _17_678, _17_679) -> begin
_17_675
end))


let ___Ctxt_succ___x = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_succ (_17_681, _17_682, _17_680, _17_683, _17_684) -> begin
_17_680
end))


let ___Ctxt_succ___xs = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_succ (_17_686, _17_687, _17_688, _17_685, _17_689) -> begin
_17_685
end))


let ___Ctxt_succ____4 = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_succ (_17_691, _17_692, _17_693, _17_694, _17_690) -> begin
_17_690
end))


type ('dummyV2, 'dummyV1) subType =
| Sub_refl of l__GType
| Sub_arry of Prims.nat * Prims.unit Util.fin
| Sub_lam of l__GType * l__GType * l__GType * l__GType * (Prims.unit, Prims.unit) subType * (Prims.unit, Prims.unit) subType


let is_Sub_refl = (fun ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Sub_refl (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sub_arry = (fun ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Sub_arry (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sub_lam = (fun ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Sub_lam (_) -> begin
true
end
| _ -> begin
false
end))


let ___Sub_refl___t1 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_refl (_17_704) -> begin
_17_704
end))


let ___Sub_arry___n = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_arry (_17_707, _17_708) -> begin
_17_707
end))


let ___Sub_arry___m = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_arry (_17_710, _17_709) -> begin
_17_709
end))


let ___Sub_lam___t1 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_17_713, _17_714, _17_715, _17_716, _17_717, _17_718) -> begin
_17_713
end))


let ___Sub_lam___t2 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_17_720, _17_719, _17_721, _17_722, _17_723, _17_724) -> begin
_17_719
end))


let ___Sub_lam___s1 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_17_726, _17_727, _17_725, _17_728, _17_729, _17_730) -> begin
_17_725
end))


let ___Sub_lam___s2 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_17_732, _17_733, _17_734, _17_731, _17_735, _17_736) -> begin
_17_731
end))


let ___Sub_lam____4 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_17_738, _17_739, _17_740, _17_741, _17_737, _17_742) -> begin
_17_737
end))


let ___Sub_lam____5 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_17_744, _17_745, _17_746, _17_747, _17_748, _17_743) -> begin
_17_743
end))


type ('dummyV3, 'dummyV2, 'dummyV1) wellTyped =
| Wt_let of ctxt * Prims.string * l__GExpr * l__GExpr * l__GType * l__GType * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_lam of ctxt * Prims.string * l__GType * l__GExpr * l__GType * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_apl of ctxt * l__GExpr * l__GExpr * l__GType * l__GType * l__GType * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit) subType
| Wt_ite of ctxt * l__GExpr * l__GExpr * l__GExpr * l__GType * l__GType * l__GType * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit) subType * (Prims.unit, Prims.unit) subType
| Wt_seq of ctxt * l__GExpr * l__GExpr * l__GType * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_ass of ctxt * l__GExpr * l__GExpr * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_unt of ctxt
| Wt_xor of ctxt * l__GExpr * l__GExpr * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_and of ctxt * l__GExpr * l__GExpr * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_bl of ctxt * Prims.bool
| Wt_apn of ctxt * l__GExpr * l__GExpr * Prims.nat * Prims.nat * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_rot of ctxt * l__GExpr * Prims.nat * Prims.unit Util.fin * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_slc of ctxt * l__GExpr * Prims.nat * Prims.nat * Prims.nat * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_arz of ctxt
| Wt_ars of ctxt * l__GExpr * l__GExpr Prims.list * Prims.nat * (Prims.unit, Prims.unit, Prims.unit) wellTyped * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_gta of ctxt * l__GExpr * Prims.nat * Prims.unit Util.fin * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_get of ctxt * Prims.string * l__GType * (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt
| Wt_ast of ctxt * l__GExpr * (Prims.unit, Prims.unit, Prims.unit) wellTyped
| Wt_loc of ctxt * Prims.int
| Wt_bex of ctxt * BoolExp.l__BoolExp


let is_Wt_let = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_let (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_lam = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_lam (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_apl = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_apl (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_ite = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_ite (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_seq = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_seq (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_ass = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_ass (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_unt = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_unt (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_xor = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_xor (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_and = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_and (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_bl = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_bl (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_apn = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_apn (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_rot = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_rot (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_slc = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_slc (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_arz = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_arz (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_ars = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_ars (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_gta = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_gta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_get = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_get (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_ast = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_ast (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_loc = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_loc (_) -> begin
true
end
| _ -> begin
false
end))


let is_Wt_bex = (fun ( _  :  obj ) ( _  :  obj ) ( _  :  obj ) ( _discr_  :  obj ) -> (match (_discr_) with
| Wt_bex (_) -> begin
true
end
| _ -> begin
false
end))


let ___Wt_let___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_17_824, _17_825, _17_826, _17_827, _17_828, _17_829, _17_830, _17_831) -> begin
_17_824
end))


let ___Wt_let___s = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_17_833, _17_832, _17_834, _17_835, _17_836, _17_837, _17_838, _17_839) -> begin
_17_832
end))


let ___Wt_let___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_17_841, _17_842, _17_840, _17_843, _17_844, _17_845, _17_846, _17_847) -> begin
_17_840
end))


let ___Wt_let___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_17_849, _17_850, _17_851, _17_848, _17_852, _17_853, _17_854, _17_855) -> begin
_17_848
end))


let ___Wt_let___ty1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_17_857, _17_858, _17_859, _17_860, _17_856, _17_861, _17_862, _17_863) -> begin
_17_856
end))


let ___Wt_let___ty2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_17_865, _17_866, _17_867, _17_868, _17_869, _17_864, _17_870, _17_871) -> begin
_17_864
end))


let ___Wt_let____6 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_17_873, _17_874, _17_875, _17_876, _17_877, _17_878, _17_872, _17_879) -> begin
_17_872
end))


let ___Wt_let____7 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_17_881, _17_882, _17_883, _17_884, _17_885, _17_886, _17_887, _17_880) -> begin
_17_880
end))


let ___Wt_lam___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_17_890, _17_891, _17_892, _17_893, _17_894, _17_895) -> begin
_17_890
end))


let ___Wt_lam___s = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_17_897, _17_896, _17_898, _17_899, _17_900, _17_901) -> begin
_17_896
end))


let ___Wt_lam___ty1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_17_903, _17_904, _17_902, _17_905, _17_906, _17_907) -> begin
_17_902
end))


let ___Wt_lam___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_17_909, _17_910, _17_911, _17_908, _17_912, _17_913) -> begin
_17_908
end))


let ___Wt_lam___ty2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_17_915, _17_916, _17_917, _17_918, _17_914, _17_919) -> begin
_17_914
end))


let ___Wt_lam____5 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_17_921, _17_922, _17_923, _17_924, _17_925, _17_920) -> begin
_17_920
end))


let ___Wt_apl___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_17_928, _17_929, _17_930, _17_931, _17_932, _17_933, _17_934, _17_935, _17_936) -> begin
_17_928
end))


let ___Wt_apl___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_17_938, _17_937, _17_939, _17_940, _17_941, _17_942, _17_943, _17_944, _17_945) -> begin
_17_937
end))


let ___Wt_apl___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_17_947, _17_948, _17_946, _17_949, _17_950, _17_951, _17_952, _17_953, _17_954) -> begin
_17_946
end))


let ___Wt_apl___ty1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_17_956, _17_957, _17_958, _17_955, _17_959, _17_960, _17_961, _17_962, _17_963) -> begin
_17_955
end))


let ___Wt_apl___ty2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_17_965, _17_966, _17_967, _17_968, _17_964, _17_969, _17_970, _17_971, _17_972) -> begin
_17_964
end))


let ___Wt_apl___ty3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_17_974, _17_975, _17_976, _17_977, _17_978, _17_973, _17_979, _17_980, _17_981) -> begin
_17_973
end))


let ___Wt_apl____6 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_17_983, _17_984, _17_985, _17_986, _17_987, _17_988, _17_982, _17_989, _17_990) -> begin
_17_982
end))


let ___Wt_apl____7 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_17_992, _17_993, _17_994, _17_995, _17_996, _17_997, _17_998, _17_991, _17_999) -> begin
_17_991
end))


let ___Wt_apl____8 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_17_1001, _17_1002, _17_1003, _17_1004, _17_1005, _17_1006, _17_1007, _17_1008, _17_1000) -> begin
_17_1000
end))


let ___Wt_ite___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1011, _17_1012, _17_1013, _17_1014, _17_1015, _17_1016, _17_1017, _17_1018, _17_1019, _17_1020, _17_1021, _17_1022) -> begin
_17_1011
end))


let ___Wt_ite___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1024, _17_1023, _17_1025, _17_1026, _17_1027, _17_1028, _17_1029, _17_1030, _17_1031, _17_1032, _17_1033, _17_1034) -> begin
_17_1023
end))


let ___Wt_ite___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1036, _17_1037, _17_1035, _17_1038, _17_1039, _17_1040, _17_1041, _17_1042, _17_1043, _17_1044, _17_1045, _17_1046) -> begin
_17_1035
end))


let ___Wt_ite___t3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1048, _17_1049, _17_1050, _17_1047, _17_1051, _17_1052, _17_1053, _17_1054, _17_1055, _17_1056, _17_1057, _17_1058) -> begin
_17_1047
end))


let ___Wt_ite___ty1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1060, _17_1061, _17_1062, _17_1063, _17_1059, _17_1064, _17_1065, _17_1066, _17_1067, _17_1068, _17_1069, _17_1070) -> begin
_17_1059
end))


let ___Wt_ite___ty2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1072, _17_1073, _17_1074, _17_1075, _17_1076, _17_1071, _17_1077, _17_1078, _17_1079, _17_1080, _17_1081, _17_1082) -> begin
_17_1071
end))


let ___Wt_ite___ty3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1084, _17_1085, _17_1086, _17_1087, _17_1088, _17_1089, _17_1083, _17_1090, _17_1091, _17_1092, _17_1093, _17_1094) -> begin
_17_1083
end))


let ___Wt_ite____7 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1096, _17_1097, _17_1098, _17_1099, _17_1100, _17_1101, _17_1102, _17_1095, _17_1103, _17_1104, _17_1105, _17_1106) -> begin
_17_1095
end))


let ___Wt_ite____8 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1108, _17_1109, _17_1110, _17_1111, _17_1112, _17_1113, _17_1114, _17_1115, _17_1107, _17_1116, _17_1117, _17_1118) -> begin
_17_1107
end))


let ___Wt_ite____9 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1120, _17_1121, _17_1122, _17_1123, _17_1124, _17_1125, _17_1126, _17_1127, _17_1128, _17_1119, _17_1129, _17_1130) -> begin
_17_1119
end))


let ___Wt_ite____10 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1132, _17_1133, _17_1134, _17_1135, _17_1136, _17_1137, _17_1138, _17_1139, _17_1140, _17_1141, _17_1131, _17_1142) -> begin
_17_1131
end))


let ___Wt_ite____11 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_17_1144, _17_1145, _17_1146, _17_1147, _17_1148, _17_1149, _17_1150, _17_1151, _17_1152, _17_1153, _17_1154, _17_1143) -> begin
_17_1143
end))


let ___Wt_seq___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_17_1157, _17_1158, _17_1159, _17_1160, _17_1161, _17_1162) -> begin
_17_1157
end))


let ___Wt_seq___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_17_1164, _17_1163, _17_1165, _17_1166, _17_1167, _17_1168) -> begin
_17_1163
end))


let ___Wt_seq___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_17_1170, _17_1171, _17_1169, _17_1172, _17_1173, _17_1174) -> begin
_17_1169
end))


let ___Wt_seq___ty = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_17_1176, _17_1177, _17_1178, _17_1175, _17_1179, _17_1180) -> begin
_17_1175
end))


let ___Wt_seq____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_17_1182, _17_1183, _17_1184, _17_1185, _17_1181, _17_1186) -> begin
_17_1181
end))


let ___Wt_seq____5 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_17_1188, _17_1189, _17_1190, _17_1191, _17_1192, _17_1187) -> begin
_17_1187
end))


let ___Wt_ass___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ass (_17_1195, _17_1196, _17_1197, _17_1198, _17_1199) -> begin
_17_1195
end))


let ___Wt_ass___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ass (_17_1201, _17_1200, _17_1202, _17_1203, _17_1204) -> begin
_17_1200
end))


let ___Wt_ass___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ass (_17_1206, _17_1207, _17_1205, _17_1208, _17_1209) -> begin
_17_1205
end))


let ___Wt_ass____3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ass (_17_1211, _17_1212, _17_1213, _17_1210, _17_1214) -> begin
_17_1210
end))


let ___Wt_ass____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ass (_17_1216, _17_1217, _17_1218, _17_1219, _17_1215) -> begin
_17_1215
end))


let ___Wt_unt___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_unt (_17_1222) -> begin
_17_1222
end))


let ___Wt_xor___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_xor (_17_1225, _17_1226, _17_1227, _17_1228, _17_1229) -> begin
_17_1225
end))


let ___Wt_xor___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_xor (_17_1231, _17_1230, _17_1232, _17_1233, _17_1234) -> begin
_17_1230
end))


let ___Wt_xor___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_xor (_17_1236, _17_1237, _17_1235, _17_1238, _17_1239) -> begin
_17_1235
end))


let ___Wt_xor____3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_xor (_17_1241, _17_1242, _17_1243, _17_1240, _17_1244) -> begin
_17_1240
end))


let ___Wt_xor____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_xor (_17_1246, _17_1247, _17_1248, _17_1249, _17_1245) -> begin
_17_1245
end))


let ___Wt_and___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_and (_17_1252, _17_1253, _17_1254, _17_1255, _17_1256) -> begin
_17_1252
end))


let ___Wt_and___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_and (_17_1258, _17_1257, _17_1259, _17_1260, _17_1261) -> begin
_17_1257
end))


let ___Wt_and___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_and (_17_1263, _17_1264, _17_1262, _17_1265, _17_1266) -> begin
_17_1262
end))


let ___Wt_and____3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_and (_17_1268, _17_1269, _17_1270, _17_1267, _17_1271) -> begin
_17_1267
end))


let ___Wt_and____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_and (_17_1273, _17_1274, _17_1275, _17_1276, _17_1272) -> begin
_17_1272
end))


let ___Wt_bl___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_bl (_17_1279, _17_1280) -> begin
_17_1279
end))


let ___Wt_bl___b = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_bl (_17_1282, _17_1281) -> begin
_17_1281
end))


let ___Wt_apn___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_17_1285, _17_1286, _17_1287, _17_1288, _17_1289, _17_1290, _17_1291) -> begin
_17_1285
end))


let ___Wt_apn___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_17_1293, _17_1292, _17_1294, _17_1295, _17_1296, _17_1297, _17_1298) -> begin
_17_1292
end))


let ___Wt_apn___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_17_1300, _17_1301, _17_1299, _17_1302, _17_1303, _17_1304, _17_1305) -> begin
_17_1299
end))


let ___Wt_apn___n = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_17_1307, _17_1308, _17_1309, _17_1306, _17_1310, _17_1311, _17_1312) -> begin
_17_1306
end))


let ___Wt_apn___m = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_17_1314, _17_1315, _17_1316, _17_1317, _17_1313, _17_1318, _17_1319) -> begin
_17_1313
end))


let ___Wt_apn____5 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_17_1321, _17_1322, _17_1323, _17_1324, _17_1325, _17_1320, _17_1326) -> begin
_17_1320
end))


let ___Wt_apn____6 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_17_1328, _17_1329, _17_1330, _17_1331, _17_1332, _17_1333, _17_1327) -> begin
_17_1327
end))


let ___Wt_rot___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_rot (_17_1336, _17_1337, _17_1338, _17_1339, _17_1340) -> begin
_17_1336
end))


let ___Wt_rot___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_rot (_17_1342, _17_1341, _17_1343, _17_1344, _17_1345) -> begin
_17_1341
end))


let ___Wt_rot___n = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_rot (_17_1347, _17_1348, _17_1346, _17_1349, _17_1350) -> begin
_17_1346
end))


let ___Wt_rot___i = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_rot (_17_1352, _17_1353, _17_1354, _17_1351, _17_1355) -> begin
_17_1351
end))


let ___Wt_rot____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_rot (_17_1357, _17_1358, _17_1359, _17_1360, _17_1356) -> begin
_17_1356
end))


let ___Wt_slc___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_17_1363, _17_1364, _17_1365, _17_1366, _17_1367, _17_1368) -> begin
_17_1363
end))


let ___Wt_slc___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_17_1370, _17_1369, _17_1371, _17_1372, _17_1373, _17_1374) -> begin
_17_1369
end))


let ___Wt_slc___n = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_17_1376, _17_1377, _17_1375, _17_1378, _17_1379, _17_1380) -> begin
_17_1375
end))


let ___Wt_slc___i = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_17_1382, _17_1383, _17_1384, _17_1381, _17_1385, _17_1386) -> begin
_17_1381
end))


let ___Wt_slc___j = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_17_1388, _17_1389, _17_1390, _17_1391, _17_1387, _17_1392) -> begin
_17_1387
end))


let ___Wt_slc____5 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_17_1394, _17_1395, _17_1396, _17_1397, _17_1398, _17_1393) -> begin
_17_1393
end))


let ___Wt_arz___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_arz (_17_1401) -> begin
_17_1401
end))


let ___Wt_ars___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_17_1404, _17_1405, _17_1406, _17_1407, _17_1408, _17_1409) -> begin
_17_1404
end))


let ___Wt_ars___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_17_1411, _17_1410, _17_1412, _17_1413, _17_1414, _17_1415) -> begin
_17_1410
end))


let ___Wt_ars___ts = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_17_1417, _17_1418, _17_1416, _17_1419, _17_1420, _17_1421) -> begin
_17_1416
end))


let ___Wt_ars___n = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_17_1423, _17_1424, _17_1425, _17_1422, _17_1426, _17_1427) -> begin
_17_1422
end))


let ___Wt_ars____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_17_1429, _17_1430, _17_1431, _17_1432, _17_1428, _17_1433) -> begin
_17_1428
end))


let ___Wt_ars____5 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_17_1435, _17_1436, _17_1437, _17_1438, _17_1439, _17_1434) -> begin
_17_1434
end))


let ___Wt_gta___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_gta (_17_1442, _17_1443, _17_1444, _17_1445, _17_1446) -> begin
_17_1442
end))


let ___Wt_gta___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_gta (_17_1448, _17_1447, _17_1449, _17_1450, _17_1451) -> begin
_17_1447
end))


let ___Wt_gta___n = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_gta (_17_1453, _17_1454, _17_1452, _17_1455, _17_1456) -> begin
_17_1452
end))


let ___Wt_gta___i = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_gta (_17_1458, _17_1459, _17_1460, _17_1457, _17_1461) -> begin
_17_1457
end))


let ___Wt_gta____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_gta (_17_1463, _17_1464, _17_1465, _17_1466, _17_1462) -> begin
_17_1462
end))


let ___Wt_get___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_get (_17_1469, _17_1470, _17_1471, _17_1472) -> begin
_17_1469
end))


let ___Wt_get___s = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_get (_17_1474, _17_1473, _17_1475, _17_1476) -> begin
_17_1473
end))


let ___Wt_get___ty = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_get (_17_1478, _17_1479, _17_1477, _17_1480) -> begin
_17_1477
end))


let ___Wt_get____3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_get (_17_1482, _17_1483, _17_1484, _17_1481) -> begin
_17_1481
end))


let ___Wt_ast___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ast (_17_1487, _17_1488, _17_1489) -> begin
_17_1487
end))


let ___Wt_ast___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ast (_17_1491, _17_1490, _17_1492) -> begin
_17_1490
end))


let ___Wt_ast____2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ast (_17_1494, _17_1495, _17_1493) -> begin
_17_1493
end))


let ___Wt_loc___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_loc (_17_1498, _17_1499) -> begin
_17_1498
end))


let ___Wt_loc___i = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_loc (_17_1501, _17_1500) -> begin
_17_1500
end))


let ___Wt_bex___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_bex (_17_1504, _17_1505) -> begin
_17_1504
end))


let ___Wt_bex___bexp = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_bex (_17_1507, _17_1506) -> begin
_17_1506
end))


let rec subtype : l__GType  ->  l__GType  ->  Prims.bool = (fun ( t1  :  l__GType ) ( t2  :  l__GType ) -> if (t1 = t2) then begin
true
end else begin
(match ((t1, t2)) with
| (GArray (i), GArray (j)) -> begin
(j <= i)
end
| (GFun (t1, t2), GFun (s1, s2)) -> begin
((suptype t1 s1) && (subtype t2 s2))
end
| _17_1529 -> begin
false
end)
end)
and suptype : l__GType  ->  l__GType  ->  Prims.bool = (fun ( t1  :  l__GType ) ( t2  :  l__GType ) -> if (t1 = t2) then begin
true
end else begin
(match ((t1, t2)) with
| (GArray (i), GArray (j)) -> begin
(j >= i)
end
| (GFun (t1, t2), GFun (s1, s2)) -> begin
((subtype t1 s1) && (suptype t2 s2))
end
| _17_1547 -> begin
false
end)
end)


let rec welltyctx_imp_findctx : ctxt  ->  Prims.string  ->  l__GType  ->  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt  ->  Prims.unit = (fun ( ctx  :  ctxt ) ( s  :  Prims.string ) ( ty  :  l__GType ) ( h  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> ())


let rec findctx_imp_welltyctx : ctxt  ->  Prims.string  ->  l__GType  ->  Prims.unit  ->  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt = (fun ( ctx  :  ctxt ) ( s  :  Prims.string ) ( ty  :  l__GType ) ( h  :  Prims.unit ) -> (match (ctx) with
| (x, y)::xs -> begin
if ((x = s) && (y = ty)) then begin
Ctxt_zero (s, ty, xs)
end else begin
Ctxt_succ (s, ty, (x, y), xs, (findctx_imp_welltyctx xs s ty ()))
end
end))


type l__IExp =
| ILit of Prims.int
| IVar of Prims.int
| IPlus of (l__IExp * l__IExp)
| IMinus of l__IExp


let is_ILit = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| ILit (_) -> begin
true
end
| _ -> begin
false
end))


let is_IVar = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| IVar (_) -> begin
true
end
| _ -> begin
false
end))


let is_IPlus = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| IPlus (_) -> begin
true
end
| _ -> begin
false
end))


let is_IMinus = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| IMinus (_) -> begin
true
end
| _ -> begin
false
end))


let ___ILit____0 = (fun ( projectee  :  l__IExp ) -> (match (projectee) with
| ILit (_17_1581) -> begin
_17_1581
end))


let ___IVar____0 = (fun ( projectee  :  l__IExp ) -> (match (projectee) with
| IVar (_17_1584) -> begin
_17_1584
end))


let ___IPlus____0 = (fun ( projectee  :  l__IExp ) -> (match (projectee) with
| IPlus (_17_1587) -> begin
_17_1587
end))


let ___IMinus____0 = (fun ( projectee  :  l__IExp ) -> (match (projectee) with
| IMinus (_17_1590) -> begin
_17_1590
end))


type l__TyExp =
| TUnit
| TBool
| TVar of Prims.int
| TArray of l__IExp
| TArrow of (l__TyExp * l__TyExp)


let is_TUnit = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| TUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_TBool = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| TBool (_) -> begin
true
end
| _ -> begin
false
end))


let is_TVar = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| TVar (_) -> begin
true
end
| _ -> begin
false
end))


let is_TArray = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| TArray (_) -> begin
true
end
| _ -> begin
false
end))


let is_TArrow = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| TArrow (_) -> begin
true
end
| _ -> begin
false
end))


let ___TVar____0 = (fun ( projectee  :  l__TyExp ) -> (match (projectee) with
| TVar (_17_1593) -> begin
_17_1593
end))


let ___TArray____0 = (fun ( projectee  :  l__TyExp ) -> (match (projectee) with
| TArray (_17_1596) -> begin
_17_1596
end))


let ___TArrow____0 = (fun ( projectee  :  l__TyExp ) -> (match (projectee) with
| TArrow (_17_1599) -> begin
_17_1599
end))


let rec normalize : l__IExp  ->  l__IExp = (fun ( iexp  :  l__IExp ) -> (match (iexp) with
| IMinus (x) -> begin
(match ((normalize x)) with
| IMinus (x') -> begin
x'
end
| ILit (i) -> begin
ILit ((- (i)))
end
| IPlus (x, y) -> begin
IPlus (((normalize (IMinus (x))), (normalize (IMinus (y)))))
end
| x' -> begin
IMinus (x')
end)
end
| IPlus (x, y) -> begin
(match (((normalize x), (normalize y))) with
| ((IVar (i), y')) | ((y', IVar (i))) -> begin
IPlus ((IVar (i), y'))
end
| (ILit (i), ILit (j)) -> begin
ILit ((i + j))
end
| ((IPlus (IVar (i), x'), y')) | ((y', IPlus (IVar (i), x'))) -> begin
IPlus ((IVar (i), IPlus ((x', y'))))
end
| ((IPlus (IMinus (IVar (i)), x'), y')) | ((y', IPlus (IMinus (IVar (i)), x'))) -> begin
IPlus ((IMinus (IVar (i)), IPlus ((x', y'))))
end
| (x', y') -> begin
IPlus ((x', y'))
end)
end
| _17_1655 -> begin
iexp
end))


let rec toTyExp : l__GType  ->  l__TyExp = (fun ( ty  :  l__GType ) -> (match (ty) with
| GUnit -> begin
TUnit
end
| GBool -> begin
TBool
end
| GVar (i) -> begin
TVar (i)
end
| GArray (n) -> begin
TArray (ILit (n))
end
| GFun (ty1, ty2) -> begin
TArrow (((toTyExp ty1), (toTyExp ty2)))
end))


let rec toGType : l__TyExp  ->  l__GType = (fun ( texp  :  l__TyExp ) -> (match (texp) with
| TUnit -> begin
GUnit
end
| TBool -> begin
GBool
end
| TVar (i) -> begin
GVar (i)
end
| TArray (iexp) -> begin
(match ((normalize iexp)) with
| ILit (n) -> begin
GArray (n)
end
| _17_1677 -> begin
GArray (0)
end)
end
| TArrow (texp1, texp2) -> begin
GFun (((toGType texp1), (toGType texp2)))
end))


type l__Cons =
| ICons of (l__IExp * l__IExp)
| TCons of (l__TyExp * l__TyExp)


let is_ICons = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| ICons (_) -> begin
true
end
| _ -> begin
false
end))


let is_TCons = (fun ( _discr_  :  obj ) -> (match (_discr_) with
| TCons (_) -> begin
true
end
| _ -> begin
false
end))


let ___ICons____0 = (fun ( projectee  :  l__Cons ) -> (match (projectee) with
| ICons (_17_1684) -> begin
_17_1684
end))


let ___TCons____0 = (fun ( projectee  :  l__Cons ) -> (match (projectee) with
| TCons (_17_1687) -> begin
_17_1687
end))


type ctxt' =
(Prims.string, l__TyExp) Par.map


let rec inferTypes : Prims.int  ->  ctxt'  ->  l__GExpr  ->  (Prims.int * l__Cons Prims.list * l__Cons Prims.list * l__TyExp) = (fun ( top  :  Prims.int ) ( ctx  :  ctxt' ) ( gexp  :  l__GExpr ) -> (match (gexp) with
| LET (x, t1, t2) -> begin
(

let _17_1702 = (inferTypes top ctx t1)
in (match (_17_1702) with
| (top', ec1, lc1, ty1) -> begin
(

let _17_1707 = (inferTypes top' (((x, ty1))::ctx) t2)
in (match (_17_1707) with
| (top'', ec2, lc2, ty2) -> begin
(top'', (FStar.List.append ec1 ec2), (FStar.List.append lc1 lc2), ty2)
end))
end))
end
| LAMBDA (x, ty, t) -> begin
(

let _17_1717 = (inferTypes top (((x, (toTyExp ty)))::ctx) t)
in (match (_17_1717) with
| (top', ec1, lc1, ty1) -> begin
(top', ec1, lc1, TArrow (((toTyExp ty), ty1)))
end))
end
| APPLY (t1, t2) -> begin
(

let _17_1726 = (inferTypes top ctx t1)
in (match (_17_1726) with
| (top', ec1, lc1, ty1) -> begin
(

let _17_1731 = (inferTypes top' ctx t2)
in (match (_17_1731) with
| (top'', ec2, lc2, ty2) -> begin
(

let e1 = TCons ((ty1, TArrow ((TVar (top''), TVar ((top'' + 1))))))
in (

let e2 = TCons ((ty2, TVar (top'')))
in ((top'' + 2), (e1)::(e2)::(FStar.List.append ec1 ec2), (FStar.List.append lc1 lc2), TVar ((top'' + 1)))))
end))
end))
end
| IFTHENELSE (t1, t2, t3) -> begin
(

let _17_1743 = (inferTypes top ctx t1)
in (match (_17_1743) with
| (top', ec1, lc1, ty1) -> begin
(

let _17_1748 = (inferTypes top' ctx t2)
in (match (_17_1748) with
| (top'', ec2, lc2, ty2) -> begin
(

let _17_1753 = (inferTypes top'' ctx t3)
in (match (_17_1753) with
| (top''', ec3, lc3, ty3) -> begin
(

let e1 = TCons ((ty1, TBool))
in (

let e2 = TCons ((ty2, TVar (top''')))
in (

let e3 = TCons ((ty3, TVar (top''')))
in ((top''' + 1), (e1)::(e2)::(e3)::(FStar.List.append (FStar.List.append ec1 ec2) ec3), (FStar.List.append lc1 lc2), TVar (top''')))))
end))
end))
end))
end
| SEQUENCE (t1, t2) -> begin
(

let _17_1765 = (inferTypes top ctx t1)
in (match (_17_1765) with
| (top', ec1, lc1, ty1) -> begin
(

let _17_1770 = (inferTypes top' ctx t2)
in (match (_17_1770) with
| (top'', ec2, lc2, ty2) -> begin
(

let e1 = TCons ((ty1, TUnit))
in (top'', (e1)::(FStar.List.append ec1 ec2), (FStar.List.append lc1 lc2), ty2))
end))
end))
end
| ASSIGN (t1, t2) -> begin
(

let _17_1780 = (inferTypes top ctx t1)
in (match (_17_1780) with
| (top', ec1, lc1, ty1) -> begin
(

let _17_1785 = (inferTypes top' ctx t2)
in (match (_17_1785) with
| (top'', ec2, lc2, ty2) -> begin
(

let e1 = TCons ((ty1, TBool))
in (

let e2 = TCons ((ty2, TBool))
in (top'', (e1)::(e2)::(FStar.List.append ec1 ec2), (FStar.List.append lc1 lc2), TUnit)))
end))
end))
end
| VAR (x) -> begin
(match ((Par.find ctx x)) with
| None -> begin
(top, [], [], TUnit)
end
| Some (ty) -> begin
(top, [], [], ty)
end)
end
| UNIT -> begin
(top, [], [], TUnit)
end
| BOOL (b) -> begin
(top, [], [], TBool)
end
| (XOR (t1, t2)) | (AND (t1, t2)) -> begin
(

let _17_1806 = (inferTypes top ctx t1)
in (match (_17_1806) with
| (top', ec1, lc1, ty1) -> begin
(

let _17_1811 = (inferTypes top' ctx t2)
in (match (_17_1811) with
| (top'', ec2, lc2, ty2) -> begin
(

let e1 = TCons ((ty1, TBool))
in (

let e2 = TCons ((ty2, TBool))
in (top'', (e1)::(e2)::(FStar.List.append ec1 ec2), (FStar.List.append lc1 lc2), TBool)))
end))
end))
end
| ARRAY (tlst) -> begin
(

let _17_1819 = (inferTypes_lst top ctx tlst)
in (match (_17_1819) with
| (top', ec, lc) -> begin
(top', ec, lc, TArray (ILit ((FStar.List.lengthT tlst))))
end))
end
| GET_ARRAY (t, i) -> begin
(

let _17_1828 = (inferTypes top ctx t)
in (match (_17_1828) with
| (top', ec1, lc1, ty1) -> begin
(

let e1 = TCons ((ty1, TArray (IVar (top'))))
in (

let l1 = ICons ((ILit (i), IVar (top')))
in ((top' + 1), (e1)::ec1, (l1)::lc1, TBool)))
end))
end
| APPEND (t1, t2) -> begin
(

let _17_1839 = (inferTypes top ctx t1)
in (match (_17_1839) with
| (top', ec1, lc1, ty1) -> begin
(

let _17_1844 = (inferTypes top' ctx t2)
in (match (_17_1844) with
| (top'', ec2, lc2, ty2) -> begin
(

let e1 = TCons ((ty1, TArray (IVar (top''))))
in (

let e2 = TCons ((ty2, TArray (IVar ((top'' + 1)))))
in (

let e3 = ICons ((IVar ((top'' + 2)), IPlus ((IVar (top''), IVar ((top'' + 1))))))
in ((top'' + 3), (e1)::(e2)::(e3)::(FStar.List.append ec1 ec2), (FStar.List.append lc1 lc2), TArray (IVar ((top'' + 2)))))))
end))
end))
end
| ROT (i, t) -> begin
(

let _17_1856 = (inferTypes top ctx t)
in (match (_17_1856) with
| (top', ec1, lc1, ty1) -> begin
(

let e1 = TCons ((ty1, TArray (IVar (top'))))
in (

let l1 = ICons ((ILit ((i + 1)), IVar (top')))
in ((top' + 1), (e1)::ec1, (l1)::lc1, TArray (IVar (top')))))
end))
end
| SLICE (t, i, j) -> begin
(

let _17_1868 = (inferTypes top ctx t)
in (match (_17_1868) with
| (top', ec1, lc1, ty1) -> begin
(

let e1 = TCons ((ty1, TArray (IVar (top'))))
in (

let l1 = ICons ((ILit ((j + 1)), IVar (top')))
in ((top' + 1), (e1)::ec1, (l1)::lc1, TArray (ILit (((j - i) + 1))))))
end))
end
| ASSERT (t) -> begin
(

let _17_1877 = (inferTypes top ctx t)
in (match (_17_1877) with
| (top', ec1, lc1, ty1) -> begin
(

let e1 = TCons ((ty1, TBool))
in (top', (e1)::ec1, lc1, TUnit))
end))
end
| LOC (i) -> begin
(top, [], [], TBool)
end
| BEXP (bexp) -> begin
(top, [], [], TBool)
end
| _17_1884 -> begin
(top, [], [], TUnit)
end))
and inferTypes_lst : Prims.int  ->  ctxt'  ->  l__GExpr Prims.list  ->  (Prims.int * l__Cons Prims.list * l__Cons Prims.list) = (fun ( top  :  Prims.int ) ( ctx  :  ctxt' ) ( lst  :  l__GExpr Prims.list ) -> (match (lst) with
| [] -> begin
(top, [], [])
end
| x::xs -> begin
(

let _17_1896 = (inferTypes top ctx x)
in (match (_17_1896) with
| (top', ec1, lc1, ty1) -> begin
(

let _17_1900 = (inferTypes_lst top' ctx xs)
in (match (_17_1900) with
| (top'', ec2, lc2) -> begin
(

let e1 = TCons ((ty1, TBool))
in (top'', (e1)::(FStar.List.append ec1 ec2), (FStar.List.append lc1 lc2)))
end))
end))
end))


let rec substIExp : Prims.int  ->  l__IExp  ->  l__IExp  ->  l__IExp = (fun ( i  :  Prims.int ) ( iexp  :  l__IExp ) ( x  :  l__IExp ) -> (match (x) with
| ILit (j) -> begin
ILit (j)
end
| IVar (j) -> begin
if (i = j) then begin
iexp
end else begin
IVar (j)
end
end
| IMinus (x) -> begin
(substIExp i iexp x)
end
| IPlus (x, y) -> begin
IPlus (((substIExp i iexp x), (substIExp i iexp y)))
end))


let rec substTExp : Prims.int  ->  l__TyExp  ->  l__TyExp  ->  l__TyExp = (fun ( i  :  Prims.int ) ( texp  :  l__TyExp ) ( x  :  l__TyExp ) -> (match (x) with
| TUnit -> begin
TUnit
end
| TBool -> begin
TBool
end
| TVar (j) -> begin
if (i = j) then begin
texp
end else begin
TVar (j)
end
end
| TArray (iexp) -> begin
TArray (iexp)
end
| TArrow (x, y) -> begin
TArrow (((substTExp i texp x), (substTExp i texp y)))
end))


let rec substIExpInTExp : Prims.int  ->  l__IExp  ->  l__TyExp  ->  l__TyExp = (fun ( i  :  Prims.int ) ( iexp  :  l__IExp ) ( x  :  l__TyExp ) -> (match (x) with
| TArray (iexp') -> begin
TArray ((substIExp i iexp iexp'))
end
| TArrow (x, y) -> begin
TArrow (((substIExpInTExp i iexp x), (substIExpInTExp i iexp y)))
end
| _17_1938 -> begin
x
end))


let rec iSubst : Prims.int  ->  l__IExp  ->  l__Cons Prims.list  ->  l__Cons Prims.list = (fun ( i  :  Prims.int ) ( iexp  :  l__IExp ) ( cons  :  l__Cons Prims.list ) -> (match (cons) with
| [] -> begin
[]
end
| ICons (c)::xs -> begin
(ICons (((substIExp i iexp (Prims.fst c)), (substIExp i iexp (Prims.snd c)))))::(iSubst i iexp xs)
end
| x::xs -> begin
(x)::(iSubst i iexp xs)
end))


let rec tSubst : Prims.int  ->  l__TyExp  ->  l__Cons Prims.list  ->  l__Cons Prims.list = (fun ( i  :  Prims.int ) ( texp  :  l__TyExp ) ( cons  :  l__Cons Prims.list ) -> (match (cons) with
| [] -> begin
[]
end
| TCons (c)::xs -> begin
(TCons (((substTExp i texp (Prims.fst c)), (substTExp i texp (Prims.snd c)))))::(tSubst i texp xs)
end
| x::xs -> begin
(x)::(tSubst i texp xs)
end))


let rec mergeLower : Prims.int  ->  Prims.int  ->  l__Cons Prims.list  ->  l__IExp = (fun ( i  :  Prims.int ) ( j  :  Prims.int ) ( bnds  :  l__Cons Prims.list ) -> (match (bnds) with
| [] -> begin
ILit (i)
end
| ICons (ILit (i'), i2)::xs -> begin
(match (i2) with
| IVar (j') -> begin
if (j = j') then begin
(mergeLower (BoolExp.max i i') j xs)
end else begin
(mergeLower i j xs)
end
end
| _17_1975 -> begin
(mergeLower i j xs)
end)
end
| _17_1977 -> begin
(FStar.All.failwith "impossible")
end))


let rec checkBounds = (fun ( check  :  l__Cons Prims.list ) ( subs  :  'A_17_206580 ) -> (match (check) with
| [] -> begin
Some (subs)
end
| ICons (ILit (i), i2)::xs -> begin
(match ((normalize i2)) with
| ILit (j) -> begin
if (i < j) then begin
(checkBounds xs subs)
end else begin
None
end
end
| _17_1991 -> begin
None
end)
end
| _17_1993 -> begin
(FStar.All.failwith "impossible")
end))


let rec unify_bnds : l__Cons Prims.list  ->  l__Cons Prims.list  ->  l__Cons Prims.list  ->  l__Cons Prims.list Prims.option = (fun ( bnds  :  l__Cons Prims.list ) ( check  :  l__Cons Prims.list ) ( subs  :  l__Cons Prims.list ) -> (match (bnds) with
| [] -> begin
(checkBounds check subs)
end
| ICons (ILit (i), i2)::xs -> begin
(match (i2) with
| IVar (j) -> begin
(

let sub = (mergeLower i j xs)
in (unify_bnds (iSubst j sub xs) (iSubst j sub check) (iSubst j sub subs)))
end
| _17_2009 -> begin
(unify_bnds xs ((ICons ((ILit (i), i2)))::check) subs)
end)
end
| _17_2011 -> begin
(FStar.All.failwith "impossible")
end))


let rec unify_eq : l__Cons Prims.list  ->  l__Cons Prims.list  ->  l__Cons Prims.list  ->  l__Cons Prims.list Prims.option = (fun ( eqs  :  l__Cons Prims.list ) ( bnds  :  l__Cons Prims.list ) ( subs  :  l__Cons Prims.list ) -> (match (eqs) with
| [] -> begin
(unify_bnds bnds [] subs)
end
| ICons (i1, i2)::xs -> begin
(match (((normalize i1), (normalize i2))) with
| ((IVar (i), iexp)) | ((iexp, IVar (i))) -> begin
(unify_eq (iSubst i iexp xs) (iSubst i iexp bnds) (iSubst i iexp subs))
end
| (ILit (i), ILit (j)) -> begin
if (i = j) then begin
(unify_eq xs bnds subs)
end else begin
None
end
end
| ((IPlus (IVar (i), y), iexp)) | ((iexp, IPlus (IVar (i), y))) -> begin
(

let sub = IPlus ((IMinus (y), iexp))
in (unify_eq (iSubst i sub eqs) (iSubst i sub bnds) (iSubst i sub subs)))
end
| ((IPlus (IMinus (IVar (i)), y), iexp)) | ((iexp, IPlus (IMinus (IVar (i)), y))) -> begin
(

let sub = IPlus ((y, iexp))
in (unify_eq (iSubst i sub eqs) (iSubst i sub bnds) (iSubst i sub subs)))
end
| _17_2060 -> begin
None
end)
end
| TCons (t1, t2)::xs -> begin
(match ((t1, t2)) with
| ((TVar (i), ty)) | ((ty, TVar (i))) -> begin
(unify_eq (tSubst i ty xs) (tSubst i ty bnds) ((TCons ((TVar (i), ty)))::subs))
end
| (TUnit, TUnit) -> begin
(unify_eq xs bnds subs)
end
| (TBool, TBool) -> begin
(unify_eq xs bnds subs)
end
| (TArray (iexp), TArray (iexp')) -> begin
(unify_eq ((ICons ((iexp, iexp')))::xs) bnds subs)
end
| (TArrow (t1, t2), TArrow (s1, s2)) -> begin
(unify_eq ((TCons ((t1, s1)))::(TCons ((t2, s2)))::xs) bnds subs)
end
| _17_2094 -> begin
None
end)
end))


let rec applySubs : l__Cons Prims.list  ->  l__GExpr  ->  l__GExpr = (fun ( subs  :  l__Cons Prims.list ) ( tm  :  l__GExpr ) -> (match (subs) with
| [] -> begin
tm
end
| TCons (TVar (i), texp)::xs -> begin
(applySubs xs (substTyInGExpr tm i (toGType texp)))
end
| _17_2106 -> begin
(FStar.All.failwith "impossible")
end))


let annotate : l__GExpr  ->  l__GExpr Util.result = (fun ( tm  :  l__GExpr ) -> (

let top = (varMaxTm tm)
in (

let _17_2114 = (inferTypes (top + 1) [] tm)
in (match (_17_2114) with
| (_17_2110, eqs, bnds, typ) -> begin
(

let res = (unify_eq eqs bnds [])
in (match (res) with
| None -> begin
Util.Err ("Could not infer types")
end
| Some (subs) -> begin
Util.Val ((applySubs subs tm))
end))
end))))




