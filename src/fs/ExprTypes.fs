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
| GArray (_20_3) -> begin
_20_3
end))


let ___GFun____0 = (fun ( projectee  :  l__GType ) -> (match (projectee) with
| GFun (_20_6) -> begin
_20_6
end))


let ___GVar____0 = (fun ( projectee  :  l__GType ) -> (match (projectee) with
| GVar (_20_9) -> begin
_20_9
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
| LET (_20_12) -> begin
_20_12
end))


let ___LAMBDA____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| LAMBDA (_20_15) -> begin
_20_15
end))


let ___APPLY____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| APPLY (_20_18) -> begin
_20_18
end))


let ___IFTHENELSE____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| IFTHENELSE (_20_21) -> begin
_20_21
end))


let ___SEQUENCE____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| SEQUENCE (_20_24) -> begin
_20_24
end))


let ___ASSIGN____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| ASSIGN (_20_27) -> begin
_20_27
end))


let ___VAR____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| VAR (_20_30) -> begin
_20_30
end))


let ___BOOL____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| BOOL (_20_33) -> begin
_20_33
end))


let ___XOR____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| XOR (_20_36) -> begin
_20_36
end))


let ___AND____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| AND (_20_39) -> begin
_20_39
end))


let ___ARRAY____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| ARRAY (_20_42) -> begin
_20_42
end))


let ___GET_ARRAY____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| GET_ARRAY (_20_45) -> begin
_20_45
end))


let ___APPEND____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| APPEND (_20_48) -> begin
_20_48
end))


let ___ROT____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| ROT (_20_51) -> begin
_20_51
end))


let ___SLICE____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| SLICE (_20_54) -> begin
_20_54
end))


let ___ASSERT____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| ASSERT (_20_57) -> begin
_20_57
end))


let ___LOC____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| LOC (_20_60) -> begin
_20_60
end))


let ___BEXP____0 = (fun ( projectee  :  l__GExpr ) -> (match (projectee) with
| BEXP (_20_63) -> begin
_20_63
end))


let rec height : l__GExpr  ->  Prims.int = (fun ( tm  :  l__GExpr ) -> (match (tm) with
| LET (s, t1, t2) -> begin
((Prims.parse_int "1") + ((height t1) + (height t2)))
end
| LAMBDA (s, ty, t) -> begin
((Prims.parse_int "1") + (height t))
end
| APPLY (t1, t2) -> begin
((Prims.parse_int "1") + (BoolExp.max (height t1) (height t2)))
end
| IFTHENELSE (t1, t2, t3) -> begin
((Prims.parse_int "1") + (BoolExp.max (BoolExp.max (height t1) (height t2)) (height t3)))
end
| SEQUENCE (t1, t2) -> begin
((Prims.parse_int "1") + (BoolExp.max (height t1) (height t2)))
end
| ASSIGN (t1, t2) -> begin
((Prims.parse_int "1") + (BoolExp.max (height t1) (height t2)))
end
| VAR (s) -> begin
(Prims.parse_int "1")
end
| UNIT -> begin
(Prims.parse_int "1")
end
| BOOL (b) -> begin
(Prims.parse_int "1")
end
| XOR (t1, t2) -> begin
((Prims.parse_int "1") + (BoolExp.max (height t1) (height t2)))
end
| AND (t1, t2) -> begin
((Prims.parse_int "1") + (BoolExp.max (height t1) (height t2)))
end
| ARRAY (tlst) -> begin
((Prims.parse_int "1") + (height_lst tlst))
end
| GET_ARRAY (t, i) -> begin
((Prims.parse_int "1") + (height t))
end
| APPEND (t1, t2) -> begin
((Prims.parse_int "1") + (BoolExp.max (height t1) (height t2)))
end
| ROT (i, t) -> begin
((Prims.parse_int "1") + (height t))
end
| SLICE (t, i, j) -> begin
((Prims.parse_int "1") + (height t))
end
| ASSERT (t) -> begin
((Prims.parse_int "1") + (height t))
end
| LOC (i) -> begin
(Prims.parse_int "1")
end
| BEXP (bexp) -> begin
(Prims.parse_int "1")
end
| _20_133 -> begin
(Prims.parse_int "0")
end))
and height_lst : l__GExpr Prims.list  ->  Prims.int = (fun ( tlst  :  l__GExpr Prims.list ) -> (match (tlst) with
| [] -> begin
(Prims.parse_int "0")
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
| _20_211 -> begin
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
(Prims.parse_int "0")
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
(Prims.parse_int "0")
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
| _20_307 -> begin
(Prims.parse_int "0")
end))
and varMaxTm_lst : l__GExpr Prims.list  ->  Prims.int = (fun ( lst  :  l__GExpr Prims.list ) -> (match (lst) with
| [] -> begin
(Prims.parse_int "0")
end
| x::xs -> begin
(BoolExp.max (varMaxTm x) (varMaxTm_lst xs))
end))


let rec replicate : Prims.int  ->  Prims.string  ->  Prims.string = (fun ( i  :  Prims.int ) ( s  :  Prims.string ) -> if (i <= (Prims.parse_int "0")) then begin
""
end else begin
(FStar.String.strcat s (replicate (i - (Prims.parse_int "1")) s))
end)


let rec append' : Prims.string Prims.list  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun ( lst1  :  Prims.string Prims.list ) ( lst2  :  Prims.string Prims.list ) -> (match ((lst1, lst2)) with
| ([], _20_319) -> begin
lst2
end
| (_20_322, []) -> begin
lst1
end
| (x::[], y::ys) -> begin
((FStar.String.strcat x y))::ys
end
| (x::xs, _20_336) -> begin
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
| GFun (_20_379) -> begin
(FStar.String.strcat "(" (FStar.String.strcat (prettyPrintTy ty1) (FStar.String.strcat ") -> " (prettyPrintTy ty2))))
end
| _20_382 -> begin
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
in (FStar.List.append (((FStar.String.strcat "let " (FStar.String.strcat s (FStar.String.strcat " = " (FStar.List.hd st1)))))::[]) (FStar.List.append (indent (Prims.parse_int "2") (FStar.List.tl st1)) st2))))
end
| LAMBDA (s, ty, t) -> begin
(

let st = (prettyPrint t)
in (

let sty = (prettyPrintTy ty)
in (FStar.List.append (((FStar.String.strcat "\\ " (FStar.String.strcat s (FStar.String.strcat ":" (FStar.String.strcat sty (FStar.String.strcat " . " (FStar.List.hd st)))))))::[]) (indent (Prims.parse_int "2") (FStar.List.tl st)))))
end
| APPLY (t1, t2) -> begin
(

let st1 = (prettyPrint t1)
in (

let st2 = (prettyPrint t2)
in if (Util.for_someT (fun ( l  :  Prims.string Prims.list ) -> ((FStar.List.length l) > (Prims.parse_int "1"))) ((st1)::(st2)::[])) then begin
(FStar.List.append (brackets st1) (indent (Prims.parse_int "2") st2))
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
in if (Util.for_someT (fun ( l  :  Prims.string Prims.list ) -> ((FStar.List.length l) > (Prims.parse_int "1"))) stlst) then begin
(FStar.List.append (FStar.List.append (("[")::[]) (FStar.List.fold_right (fun ( lst  :  Prims.string Prims.list ) ( acc  :  Prims.string Prims.list ) -> (FStar.List.append (appBack "," (indent (Prims.parse_int "2") lst)) acc)) stlst [])) (("]")::[]))
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
in if (Util.for_someT (fun ( l  :  Prims.string Prims.list ) -> ((FStar.List.lengthT l) > (Prims.parse_int "1"))) ((st1)::(st2)::[])) then begin
(FStar.List.append (FStar.List.append (("append")::[]) (indent (Prims.parse_int "2") st1)) (indent (Prims.parse_int "2") st2))
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
| _20_488 -> begin
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
| _20_571 -> begin
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
| _20_641 -> begin
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
| Ctxt_zero (_20_659, _20_660, _20_661) -> begin
_20_659
end))


let ___Ctxt_zero___ty = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_zero (_20_663, _20_662, _20_664) -> begin
_20_662
end))


let ___Ctxt_zero___xs = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_zero (_20_666, _20_667, _20_665) -> begin
_20_665
end))


let ___Ctxt_succ___s = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_succ (_20_670, _20_671, _20_672, _20_673, _20_674) -> begin
_20_670
end))


let ___Ctxt_succ___ty = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_succ (_20_676, _20_675, _20_677, _20_678, _20_679) -> begin
_20_675
end))


let ___Ctxt_succ___x = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_succ (_20_681, _20_682, _20_680, _20_683, _20_684) -> begin
_20_680
end))


let ___Ctxt_succ___xs = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_succ (_20_686, _20_687, _20_688, _20_685, _20_689) -> begin
_20_685
end))


let ___Ctxt_succ____4 = (fun ( _0  :  ctxt ) ( _1  :  Prims.string ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTypedCtxt ) -> (match (projectee) with
| Ctxt_succ (_20_691, _20_692, _20_693, _20_694, _20_690) -> begin
_20_690
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
| Sub_refl (_20_704) -> begin
_20_704
end))


let ___Sub_arry___n = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_arry (_20_707, _20_708) -> begin
_20_707
end))


let ___Sub_arry___m = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_arry (_20_710, _20_709) -> begin
_20_709
end))


let ___Sub_lam___t1 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_20_713, _20_714, _20_715, _20_716, _20_717, _20_718) -> begin
_20_713
end))


let ___Sub_lam___t2 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_20_720, _20_719, _20_721, _20_722, _20_723, _20_724) -> begin
_20_719
end))


let ___Sub_lam___s1 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_20_726, _20_727, _20_725, _20_728, _20_729, _20_730) -> begin
_20_725
end))


let ___Sub_lam___s2 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_20_732, _20_733, _20_734, _20_731, _20_735, _20_736) -> begin
_20_731
end))


let ___Sub_lam____4 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_20_738, _20_739, _20_740, _20_741, _20_737, _20_742) -> begin
_20_737
end))


let ___Sub_lam____5 = (fun ( _0  :  l__GType ) ( _1  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit) subType ) -> (match (projectee) with
| Sub_lam (_20_744, _20_745, _20_746, _20_747, _20_748, _20_743) -> begin
_20_743
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
| Wt_let (_20_824, _20_825, _20_826, _20_827, _20_828, _20_829, _20_830, _20_831) -> begin
_20_824
end))


let ___Wt_let___s = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_20_833, _20_832, _20_834, _20_835, _20_836, _20_837, _20_838, _20_839) -> begin
_20_832
end))


let ___Wt_let___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_20_841, _20_842, _20_840, _20_843, _20_844, _20_845, _20_846, _20_847) -> begin
_20_840
end))


let ___Wt_let___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_20_849, _20_850, _20_851, _20_848, _20_852, _20_853, _20_854, _20_855) -> begin
_20_848
end))


let ___Wt_let___ty1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_20_857, _20_858, _20_859, _20_860, _20_856, _20_861, _20_862, _20_863) -> begin
_20_856
end))


let ___Wt_let___ty2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_20_865, _20_866, _20_867, _20_868, _20_869, _20_864, _20_870, _20_871) -> begin
_20_864
end))


let ___Wt_let____6 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_20_873, _20_874, _20_875, _20_876, _20_877, _20_878, _20_872, _20_879) -> begin
_20_872
end))


let ___Wt_let____7 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_let (_20_881, _20_882, _20_883, _20_884, _20_885, _20_886, _20_887, _20_880) -> begin
_20_880
end))


let ___Wt_lam___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_20_890, _20_891, _20_892, _20_893, _20_894, _20_895) -> begin
_20_890
end))


let ___Wt_lam___s = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_20_897, _20_896, _20_898, _20_899, _20_900, _20_901) -> begin
_20_896
end))


let ___Wt_lam___ty1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_20_903, _20_904, _20_902, _20_905, _20_906, _20_907) -> begin
_20_902
end))


let ___Wt_lam___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_20_909, _20_910, _20_911, _20_908, _20_912, _20_913) -> begin
_20_908
end))


let ___Wt_lam___ty2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_20_915, _20_916, _20_917, _20_918, _20_914, _20_919) -> begin
_20_914
end))


let ___Wt_lam____5 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_lam (_20_921, _20_922, _20_923, _20_924, _20_925, _20_920) -> begin
_20_920
end))


let ___Wt_apl___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_20_928, _20_929, _20_930, _20_931, _20_932, _20_933, _20_934, _20_935, _20_936) -> begin
_20_928
end))


let ___Wt_apl___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_20_938, _20_937, _20_939, _20_940, _20_941, _20_942, _20_943, _20_944, _20_945) -> begin
_20_937
end))


let ___Wt_apl___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_20_947, _20_948, _20_946, _20_949, _20_950, _20_951, _20_952, _20_953, _20_954) -> begin
_20_946
end))


let ___Wt_apl___ty1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_20_956, _20_957, _20_958, _20_955, _20_959, _20_960, _20_961, _20_962, _20_963) -> begin
_20_955
end))


let ___Wt_apl___ty2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_20_965, _20_966, _20_967, _20_968, _20_964, _20_969, _20_970, _20_971, _20_972) -> begin
_20_964
end))


let ___Wt_apl___ty3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_20_974, _20_975, _20_976, _20_977, _20_978, _20_973, _20_979, _20_980, _20_981) -> begin
_20_973
end))


let ___Wt_apl____6 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_20_983, _20_984, _20_985, _20_986, _20_987, _20_988, _20_982, _20_989, _20_990) -> begin
_20_982
end))


let ___Wt_apl____7 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_20_992, _20_993, _20_994, _20_995, _20_996, _20_997, _20_998, _20_991, _20_999) -> begin
_20_991
end))


let ___Wt_apl____8 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apl (_20_1001, _20_1002, _20_1003, _20_1004, _20_1005, _20_1006, _20_1007, _20_1008, _20_1000) -> begin
_20_1000
end))


let ___Wt_ite___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1011, _20_1012, _20_1013, _20_1014, _20_1015, _20_1016, _20_1017, _20_1018, _20_1019, _20_1020, _20_1021, _20_1022) -> begin
_20_1011
end))


let ___Wt_ite___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1024, _20_1023, _20_1025, _20_1026, _20_1027, _20_1028, _20_1029, _20_1030, _20_1031, _20_1032, _20_1033, _20_1034) -> begin
_20_1023
end))


let ___Wt_ite___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1036, _20_1037, _20_1035, _20_1038, _20_1039, _20_1040, _20_1041, _20_1042, _20_1043, _20_1044, _20_1045, _20_1046) -> begin
_20_1035
end))


let ___Wt_ite___t3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1048, _20_1049, _20_1050, _20_1047, _20_1051, _20_1052, _20_1053, _20_1054, _20_1055, _20_1056, _20_1057, _20_1058) -> begin
_20_1047
end))


let ___Wt_ite___ty1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1060, _20_1061, _20_1062, _20_1063, _20_1059, _20_1064, _20_1065, _20_1066, _20_1067, _20_1068, _20_1069, _20_1070) -> begin
_20_1059
end))


let ___Wt_ite___ty2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1072, _20_1073, _20_1074, _20_1075, _20_1076, _20_1071, _20_1077, _20_1078, _20_1079, _20_1080, _20_1081, _20_1082) -> begin
_20_1071
end))


let ___Wt_ite___ty3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1084, _20_1085, _20_1086, _20_1087, _20_1088, _20_1089, _20_1083, _20_1090, _20_1091, _20_1092, _20_1093, _20_1094) -> begin
_20_1083
end))


let ___Wt_ite____7 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1096, _20_1097, _20_1098, _20_1099, _20_1100, _20_1101, _20_1102, _20_1095, _20_1103, _20_1104, _20_1105, _20_1106) -> begin
_20_1095
end))


let ___Wt_ite____8 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1108, _20_1109, _20_1110, _20_1111, _20_1112, _20_1113, _20_1114, _20_1115, _20_1107, _20_1116, _20_1117, _20_1118) -> begin
_20_1107
end))


let ___Wt_ite____9 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1120, _20_1121, _20_1122, _20_1123, _20_1124, _20_1125, _20_1126, _20_1127, _20_1128, _20_1119, _20_1129, _20_1130) -> begin
_20_1119
end))


let ___Wt_ite____10 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1132, _20_1133, _20_1134, _20_1135, _20_1136, _20_1137, _20_1138, _20_1139, _20_1140, _20_1141, _20_1131, _20_1142) -> begin
_20_1131
end))


let ___Wt_ite____11 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ite (_20_1144, _20_1145, _20_1146, _20_1147, _20_1148, _20_1149, _20_1150, _20_1151, _20_1152, _20_1153, _20_1154, _20_1143) -> begin
_20_1143
end))


let ___Wt_seq___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_20_1157, _20_1158, _20_1159, _20_1160, _20_1161, _20_1162) -> begin
_20_1157
end))


let ___Wt_seq___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_20_1164, _20_1163, _20_1165, _20_1166, _20_1167, _20_1168) -> begin
_20_1163
end))


let ___Wt_seq___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_20_1170, _20_1171, _20_1169, _20_1172, _20_1173, _20_1174) -> begin
_20_1169
end))


let ___Wt_seq___ty = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_20_1176, _20_1177, _20_1178, _20_1175, _20_1179, _20_1180) -> begin
_20_1175
end))


let ___Wt_seq____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_20_1182, _20_1183, _20_1184, _20_1185, _20_1181, _20_1186) -> begin
_20_1181
end))


let ___Wt_seq____5 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_seq (_20_1188, _20_1189, _20_1190, _20_1191, _20_1192, _20_1187) -> begin
_20_1187
end))


let ___Wt_ass___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ass (_20_1195, _20_1196, _20_1197, _20_1198, _20_1199) -> begin
_20_1195
end))


let ___Wt_ass___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ass (_20_1201, _20_1200, _20_1202, _20_1203, _20_1204) -> begin
_20_1200
end))


let ___Wt_ass___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ass (_20_1206, _20_1207, _20_1205, _20_1208, _20_1209) -> begin
_20_1205
end))


let ___Wt_ass____3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ass (_20_1211, _20_1212, _20_1213, _20_1210, _20_1214) -> begin
_20_1210
end))


let ___Wt_ass____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ass (_20_1216, _20_1217, _20_1218, _20_1219, _20_1215) -> begin
_20_1215
end))


let ___Wt_unt___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_unt (_20_1222) -> begin
_20_1222
end))


let ___Wt_xor___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_xor (_20_1225, _20_1226, _20_1227, _20_1228, _20_1229) -> begin
_20_1225
end))


let ___Wt_xor___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_xor (_20_1231, _20_1230, _20_1232, _20_1233, _20_1234) -> begin
_20_1230
end))


let ___Wt_xor___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_xor (_20_1236, _20_1237, _20_1235, _20_1238, _20_1239) -> begin
_20_1235
end))


let ___Wt_xor____3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_xor (_20_1241, _20_1242, _20_1243, _20_1240, _20_1244) -> begin
_20_1240
end))


let ___Wt_xor____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_xor (_20_1246, _20_1247, _20_1248, _20_1249, _20_1245) -> begin
_20_1245
end))


let ___Wt_and___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_and (_20_1252, _20_1253, _20_1254, _20_1255, _20_1256) -> begin
_20_1252
end))


let ___Wt_and___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_and (_20_1258, _20_1257, _20_1259, _20_1260, _20_1261) -> begin
_20_1257
end))


let ___Wt_and___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_and (_20_1263, _20_1264, _20_1262, _20_1265, _20_1266) -> begin
_20_1262
end))


let ___Wt_and____3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_and (_20_1268, _20_1269, _20_1270, _20_1267, _20_1271) -> begin
_20_1267
end))


let ___Wt_and____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_and (_20_1273, _20_1274, _20_1275, _20_1276, _20_1272) -> begin
_20_1272
end))


let ___Wt_bl___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_bl (_20_1279, _20_1280) -> begin
_20_1279
end))


let ___Wt_bl___b = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_bl (_20_1282, _20_1281) -> begin
_20_1281
end))


let ___Wt_apn___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_20_1285, _20_1286, _20_1287, _20_1288, _20_1289, _20_1290, _20_1291) -> begin
_20_1285
end))


let ___Wt_apn___t1 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_20_1293, _20_1292, _20_1294, _20_1295, _20_1296, _20_1297, _20_1298) -> begin
_20_1292
end))


let ___Wt_apn___t2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_20_1300, _20_1301, _20_1299, _20_1302, _20_1303, _20_1304, _20_1305) -> begin
_20_1299
end))


let ___Wt_apn___n = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_20_1307, _20_1308, _20_1309, _20_1306, _20_1310, _20_1311, _20_1312) -> begin
_20_1306
end))


let ___Wt_apn___m = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_20_1314, _20_1315, _20_1316, _20_1317, _20_1313, _20_1318, _20_1319) -> begin
_20_1313
end))


let ___Wt_apn____5 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_20_1321, _20_1322, _20_1323, _20_1324, _20_1325, _20_1320, _20_1326) -> begin
_20_1320
end))


let ___Wt_apn____6 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_apn (_20_1328, _20_1329, _20_1330, _20_1331, _20_1332, _20_1333, _20_1327) -> begin
_20_1327
end))


let ___Wt_rot___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_rot (_20_1336, _20_1337, _20_1338, _20_1339, _20_1340) -> begin
_20_1336
end))


let ___Wt_rot___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_rot (_20_1342, _20_1341, _20_1343, _20_1344, _20_1345) -> begin
_20_1341
end))


let ___Wt_rot___n = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_rot (_20_1347, _20_1348, _20_1346, _20_1349, _20_1350) -> begin
_20_1346
end))


let ___Wt_rot___i = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_rot (_20_1352, _20_1353, _20_1354, _20_1351, _20_1355) -> begin
_20_1351
end))


let ___Wt_rot____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_rot (_20_1357, _20_1358, _20_1359, _20_1360, _20_1356) -> begin
_20_1356
end))


let ___Wt_slc___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_20_1363, _20_1364, _20_1365, _20_1366, _20_1367, _20_1368) -> begin
_20_1363
end))


let ___Wt_slc___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_20_1370, _20_1369, _20_1371, _20_1372, _20_1373, _20_1374) -> begin
_20_1369
end))


let ___Wt_slc___n = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_20_1376, _20_1377, _20_1375, _20_1378, _20_1379, _20_1380) -> begin
_20_1375
end))


let ___Wt_slc___i = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_20_1382, _20_1383, _20_1384, _20_1381, _20_1385, _20_1386) -> begin
_20_1381
end))


let ___Wt_slc___j = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_20_1388, _20_1389, _20_1390, _20_1391, _20_1387, _20_1392) -> begin
_20_1387
end))


let ___Wt_slc____5 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_slc (_20_1394, _20_1395, _20_1396, _20_1397, _20_1398, _20_1393) -> begin
_20_1393
end))


let ___Wt_arz___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_arz (_20_1401) -> begin
_20_1401
end))


let ___Wt_ars___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_20_1404, _20_1405, _20_1406, _20_1407, _20_1408, _20_1409) -> begin
_20_1404
end))


let ___Wt_ars___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_20_1411, _20_1410, _20_1412, _20_1413, _20_1414, _20_1415) -> begin
_20_1410
end))


let ___Wt_ars___ts = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_20_1417, _20_1418, _20_1416, _20_1419, _20_1420, _20_1421) -> begin
_20_1416
end))


let ___Wt_ars___n = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_20_1423, _20_1424, _20_1425, _20_1422, _20_1426, _20_1427) -> begin
_20_1422
end))


let ___Wt_ars____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_20_1429, _20_1430, _20_1431, _20_1432, _20_1428, _20_1433) -> begin
_20_1428
end))


let ___Wt_ars____5 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ars (_20_1435, _20_1436, _20_1437, _20_1438, _20_1439, _20_1434) -> begin
_20_1434
end))


let ___Wt_gta___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_gta (_20_1442, _20_1443, _20_1444, _20_1445, _20_1446) -> begin
_20_1442
end))


let ___Wt_gta___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_gta (_20_1448, _20_1447, _20_1449, _20_1450, _20_1451) -> begin
_20_1447
end))


let ___Wt_gta___n = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_gta (_20_1453, _20_1454, _20_1452, _20_1455, _20_1456) -> begin
_20_1452
end))


let ___Wt_gta___i = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_gta (_20_1458, _20_1459, _20_1460, _20_1457, _20_1461) -> begin
_20_1457
end))


let ___Wt_gta____4 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_gta (_20_1463, _20_1464, _20_1465, _20_1466, _20_1462) -> begin
_20_1462
end))


let ___Wt_get___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_get (_20_1469, _20_1470, _20_1471, _20_1472) -> begin
_20_1469
end))


let ___Wt_get___s = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_get (_20_1474, _20_1473, _20_1475, _20_1476) -> begin
_20_1473
end))


let ___Wt_get___ty = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_get (_20_1478, _20_1479, _20_1477, _20_1480) -> begin
_20_1477
end))


let ___Wt_get____3 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_get (_20_1482, _20_1483, _20_1484, _20_1481) -> begin
_20_1481
end))


let ___Wt_ast___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ast (_20_1487, _20_1488, _20_1489) -> begin
_20_1487
end))


let ___Wt_ast___t = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ast (_20_1491, _20_1490, _20_1492) -> begin
_20_1490
end))


let ___Wt_ast____2 = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_ast (_20_1494, _20_1495, _20_1493) -> begin
_20_1493
end))


let ___Wt_loc___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_loc (_20_1498, _20_1499) -> begin
_20_1498
end))


let ___Wt_loc___i = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_loc (_20_1501, _20_1500) -> begin
_20_1500
end))


let ___Wt_bex___ctx = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_bex (_20_1504, _20_1505) -> begin
_20_1504
end))


let ___Wt_bex___bexp = (fun ( _0  :  ctxt ) ( _1  :  l__GExpr ) ( _2  :  l__GType ) ( projectee  :  (Prims.unit, Prims.unit, Prims.unit) wellTyped ) -> (match (projectee) with
| Wt_bex (_20_1507, _20_1506) -> begin
_20_1506
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
| _20_1529 -> begin
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
| _20_1547 -> begin
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
| ILit (_20_1581) -> begin
_20_1581
end))


let ___IVar____0 = (fun ( projectee  :  l__IExp ) -> (match (projectee) with
| IVar (_20_1584) -> begin
_20_1584
end))


let ___IPlus____0 = (fun ( projectee  :  l__IExp ) -> (match (projectee) with
| IPlus (_20_1587) -> begin
_20_1587
end))


let ___IMinus____0 = (fun ( projectee  :  l__IExp ) -> (match (projectee) with
| IMinus (_20_1590) -> begin
_20_1590
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
| TVar (_20_1593) -> begin
_20_1593
end))


let ___TArray____0 = (fun ( projectee  :  l__TyExp ) -> (match (projectee) with
| TArray (_20_1596) -> begin
_20_1596
end))


let ___TArrow____0 = (fun ( projectee  :  l__TyExp ) -> (match (projectee) with
| TArrow (_20_1599) -> begin
_20_1599
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
| _20_1655 -> begin
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
| _20_1677 -> begin
GArray ((Prims.parse_int "0"))
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
| ICons (_20_1684) -> begin
_20_1684
end))


let ___TCons____0 = (fun ( projectee  :  l__Cons ) -> (match (projectee) with
| TCons (_20_1687) -> begin
_20_1687
end))


type ctxt' =
(Prims.string, l__TyExp) Par.map


let rec inferTypes : Prims.int  ->  ctxt'  ->  l__GExpr  ->  (Prims.int * l__Cons Prims.list * l__Cons Prims.list * l__TyExp) = (fun ( top  :  Prims.int ) ( ctx  :  ctxt' ) ( gexp  :  l__GExpr ) -> (match (gexp) with
| LET (x, t1, t2) -> begin
(

let _20_1702 = (inferTypes top ctx t1)
in (match (_20_1702) with
| (top', ec1, lc1, ty1) -> begin
(

let _20_1707 = (inferTypes top' (((x, ty1))::ctx) t2)
in (match (_20_1707) with
| (top'', ec2, lc2, ty2) -> begin
(top'', (FStar.List.append ec1 ec2), (FStar.List.append lc1 lc2), ty2)
end))
end))
end
| LAMBDA (x, ty, t) -> begin
(

let _20_1717 = (inferTypes top (((x, (toTyExp ty)))::ctx) t)
in (match (_20_1717) with
| (top', ec1, lc1, ty1) -> begin
(top', ec1, lc1, TArrow (((toTyExp ty), ty1)))
end))
end
| APPLY (t1, t2) -> begin
(

let _20_1726 = (inferTypes top ctx t1)
in (match (_20_1726) with
| (top', ec1, lc1, ty1) -> begin
(

let _20_1731 = (inferTypes top' ctx t2)
in (match (_20_1731) with
| (top'', ec2, lc2, ty2) -> begin
(

let e1 = TCons ((ty1, TArrow ((TVar (top''), TVar ((top'' + (Prims.parse_int "1")))))))
in (

let e2 = TCons ((ty2, TVar (top'')))
in ((top'' + (Prims.parse_int "2")), (e1)::(e2)::(FStar.List.append ec1 ec2), (FStar.List.append lc1 lc2), TVar ((top'' + (Prims.parse_int "1"))))))
end))
end))
end
| IFTHENELSE (t1, t2, t3) -> begin
(

let _20_1743 = (inferTypes top ctx t1)
in (match (_20_1743) with
| (top', ec1, lc1, ty1) -> begin
(

let _20_1748 = (inferTypes top' ctx t2)
in (match (_20_1748) with
| (top'', ec2, lc2, ty2) -> begin
(

let _20_1753 = (inferTypes top'' ctx t3)
in (match (_20_1753) with
| (top''', ec3, lc3, ty3) -> begin
(

let e1 = TCons ((ty1, TBool))
in (

let e2 = TCons ((ty2, TVar (top''')))
in (

let e3 = TCons ((ty3, TVar (top''')))
in ((top''' + (Prims.parse_int "1")), (e1)::(e2)::(e3)::(FStar.List.append (FStar.List.append ec1 ec2) ec3), (FStar.List.append lc1 lc2), TVar (top''')))))
end))
end))
end))
end
| SEQUENCE (t1, t2) -> begin
(

let _20_1765 = (inferTypes top ctx t1)
in (match (_20_1765) with
| (top', ec1, lc1, ty1) -> begin
(

let _20_1770 = (inferTypes top' ctx t2)
in (match (_20_1770) with
| (top'', ec2, lc2, ty2) -> begin
(

let e1 = TCons ((ty1, TUnit))
in (top'', (e1)::(FStar.List.append ec1 ec2), (FStar.List.append lc1 lc2), ty2))
end))
end))
end
| ASSIGN (t1, t2) -> begin
(

let _20_1780 = (inferTypes top ctx t1)
in (match (_20_1780) with
| (top', ec1, lc1, ty1) -> begin
(

let _20_1785 = (inferTypes top' ctx t2)
in (match (_20_1785) with
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

let _20_1806 = (inferTypes top ctx t1)
in (match (_20_1806) with
| (top', ec1, lc1, ty1) -> begin
(

let _20_1811 = (inferTypes top' ctx t2)
in (match (_20_1811) with
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

let _20_1819 = (inferTypes_lst top ctx tlst)
in (match (_20_1819) with
| (top', ec, lc) -> begin
(top', ec, lc, TArray (ILit ((FStar.List.lengthT tlst))))
end))
end
| GET_ARRAY (t, i) -> begin
(

let _20_1828 = (inferTypes top ctx t)
in (match (_20_1828) with
| (top', ec1, lc1, ty1) -> begin
(

let e1 = TCons ((ty1, TArray (IVar (top'))))
in (

let l1 = ICons ((ILit (i), IVar (top')))
in ((top' + (Prims.parse_int "1")), (e1)::ec1, (l1)::lc1, TBool)))
end))
end
| APPEND (t1, t2) -> begin
(

let _20_1839 = (inferTypes top ctx t1)
in (match (_20_1839) with
| (top', ec1, lc1, ty1) -> begin
(

let _20_1844 = (inferTypes top' ctx t2)
in (match (_20_1844) with
| (top'', ec2, lc2, ty2) -> begin
(

let e1 = TCons ((ty1, TArray (IVar (top''))))
in (

let e2 = TCons ((ty2, TArray (IVar ((top'' + (Prims.parse_int "1"))))))
in (

let e3 = ICons ((IVar ((top'' + (Prims.parse_int "2"))), IPlus ((IVar (top''), IVar ((top'' + (Prims.parse_int "1")))))))
in ((top'' + (Prims.parse_int "3")), (e1)::(e2)::(e3)::(FStar.List.append ec1 ec2), (FStar.List.append lc1 lc2), TArray (IVar ((top'' + (Prims.parse_int "2"))))))))
end))
end))
end
| ROT (i, t) -> begin
(

let _20_1856 = (inferTypes top ctx t)
in (match (_20_1856) with
| (top', ec1, lc1, ty1) -> begin
(

let e1 = TCons ((ty1, TArray (IVar (top'))))
in (

let l1 = ICons ((ILit ((i + (Prims.parse_int "1"))), IVar (top')))
in ((top' + (Prims.parse_int "1")), (e1)::ec1, (l1)::lc1, TArray (IVar (top')))))
end))
end
| SLICE (t, i, j) -> begin
(

let _20_1868 = (inferTypes top ctx t)
in (match (_20_1868) with
| (top', ec1, lc1, ty1) -> begin
(

let e1 = TCons ((ty1, TArray (IVar (top'))))
in (

let l1 = ICons ((ILit ((j + (Prims.parse_int "1"))), IVar (top')))
in ((top' + (Prims.parse_int "1")), (e1)::ec1, (l1)::lc1, TArray (ILit (((j - i) + (Prims.parse_int "1")))))))
end))
end
| ASSERT (t) -> begin
(

let _20_1877 = (inferTypes top ctx t)
in (match (_20_1877) with
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
| _20_1884 -> begin
(top, [], [], TUnit)
end))
and inferTypes_lst : Prims.int  ->  ctxt'  ->  l__GExpr Prims.list  ->  (Prims.int * l__Cons Prims.list * l__Cons Prims.list) = (fun ( top  :  Prims.int ) ( ctx  :  ctxt' ) ( lst  :  l__GExpr Prims.list ) -> (match (lst) with
| [] -> begin
(top, [], [])
end
| x::xs -> begin
(

let _20_1896 = (inferTypes top ctx x)
in (match (_20_1896) with
| (top', ec1, lc1, ty1) -> begin
(

let _20_1900 = (inferTypes_lst top' ctx xs)
in (match (_20_1900) with
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
| _20_1938 -> begin
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
| _20_1975 -> begin
(mergeLower i j xs)
end)
end
| _20_1977 -> begin
(FStar.All.failwith "impossible")
end))


let rec checkBounds = (fun ( check  :  l__Cons Prims.list ) ( subs  :  'A_20_206580 ) -> (match (check) with
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
| _20_1991 -> begin
None
end)
end
| _20_1993 -> begin
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
| _20_2009 -> begin
(unify_bnds xs ((ICons ((ILit (i), i2)))::check) subs)
end)
end
| _20_2011 -> begin
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
| _20_2060 -> begin
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
| _20_2094 -> begin
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
| _20_2106 -> begin
(FStar.All.failwith "impossible")
end))


let annotate : l__GExpr  ->  l__GExpr Util.result = (fun ( tm  :  l__GExpr ) -> (

let top = (varMaxTm tm)
in (

let _20_2114 = (inferTypes (top + (Prims.parse_int "1")) [] tm)
in (match (_20_2114) with
| (_20_2110, eqs, bnds, typ) -> begin
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




