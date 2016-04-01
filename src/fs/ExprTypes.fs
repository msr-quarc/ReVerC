#light "off"
module ExprTypes
open Prims

type l__GType =
| GUnit
| GBool
| GArray of Prims.int
| GFun of (l__GType * l__GType)
| GVar of Prims.int



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
in if (Util.for_someT (fun ( l  :  Prims.string Prims.list ) -> ((FStar.List.length l) > (Prims.parse_int "1"))) ((st1)::(st2)::[])) then begin
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


type l__IExp =
| ILit of Prims.int
| IVar of Prims.int
| IPlus of (l__IExp * l__IExp)
| IMinus of l__IExp



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

let e = TCons ((ty1, TArrow ((TVar (top''), TVar ((top'' + (Prims.parse_int "1")))))))
in (

let c = TCons ((ty2, TVar (top'')))
in ((top'' + (Prims.parse_int "2")), (e)::(FStar.List.append ec1 ec2), (c)::(FStar.List.append lc1 lc2), TVar ((top'' + (Prims.parse_int "1"))))))
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
(top', ec, lc, TArray (ILit ((FStar.List.length tlst))))
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
| ICons (c1, c2)::xs -> begin
(ICons (((substIExp i iexp c1), (substIExp i iexp c2))))::(iSubst i iexp xs)
end
| TCons (c1, c2)::xs -> begin
(TCons (((substIExpInTExp i iexp c1), (substIExpInTExp i iexp c2))))::(iSubst i iexp xs)
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


let rec mergeLower : l__IExp  ->  Prims.int  ->  l__Cons Prims.list  ->  l__IExp Prims.option = (fun ( iexp  :  l__IExp ) ( j  :  Prims.int ) ( bnds  :  l__Cons Prims.list ) -> (match (bnds) with
| [] -> begin
Some (iexp)
end
| ICons (iexp', IVar (h))::xs -> begin
if (h = j) then begin
(match (((normalize iexp), (normalize iexp'))) with
| (ILit (x), ILit (y)) -> begin
(mergeLower (ILit ((BoolExp.max x y))) j xs)
end
| (IVar (x), IVar (y)) -> begin
if (x = y) then begin
(mergeLower (IVar (x)) j xs)
end else begin
None
end
end
| _20_1988 -> begin
None
end)
end else begin
(mergeLower iexp j xs)
end
end
| _20_1991::xs -> begin
(mergeLower iexp j xs)
end))


let rec unify_bnds : Prims.int  ->  l__Cons Prims.list  ->  l__Cons Prims.list  ->  l__Cons Prims.list Prims.option = (fun ( top  :  Prims.int ) ( bnds  :  l__Cons Prims.list ) ( subs  :  l__Cons Prims.list ) -> (match (bnds) with
| [] -> begin
Some (subs)
end
| ICons (i1, i2)::xs -> begin
(match (((normalize i1), (normalize i2))) with
| (iexp, IVar (j)) -> begin
(match ((mergeLower iexp j xs)) with
| Some (sub) -> begin
(unify_bnds top (iSubst j sub xs) (iSubst j sub subs))
end
| None -> begin
(unify_bnds top (FStar.List.append xs ((ICons ((iexp, IVar (j))))::[])) subs)
end)
end
| (ILit (x), ILit (y)) -> begin
if (x <= y) then begin
(unify_bnds top xs subs)
end else begin
None
end
end
| (iexp, iexp') -> begin
(unify_bnds top (FStar.List.append xs ((ICons ((iexp, iexp')))::[])) subs)
end)
end
| TCons (t1, t2)::xs -> begin
(match ((t1, t2)) with
| ((TVar (i), TUnit)) | ((TUnit, TVar (i))) -> begin
(unify_bnds top (tSubst i TUnit xs) (tSubst i TUnit subs))
end
| ((TVar (i), TBool)) | ((TBool, TVar (i))) -> begin
(unify_bnds top (tSubst i TBool xs) (tSubst i TBool subs))
end
| (TVar (i), TArray (iexp)) -> begin
(

let sub = TArray (IVar (top))
in (unify_bnds (top + (Prims.parse_int "1")) (tSubst i sub ((ICons ((iexp, IVar (top))))::xs)) ((TCons ((TVar (i), sub)))::(tSubst i sub subs))))
end
| (TArray (iexp), TVar (i)) -> begin
(

let sub = TArray (IVar (top))
in (unify_bnds (top + (Prims.parse_int "1")) (tSubst i sub ((ICons ((IVar (top), iexp)))::xs)) ((TCons ((TVar (i), sub)))::(tSubst i sub subs))))
end
| (TVar (i), TArrow (t1, t2)) -> begin
(

let sub = TArrow ((TVar (top), TVar ((top + (Prims.parse_int "1")))))
in (unify_bnds (top + (Prims.parse_int "2")) (tSubst i sub ((TCons ((t1, TVar (top))))::(TCons ((TVar ((top + (Prims.parse_int "1"))), t2)))::xs)) ((TCons ((TVar (i), sub)))::(tSubst i sub subs))))
end
| (TArrow (t1, t2), TVar (i)) -> begin
(

let sub = TArrow ((TVar (top), TVar ((top + (Prims.parse_int "1")))))
in (unify_bnds (top + (Prims.parse_int "2")) (tSubst i sub ((TCons ((TVar (top), t1)))::(TCons ((t2, TVar ((top + (Prims.parse_int "1"))))))::xs)) ((TCons ((TVar (i), sub)))::(tSubst i sub subs))))
end
| (TVar (i), TVar (j)) -> begin
(unify_bnds top (FStar.List.append xs ((TCons ((t1, t2)))::[])) subs)
end
| (TUnit, TUnit) -> begin
(unify_bnds top xs subs)
end
| (TBool, TBool) -> begin
(unify_bnds top xs subs)
end
| (TArray (iexp), TArray (iexp')) -> begin
(unify_bnds top ((ICons ((iexp', iexp)))::xs) subs)
end
| (TArrow (t1, t2), TArrow (s1, s2)) -> begin
(unify_bnds top ((TCons ((s1, t1)))::(TCons ((t2, s2)))::xs) subs)
end
| _20_2092 -> begin
None
end)
end))


let rec unify_eq : Prims.int  ->  l__Cons Prims.list  ->  l__Cons Prims.list  ->  l__Cons Prims.list  ->  l__Cons Prims.list Prims.option = (fun ( top  :  Prims.int ) ( eqs  :  l__Cons Prims.list ) ( bnds  :  l__Cons Prims.list ) ( subs  :  l__Cons Prims.list ) -> (match (eqs) with
| [] -> begin
(unify_bnds top bnds subs)
end
| ICons (i1, i2)::xs -> begin
(match (((normalize i1), (normalize i2))) with
| ((IVar (i), iexp)) | ((iexp, IVar (i))) -> begin
(unify_eq top (iSubst i iexp xs) (iSubst i iexp bnds) (iSubst i iexp subs))
end
| (ILit (i), ILit (j)) -> begin
if (i = j) then begin
(unify_eq top xs bnds subs)
end else begin
None
end
end
| ((IPlus (IVar (i), y), iexp)) | ((iexp, IPlus (IVar (i), y))) -> begin
(

let sub = IPlus ((IMinus (y), iexp))
in (unify_eq top (iSubst i sub eqs) (iSubst i sub bnds) (iSubst i sub subs)))
end
| ((IPlus (IMinus (IVar (i)), y), iexp)) | ((iexp, IPlus (IMinus (IVar (i)), y))) -> begin
(

let sub = IPlus ((y, iexp))
in (unify_eq top (iSubst i sub eqs) (iSubst i sub bnds) (iSubst i sub subs)))
end
| _20_2142 -> begin
None
end)
end
| TCons (t1, t2)::xs -> begin
(match ((t1, t2)) with
| ((TVar (i), ty)) | ((ty, TVar (i))) -> begin
(unify_eq top (tSubst i ty xs) (tSubst i ty bnds) ((TCons ((TVar (i), ty)))::(tSubst i ty subs)))
end
| (TUnit, TUnit) -> begin
(unify_eq top xs bnds subs)
end
| (TBool, TBool) -> begin
(unify_eq top xs bnds subs)
end
| (TArray (iexp), TArray (iexp')) -> begin
(unify_eq top ((ICons ((iexp, iexp')))::xs) bnds subs)
end
| (TArrow (t1, t2), TArrow (s1, s2)) -> begin
(unify_eq top ((TCons ((t1, s1)))::(TCons ((t2, s2)))::xs) bnds subs)
end
| _20_2176 -> begin
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
| _20_2188 -> begin
(FStar.All.failwith "impossible")
end))


let annotate : l__GExpr  ->  l__GExpr Util.result = (fun ( tm  :  l__GExpr ) -> (

let _20_2194 = (inferTypes (Prims.parse_int "0") [] tm)
in (match (_20_2194) with
| (top, eqs, bnds, typ) -> begin
(

let res = (unify_eq top eqs bnds [])
in (match (res) with
| None -> begin
Util.Err ("Could not infer types")
end
| Some (subs) -> begin
Util.Val ((applySubs subs tm))
end))
end)))




