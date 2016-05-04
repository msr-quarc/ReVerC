(** Abstract syntax & general Revs utilities *)
module ExprTypes

(* Abstract syntax of Revs, along with utilities. Eventually a
   relational definition of the semantics should go here *)

open Util
open BoolExp

type GType =
  | GUnit
  | GBool
  | GArray of int
  | GFun of GType * GType
  | GConst of GType
  // Compiler use only
  | GVar of int

type GExpr =
  | LET        of string * GExpr * GExpr
  | LAMBDA     of string * GType * GExpr
  | APPLY      of GExpr * GExpr
  | IFTHENELSE of GExpr * GExpr * GExpr
  | SEQUENCE   of GExpr * GExpr
  | ASSIGN     of GExpr * GExpr
  | VAR        of string
  | UNIT
  | BOOL       of bool
  | XOR        of GExpr * GExpr
  | AND        of GExpr * GExpr
  | ARRAY      of list<GExpr>
  | GET_ARRAY  of GExpr * int
  | APPEND     of GExpr * GExpr
  | ROT        of int * GExpr
  | SLICE      of GExpr * int * int
  | CLEAN      of (GExpr * GExpr) // temporary hack for reporting failed assertions
  | ASSERT     of (GExpr * GExpr) // temporary hack for reporting failed assertions
  // Compiler use only
  | LOC        of int
  | BEXP       of BoolExp

let rec freeIn x tm = match tm with
  | LET (s, t1, t2) -> freeIn x t1 || (not (x = s) && freeIn x t2)
  | LAMBDA (s, ty, t) -> not (x = s) && freeIn x t
  | APPLY (t1, t2) -> freeIn x t1 || freeIn x t2
  | IFTHENELSE (t1, t2, t3) -> freeIn x t1 || freeIn x t2 || freeIn x t3
  | SEQUENCE (t1, t2) -> freeIn x t1 || freeIn x t2
  | ASSIGN (t1, t2) -> freeIn x t1 || freeIn x t2
  | VAR s -> x = s
  | UNIT -> false
  | BOOL b -> false
  | XOR (t1, t2) -> freeIn x t1 || freeIn x t2
  | AND (t1, t2) -> freeIn x t1 || freeIn x t2
  | ARRAY tlst -> freeIn_lst x tlst
  | GET_ARRAY (t, i) -> freeIn x t
  | APPEND (t1, t2) -> freeIn x t1 || freeIn x t2
  | ROT (i, t) -> freeIn x t
  | SLICE (t, i, j) -> freeIn x t
  | CLEAN (t, _) -> freeIn x t
  | ASSERT (t, _) -> freeIn x t
  | LOC i -> false
  | BEXP bexp -> false
  | _ -> false
and freeIn_lst x lst = match lst with
  | [] -> false
  | t::xs -> freeIn x t || freeIn_lst x xs

let freeVars tm = fun x -> freeIn x tm

let rec locsAcc lset tm = match tm with
  | LET (s, t1, t2) -> locsAcc (locsAcc lset t1) t2
  | LAMBDA (s, ty, t) -> locsAcc lset t
  | APPLY (t1, t2) -> locsAcc (locsAcc lset t1) t2
  | IFTHENELSE (t1, t2, t3) -> locsAcc (locsAcc lset t1) t2
  | SEQUENCE (t1, t2) -> locsAcc (locsAcc lset t1) t2
  | ASSIGN (t1, t2) -> locsAcc (locsAcc lset t1) t2
  | XOR (t1, t2) -> locsAcc (locsAcc lset t1) t2
  | AND (t1, t2) -> locsAcc (locsAcc lset t1) t2
  | ARRAY tlst -> locsAcc_lst lset tlst
  | GET_ARRAY (t, i) -> locsAcc lset t
  | APPEND (t1, t2) -> locsAcc (locsAcc lset t1) t2
  | ROT (i, t) -> locsAcc lset t
  | SLICE (t, i, j) -> locsAcc lset t
  | CLEAN (t, _) -> locsAcc lset t
  | ASSERT (t, _) -> locsAcc lset t
  | LOC i -> Set.ins i lset
  | _ -> lset
and locsAcc_lst lset lst = match lst with
  | [] -> lset
  | t::xs -> locsAcc_lst (locsAcc lset t) xs

let locs tm = locsAcc Set.empty tm

let rec varMaxTy ty = match ty with
  | GUnit | GBool | GArray _ -> 0
  | GVar i -> i
  | GConst ty -> varMaxTy ty
  | GFun (ty1, ty2) -> max (varMaxTy ty1) (varMaxTy ty2)

let rec varMaxTm tm = match tm with
  | LET (s, t1, t2) -> max (varMaxTm t1) (varMaxTm t2)
  | LAMBDA (s, ty, t) -> max (varMaxTy ty) (varMaxTm t)
  | APPLY (t1, t2) -> max (varMaxTm t1) (varMaxTm t2)
  | IFTHENELSE (t1, t2, t3) -> max (max (varMaxTm t1) (varMaxTm t2)) (varMaxTm t3)
  | SEQUENCE (t1, t2) -> max (varMaxTm t1) (varMaxTm t2)
  | ASSIGN (t1, t2) -> max (varMaxTm t1) (varMaxTm t2)
  | VAR _ | UNIT | BOOL _ | LOC _ | BEXP _ -> 0
  | XOR (t1, t2) -> max (varMaxTm t1) (varMaxTm t2)
  | AND (t1, t2) -> max (varMaxTm t1) (varMaxTm t2)
  | ARRAY tlst -> varMaxTm_lst tlst
  | GET_ARRAY (t, i) -> varMaxTm t
  | APPEND (t1, t2) -> max (varMaxTm t1) (varMaxTm t2)
  | ROT (i, t) -> varMaxTm t
  | SLICE (t, i, j) -> varMaxTm t
  | ASSERT (t, _) -> varMaxTm t
  | _ -> 0
and varMaxTm_lst lst = match lst with
  | [] -> 0
  | x::xs -> max (varMaxTm x) (varMaxTm_lst xs)

(* Pretty printing *)
let rec replicate i s =
  if i <= 0 then "" else FStar.String.strcat s (replicate (i-1) s)
let rec append' lst1 lst2 = match (lst1, lst2) with
  | ([], _)        -> lst2
  | (_, [])        -> lst1
  | (x::[], y::ys) -> (FStar.String.strcat x y)::ys
  | (x::xs, _)     -> x::(append' xs lst2)
let appFront s lst = match lst with
  | []    -> [s]
  | x::xs -> (FStar.String.strcat s x)::xs
let rec appBack s lst = match lst with
  | []    -> [s]
  | x::[] -> (FStar.String.strcat x s)::[]
  | x::xs -> appBack s xs
let indent i l = List.map (fun s -> FStar.String.strcat (replicate i " ") s) l
let brackets s = appFront "(" (appBack ")" s)

let hdT l = match l with
  | x::xs -> x
let tlT l = match l with
  | x::xs -> xs

let rec prettyPrintTy ty = match ty with
  | GUnit -> "unit"
  | GBool -> "bool"
  | GVar i -> Prims.string_of_int i
  | GArray n -> FStar.String.strcat "vec " (Prims.string_of_int n)
  | GConst ty -> FStar.String.strcat "const " (prettyPrintTy ty)
  | GFun (ty1, ty2) -> begin match ty1 with
    | GFun _ -> FStar.String.strcat "(" (FStar.String.strcat (prettyPrintTy ty1) (FStar.String.strcat ") -> " (prettyPrintTy ty2)))
    | _ -> FStar.String.strcat (prettyPrintTy ty1) (FStar.String.strcat " -> " (prettyPrintTy ty2))
    end

let rec prettyPrint gexp = match gexp with
  | LET (s, t1, t2) ->
      let st1 = prettyPrint t1 in
      let st2 = prettyPrint t2 in
        [FStar.String.strcat "let " (FStar.String.strcat s (FStar.String.strcat " = " (hdT st1)))] @
        ((indent 2 (tlT st1)) @ st2)
  | LAMBDA (s, ty, t) ->
      let st = prettyPrint t in
      let sty = prettyPrintTy ty in
        [FStar.String.strcat "\ " (FStar.String.strcat s (FStar.String.strcat ":" (FStar.String.strcat sty (FStar.String.strcat " . " (hdT st)))))] @
        (indent 2 (tlT st))
  | APPLY (t1, t2) ->
      let st1 = prettyPrint t1 in
      let st2 = prettyPrint t2 in
        if forSomeT (fun l -> List.length l > 1) ([st1;st2])
        then (brackets st1) @ (indent 2 st2)
        else [FStar.String.strcat (hdT st1) (FStar.String.strcat " " (hdT st2))]
  | IFTHENELSE (t1, t2, t3) ->
      let st1 = prettyPrint t1 in
      let st2 = prettyPrint t2 in
      let st3 = prettyPrint t3 in
        (appFront "if " st1) @ (appFront "then " st2) @ (appFront "else " st3)
  | SEQUENCE (t1, t2) ->
      let st1 = prettyPrint t1 in
      let st2 = prettyPrint t2 in
        st1 @ st2
  | ASSIGN (t1, t2) ->
      let st1 = prettyPrint t1 in
      let st2 = prettyPrint t2 in
        append' st1 (appFront " <- " st2)
  | VAR s -> [s]
  | UNIT -> ["()"]
  | BOOL b -> if b then ["true"] else ["false"]
  | XOR (t1, t2) ->
      let st1 = prettyPrint t1 in
      let st2 = prettyPrint t2 in
        brackets (append' st1 (appFront " <> " st2))
  | AND (t1, t2) ->
      let st1 = prettyPrint t1 in
      let st2 = prettyPrint t2 in
        brackets (append' st1 (appFront " && " st2))
  | ARRAY tlst ->
      let stlst = prettyPrint_lst tlst in
        if forSomeT (fun l -> List.length l > 1) stlst
        then
          let f stlst lst = stlst @ (appBack "," (indent 2 lst)) in
            ["["] @ (FStar.List.fold_left f [] stlst) @ ["]"]
        else 
          let f str lst = match lst with
            | [] -> str
            | x::xs -> FStar.String.strcat str (FStar.String.strcat "," x)
          in
            [FStar.String.strcat (FStar.List.fold_left f "[" stlst) "]"]
  | GET_ARRAY (t, i) ->
      let st = prettyPrint t in
        appBack (FStar.String.strcat ".[" (FStar.String.strcat (Prims.string_of_int i) "]")) st
  | APPEND (t1, t2) ->
      let st1 = prettyPrint t1 in
      let st2 = prettyPrint t2 in
        if forSomeT (fun l -> List.length l > 1) [st1;st2]
        then ["append"] @ (indent 2 st1) @ (indent 2 st2)
        else [FStar.String.strcat "append" (FStar.String.strcat (hdT st1) (FStar.String.strcat " " (hdT st2)))]
  | ROT (i, t) ->
      let st = prettyPrint t in
        appFront (FStar.String.strcat "rot " (Prims.string_of_int i)) st
  | SLICE (t, i, j) ->
      let st = prettyPrint t in
        appBack (FStar.String.strcat ".[" (FStar.String.strcat (Prims.string_of_int i) (FStar.String.strcat ".." (FStar.String.strcat (Prims.string_of_int j) "]")))) st
  | CLEAN (t, _) ->
      let st = prettyPrint t in
        appFront "clean " st
  | ASSERT (t, _) ->
      let st = prettyPrint t in
        appFront "allege " st
  | LOC i -> [FStar.String.strcat "loc " (Prims.string_of_int i)]
  | BEXP bexp -> [prettyPrintBexp bexp]
  | _ -> ["NOT SUPPORTED"]
and prettyPrint_lst tlst =  match tlst with
  | [] -> []
  | x::xs -> (prettyPrint x)::(prettyPrint_lst xs)

let show gexp =
  let str = prettyPrint gexp in
  FStar.String.concat "\n" str

let print gexp =
  let str = prettyPrint gexp in
  List.iter FStar.IO.print_string str

(* Substitutions *)
let rec substTy ty i ty' = match ty with
  | GUnit | GBool | GArray _ -> ty
  | GVar j -> if i = j then ty' else ty
  | GConst ty -> GConst (substTy ty i ty')
  | GFun (ty1, ty2) -> GFun (substTy ty1 i ty', substTy ty2 i ty')

let rec substGExpr tm s tm' = match tm with
  | LET (x, t1, t2) ->
    if x = s then LET (x, substGExpr t1 s tm', t2)
    else LET (x, substGExpr t1 s tm', substGExpr t2 s tm')
  | LAMBDA (x, ty, t) ->
    if x = s then tm else LAMBDA (x, ty, substGExpr t s tm')
  | APPLY (t1, t2) -> APPLY (substGExpr t1 s tm', substGExpr t2 s tm')
  | IFTHENELSE (t1, t2, t3) ->
    IFTHENELSE (substGExpr t1 s tm', substGExpr t2 s tm', substGExpr t3 s tm')
  | SEQUENCE (t1, t2) -> SEQUENCE (substGExpr t1 s tm', substGExpr t2 s tm')
  | ASSIGN (t1, t2) -> ASSIGN (substGExpr t1 s tm', substGExpr t2 s tm')
  | VAR x -> if x = s then tm' else tm
  | XOR (t1, t2) -> XOR (substGExpr t1 s tm', substGExpr t2 s tm')
  | AND (t1, t2) -> AND (substGExpr t1 s tm', substGExpr t2 s tm')
  | ARRAY tlst -> ARRAY (substGExpr_lst tlst s tm')
  | GET_ARRAY (t, i) -> GET_ARRAY (substGExpr t s tm', i)
  | APPEND (t1, t2) -> APPEND (substGExpr t1 s tm', substGExpr t2 s tm')
  | ROT (i, t) -> ROT (i, substGExpr t s tm')
  | SLICE (t, i, j) -> SLICE (substGExpr t s tm', i, j)
  | CLEAN (t, t') -> CLEAN (substGExpr t s tm', t')
  | ASSERT (t, t') -> ASSERT (substGExpr t s tm', t')
  | _ -> tm
and substGExpr_lst lst s tm' = match lst with
  | [] -> []
  | x::xs -> (substGExpr x s tm')::(substGExpr_lst xs s tm')

let rec substTyInGExpr tm k ty = match tm with
  | LET (x, t1, t2) -> LET (x, substTyInGExpr t1 k ty, substTyInGExpr t2 k ty)
  | LAMBDA (x, ty', t) -> LAMBDA (x, substTy ty' k ty, substTyInGExpr t k ty)
  | APPLY (t1, t2) -> APPLY (substTyInGExpr t1 k ty, substTyInGExpr t2 k ty)
  | IFTHENELSE (t1, t2, t3) -> IFTHENELSE (substTyInGExpr t1 k ty, substTyInGExpr t2 k ty, substTyInGExpr t3 k ty)
  | SEQUENCE (t1, t2) -> SEQUENCE (substTyInGExpr t1 k ty, substTyInGExpr t2 k ty)
  | ASSIGN (t1, t2) -> ASSIGN (substTyInGExpr t1 k ty, substTyInGExpr t2 k ty)
  | XOR (t1, t2) -> XOR (substTyInGExpr t1 k ty, substTyInGExpr t2 k ty)
  | AND (t1, t2) -> AND (substTyInGExpr t1 k ty, substTyInGExpr t2 k ty)
  | ARRAY tlst -> ARRAY (substTyInGExpr_lst tlst k ty)
  | GET_ARRAY (t, i) -> GET_ARRAY (substTyInGExpr t k ty, i)
  | APPEND (t1, t2) -> APPEND (substTyInGExpr t1 k ty, substTyInGExpr t2 k ty)
  | ROT (i, t) -> ROT (i, substTyInGExpr t k ty)
  | SLICE (t, i, j) -> SLICE (substTyInGExpr t k ty, i, j)
  | CLEAN (t, t') -> CLEAN (substTyInGExpr t k ty, t')
  | ASSERT (t, t') -> ASSERT (substTyInGExpr t k ty, t')
  | _ -> tm
and substTyInGExpr_lst lst k ty = match lst with
  | [] -> []
  | x::xs -> (substTyInGExpr x k ty)::(substTyInGExpr_lst xs k ty)

