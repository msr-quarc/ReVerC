module ExprTypes

(* ExprTypes - Abstract syntax of Revs, along with utilities for free variables,
               type inferencing, etc. Type inference includes only the
               simplified constraint system & solver now. In particular, this
               means we can't actually infer subtype polymorphism. We could do
               this using the "let-polymorphism" trick of the Hindley-Milner
               type system, but it's not implemented at the moment.
               Also, a relational big step semantics is defined, but it's
               implementation is a bit out of date with respect to the current
               semantics. Eventually we want to prove that the interpreter
               aggrees with the relational semantic definition. *)

open Util
open BoolExp
//open Dependence

type GType =
  | GUnit
  | GBool
  | GArray of int
  | GFun of GType * GType
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
  | ARRAY      of list GExpr
  | GET_ARRAY  of GExpr * int
  | APPEND     of GExpr * GExpr
  | ROT        of int * GExpr
  | SLICE      of GExpr * int * int
  | ASSERT     of GExpr
  // Compiler use only
  | LOC        of int
  | BEXP       of BoolExp

// Structural properties for helping with proofs
val height : tm:GExpr -> Tot int (decreases %[tm;1])
val height_lst : tlst:(list GExpr) -> Tot int (decreases %[tlst;0])
let rec height tm = match tm with
  | LET (s, t1, t2) -> 1 + (height t1) + (height t2)
  | LAMBDA (s, ty, t) -> 1 + (height t)
  | APPLY (t1, t2) -> 1 + (max (height t1) (height t2))
  | IFTHENELSE (t1, t2, t3) -> 1 + (max (max (height t1) (height t2)) (height t3))
  | SEQUENCE (t1, t2) -> 1 + (max (height t1) (height t2))
  | ASSIGN (t1, t2) -> 1 + (max (height t1) (height t2))
  | VAR s -> 1
  | UNIT -> 1
  | BOOL b -> 1
  | XOR (t1, t2) -> 1 + (max (height t1) (height t2))
  | AND (t1, t2) -> 1 + (max (height t1) (height t2))
  | ARRAY tlst -> 1 + (height_lst tlst)
  | GET_ARRAY (t, i) -> 1 + (height t)
  | APPEND (t1, t2) -> 1 + (max (height t1) (height t2))
  | ROT (i, t) -> 1 + (height t)
  | SLICE (t, i, j) -> 1 + (height t)
  | ASSERT t -> 1 + (height t)
  | LOC i -> 1
  | BEXP bexp -> 1
  | _ -> 0
and height_lst tlst = match tlst with
  | [] -> 0
  | x::xs -> max (height x) (height_lst xs)

val freeIn : x:string -> tm:GExpr -> Tot bool (decreases %[tm;0])
val freeIn_lst : x:string -> lst:list GExpr -> Tot bool (decreases %[lst;1])
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
  | ASSERT t -> freeIn x t
  | LOC i -> false
  | BEXP bexp -> false
  | _ -> false
and freeIn_lst x lst = match lst with
  | [] -> false
  | t::xs -> freeIn x t || freeIn_lst x xs

val freeVars : tm:GExpr -> Tot (set string) (decreases %[tm;0])
let freeVars tm = fun x -> freeIn x tm

val varMaxTy : ty:GType -> Tot int (decreases ty)
let rec varMaxTy ty = match ty with
  | GUnit | GBool | GArray _ -> 0
  | GVar i -> i
  | GFun (ty1, ty2) -> max (varMaxTy ty1) (varMaxTy ty2)

val varMaxTm : tm:GExpr -> Tot int (decreases %[tm;0])
val varMaxTm_lst : lst:list GExpr -> Tot int (decreases %[lst;1])
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
  | ASSERT t -> varMaxTm t
  | _ -> 0
and varMaxTm_lst lst = match lst with
  | [] -> 0
  | x::xs -> max (varMaxTm x) (varMaxTm_lst xs)

// Pretty printing
val replicate : int -> string -> Tot string
val append'   : list string -> list string -> Tot (list string)
val appFront  : string -> list string -> Tot (list string)
val appBack   : string -> list string -> Tot (list string)

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

val hdT : l:(list 'a){FStar.List.lengthT l >= 1} -> Tot 'a
val tlT : l:(list 'a){FStar.List.lengthT l >= 1} -> Tot (list 'a)
let hdT l = match l with
  | x::xs -> x
let tlT l = match l with
  | x::xs -> xs

val prettyPrintTy : GType -> string
let rec prettyPrintTy ty = match ty with
  | GUnit -> "unit"
  | GBool -> "bool"
  | GVar i -> Prims.string_of_int i
  | GArray n -> FStar.String.strcat "vec " (Prims.string_of_int n)
  | GFun (ty1, ty2) -> begin match ty1 with
    | GFun _ -> FStar.String.strcat "("
               (FStar.String.strcat (prettyPrintTy ty1)
               (FStar.String.strcat ") -> " (prettyPrintTy ty2)))
    | _ -> FStar.String.strcat (prettyPrintTy ty1)
          (FStar.String.strcat " -> " (prettyPrintTy ty2))
    end

val prettyPrint : GExpr -> list string
let rec prettyPrint gexp =
  let indent i l = FStar.List.map (fun s -> FStar.String.strcat (replicate i " ") s) l in
  let brackets s = appFront "(" (appBack ")" s) in
  let flatten s lst = FStar.String.concat s (FStar.List.map FStar.List.hd lst) in
  match gexp with
    | LET (s, t1, t2) ->
        let st1 = prettyPrint t1 in
        let st2 = prettyPrint t2 in
          [FStar.String.strcat "let " (FStar.String.strcat s (FStar.String.strcat " = " (FStar.List.hd st1)))] @
          ((indent 2 (FStar.List.tl st1)) @ st2)
    | LAMBDA (s, ty, t) ->
        let st = prettyPrint t in
        let sty = prettyPrintTy ty in
          [FStar.String.strcat "\ " (FStar.String.strcat s (FStar.String.strcat ":" (FStar.String.strcat sty (FStar.String.strcat " . " (FStar.List.hd st)))))] @
          (indent 2 (FStar.List.tl st))
    | APPLY (t1, t2) ->
        let st1 = prettyPrint t1 in
        let st2 = prettyPrint t2 in
          if for_someT (fun l -> FStar.List.length l > 1) ([st1;st2])
          then (brackets st1) @ (indent 2 st2)
          else [FStar.String.strcat "(" (FStar.String.strcat (FStar.List.hd st1) (FStar.String.strcat ")" (flatten " " [st2])))]
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
          brackets <| append' st1 (appFront " <> " st2)
    | AND (t1, t2) ->
        let st1 = prettyPrint t1 in
        let st2 = prettyPrint t2 in
          brackets <| append' st1 (appFront " && " st2)
    | ARRAY tlst ->
        let stlst = FStar.List.map prettyPrint tlst in
          if for_someT (fun l -> FStar.List.length l > 1) stlst
          then ["["] @ (FStar.List.fold_right (fun lst acc -> (appBack "," (indent 2 lst)) @ acc) stlst []) @ ["]"]
          else [FStar.String.strcat "[" (FStar.String.strcat (flatten "," stlst) "]")]
    | GET_ARRAY (t, i) ->
        let st = prettyPrint t in
          appBack (FStar.String.strcat ".[" (FStar.String.strcat (Prims.string_of_int i) "]")) st
    | APPEND (t1, t2) ->
        let st1 = prettyPrint t1 in
        let st2 = prettyPrint t2 in
          if for_someT (fun l -> FStar.List.lengthT l > 1) [st1;st2]
          then ["append"] @ (indent 2 st1) @ (indent 2 st2)
          else [FStar.String.strcat "append" (FStar.String.strcat (FStar.List.hd st1) (FStar.String.strcat " " (FStar.List.hd st2)))]
    | ROT (i, t) ->
        let st = prettyPrint t in
          appFront (FStar.String.strcat "rot " (Prims.string_of_int i)) st
    | SLICE (t, i, j) ->
        let st = prettyPrint t in
          appBack (FStar.String.strcat ".["
                  (FStar.String.strcat (Prims.string_of_int i)
                  (FStar.String.strcat ".."
                  (FStar.String.strcat (Prims.string_of_int j) "]")))) st
    | ASSERT t ->
        let st = prettyPrint t in
          appFront "allege " st
    | LOC i -> [FStar.String.strcat "loc " (Prims.string_of_int i)]
    | BEXP bexp -> [prettyPrintBexp bexp]
    | _ -> []

val show : GExpr -> Tot string
let show gexp = ""
//let show gexp =
//  let str = prettyPrint gexp in
//  FStar.String.concat "\n" str

let print gexp =
  let str = prettyPrint gexp in
  FStar.List.iter IO.print_string str

// Substitutions
val substTy : ty:GType -> int -> GType -> Tot GType (decreases ty)
let rec substTy ty i ty' = match ty with
  | GUnit | GBool | GArray _ -> ty
  | GVar j -> if i = j then ty' else ty
  | GFun (ty1, ty2) -> GFun (substTy ty1 i ty', substTy ty2 i ty')

val substGExpr : tm:GExpr -> string -> GExpr -> Tot GExpr (decreases %[tm;0])
val substGExpr_lst : l:list GExpr -> string -> GExpr -> Tot (list GExpr) (decreases %[l;1])
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
  | ASSERT t -> ASSERT (substGExpr t s tm')
  | _ -> tm
and substGExpr_lst lst s tm' = match lst with
  | [] -> []
  | x::xs -> (substGExpr x s tm')::(substGExpr_lst xs s tm')

val substTyInGExpr : tm:GExpr -> int -> GType -> Tot GExpr (decreases %[tm;0])
val substTyInGExpr_lst : l:list GExpr -> int -> GType -> Tot (list GExpr) (decreases %[l;1])
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
  | ASSERT t -> ASSERT (substTyInGExpr t k ty)
  | _ -> tm
and substTyInGExpr_lst lst k ty = match lst with
  | [] -> []
  | x::xs -> (substTyInGExpr x k ty)::(substTyInGExpr_lst xs k ty)

// Typechecking
open Par
type ctxt = Par.map string GType

type wellTypedCtxt : ctxt -> string -> GType -> Type =
  | Ctxt_zero : s:string -> ty:GType -> xs:ctxt -> wellTypedCtxt ((s, ty)::xs) s ty
  | Ctxt_succ : s:string -> ty:GType -> x:(string * GType){~(fst x = s)} -> xs:ctxt ->
                wellTypedCtxt xs s ty ->
                wellTypedCtxt (x::xs) s ty

type subType : GType -> GType -> Type =
  | Sub_refl : #t1:GType -> subType t1 t1
  | Sub_arry : n:nat -> m:fin n -> subType (GArray n) (GArray m)
  | Sub_lam  : #t1:GType -> #t2:GType -> #s1:GType -> #s2:GType ->
               subType s1 t1 ->
               subType t2 s2 ->
               subType (GFun (t1, t2)) (GFun (s1, s2))

type wellTyped : ctxt -> GExpr -> GType -> Type =
  | Wt_let : #ctx:ctxt -> #s:string -> #t1:GExpr -> #t2:GExpr -> #ty1:GType -> #ty2:GType ->
             wellTyped ctx t1 ty1 ->
             wellTyped ((s, ty1)::ctx) t2 ty2 ->
             wellTyped ctx (LET (s, t1, t2)) ty2
  | Wt_lam : #ctx:ctxt -> #s:string -> #ty1:GType -> #t:GExpr -> #ty2:GType ->
             wellTyped ((s, ty1)::ctx) t ty2 ->
             wellTyped ctx (LAMBDA (s, ty1, t)) (GFun (ty1, ty2))
  | Wt_apl : #ctx:ctxt -> #t1:GExpr -> #t2:GExpr -> #ty1:GType -> #ty2:GType -> #ty3:GType ->
             wellTyped ctx t1 (GFun (ty1, ty2)) ->
             wellTyped ctx t2 ty3 ->
             subType ty3 ty1 ->
             wellTyped ctx (APPLY (t1, t2)) ty2
  | Wt_ite : #ctx:ctxt -> #t1:GExpr -> #t2:GExpr -> #t3:GExpr -> #ty1:GType -> #ty2:GType -> #ty3:GType ->
             wellTyped ctx t1 GBool ->
             wellTyped ctx t2 ty1 ->
             wellTyped ctx t3 ty2 ->
             subType ty1 ty3 ->
             subType ty2 ty3 ->
             wellTyped ctx (IFTHENELSE (t1, t2, t3)) ty3
  | Wt_seq : #ctx:ctxt -> #t1:GExpr -> #t2:GExpr -> #ty:GType ->
             wellTyped ctx t1 GUnit ->
             wellTyped ctx t2 ty ->
             wellTyped ctx (SEQUENCE (t1, t2)) ty
  | Wt_ass : #ctx:ctxt -> #t1:GExpr -> #t2:GExpr ->
             wellTyped ctx t1 GBool ->
             wellTyped ctx t2 GBool ->
             wellTyped ctx (ASSIGN (t1, t2)) GUnit
  | Wt_unt : #ctx:ctxt -> wellTyped ctx UNIT GUnit
  | Wt_xor : #ctx:ctxt -> #t1:GExpr -> #t2:GExpr ->
             wellTyped ctx t1 GBool ->
             wellTyped ctx t2 GBool ->
             wellTyped ctx (XOR (t1, t2)) GBool
  | Wt_and : #ctx:ctxt -> #t1:GExpr -> #t2:GExpr ->
             wellTyped ctx t1 GBool ->
             wellTyped ctx t2 GBool ->
             wellTyped ctx (AND (t1, t2)) GBool
  | Wt_bl  : #ctx:ctxt -> b:bool -> wellTyped ctx (BOOL b) GBool
  | Wt_apn : #ctx:ctxt -> #t1:GExpr -> #t2:GExpr -> #n:nat -> #m:nat ->
             wellTyped ctx t1 (GArray n) ->
             wellTyped ctx t2 (GArray m) ->
             wellTyped ctx (APPEND (t1, t2)) (GArray (n + m))
  | Wt_rot : #ctx:ctxt -> #t:GExpr -> #n:nat -> i:fin n ->
             wellTyped ctx t (GArray n) ->
             wellTyped ctx (ROT (i, t)) (GArray n)
  | Wt_slc : #ctx:ctxt -> #t:GExpr -> #n:nat -> i:nat -> j:nat{i <= j && j < n} ->
             wellTyped ctx t (GArray n) ->
             wellTyped ctx (SLICE (t, i, j)) (GArray (j - i))
  | Wt_arz : #ctx:ctxt -> wellTyped ctx (ARRAY []) (GArray 0)
  | Wt_ars : #ctx:ctxt -> #t:GExpr -> #ts:list GExpr -> #n:nat ->
             wellTyped ctx t GBool ->
             wellTyped ctx (ARRAY ts) (GArray n) ->
             wellTyped ctx (ARRAY (t::ts)) (GArray (n+1))
  | Wt_gta : #ctx:ctxt -> #t:GExpr -> #n:nat -> i:fin n ->
             wellTyped ctx t (GArray n) ->
             wellTyped ctx (GET_ARRAY (t, i)) GBool
  | Wt_get : #ctx:ctxt -> #s:string -> #ty:GType ->
             wellTypedCtxt ctx s ty ->
             wellTyped ctx (VAR s) ty
  | Wt_ast : #ctx:ctxt -> #t:GExpr ->
             wellTyped ctx t GBool ->
             wellTyped ctx (ASSERT t) GUnit
  | Wt_loc : #ctx:ctxt -> i:int ->
             wellTyped ctx (LOC i) GBool
  | Wt_bex : #ctx:ctxt -> bexp:BoolExp ->
             wellTyped ctx (BEXP bexp) GBool

val subtype : t1:GType -> t2:GType -> Tot bool
val suptype : t1:GType -> t2:GType -> Tot bool
let rec subtype t1 t2 = if t1 = t2 then true else match (t1, t2) with
  | (GArray i, GArray j) -> j <= i
  | (GFun (t1, t2), GFun (s1, s2)) -> (suptype t1 s1) && (subtype t2 s2)
  | _ -> false
and suptype t1 t2 = if t1 = t2 then true else match (t1, t2) with
  | (GArray i, GArray j) -> j >= i
  | (GFun (t1, t2), GFun (s1, s2)) -> (subtype t1 s1) && (suptype t2 s2)
  | _ -> false

val welltyctx_imp_findctx : ctx:ctxt -> s:string -> ty:GType -> wellTypedCtxt ctx s ty ->
  Lemma (find ctx s = Some ty)
let rec welltyctx_imp_findctx ctx s ty h = match h with
  | Ctxt_zero s ty xs -> ()
  | Ctxt_succ s ty x xs h' -> welltyctx_imp_findctx xs s ty h'

val findctx_imp_welltyctx : ctx:ctxt -> s:string -> ty:GType -> h:unit{find ctx s = Some ty} ->
  wellTypedCtxt ctx s ty
let rec findctx_imp_welltyctx ctx s ty h = match ctx with
  | (x,y)::xs -> if x = s && y = ty
    then Ctxt_zero s ty xs
    else Ctxt_succ s ty (x,y) xs (findctx_imp_welltyctx xs s ty ())

(* --------------------------- Type inference *)
type IExp =
  | ILit   of int
  | IVar   of int
  | IPlus  of IExp * IExp
  | IMinus of IExp

type TyExp =
  | TUnit
  | TBool
  | TVar   of int
  | TArray of IExp
  | TArrow of TyExp * TyExp

val normalize : IExp -> IExp
let rec normalize iexp = match iexp with
  | IMinus x ->
    begin match normalize x with
      | IMinus x'    -> x'
      | ILit i       -> ILit (-i)
      | IPlus (x, y) -> IPlus (normalize (IMinus x), normalize (IMinus y))
      | x'           -> IMinus x'
    end
  | IPlus (x, y) ->
    begin match (normalize x, normalize y) with
      | (IVar i, y') | (y', IVar i)       -> IPlus (IVar i, y')
      | (ILit i, ILit j)                  -> ILit (i+j)
      | (IPlus (IVar i, x'), y')
      | (y', IPlus (IVar i, x'))          -> IPlus (IVar i, IPlus (x', y'))
      | (IPlus (IMinus (IVar i), x'), y')
      | (y', IPlus (IMinus (IVar i), x')) -> IPlus (IMinus (IVar i), IPlus (x', y'))
      | (x', y')                          -> IPlus (x', y')
    end
  | _ -> iexp

val toTyExp : GType -> Tot TyExp
let rec toTyExp ty = match ty with
  | GUnit -> TUnit
  | GBool -> TBool
  | GVar i -> TVar i
  | GArray n -> TArray (ILit n)
  | GFun (ty1, ty2) -> TArrow (toTyExp ty1, toTyExp ty2)

val toGType : TyExp -> GType
let rec toGType texp = match texp with
  | TUnit -> GUnit
  | TBool -> GBool
  | TVar i -> GVar i
  | TArray iexp ->
    begin match normalize iexp with
      | ILit n -> GArray n
      | _ -> GArray 0
    end
  | TArrow (texp1, texp2) -> GFun (toGType texp1, toGType texp2)

// Constraints (equality or less than) over type expressions
type Cons =
  | ICons of IExp * IExp
  | TCons of TyExp * TyExp

type ctxt' = map string TyExp

val inferTypes : int -> ctxt' -> tm:GExpr -> Tot (int * list Cons * list Cons * TyExp) (decreases %[tm;0])
val inferTypes_lst : int -> ctxt' -> l:list GExpr -> Tot (int * list Cons * list Cons) (decreases %[l;1])
let rec inferTypes top ctx gexp = match gexp with
  | LET (x, t1, t2) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t1 in
    let (top'', ec2, lc2, ty2) = inferTypes top' ((x, ty1)::ctx) t2 in
        (top'', ec1@ec2, lc1@lc2, ty2)
  | LAMBDA (x, ty, t) ->
    let (top', ec1, lc1, ty1) = inferTypes top ((x, (toTyExp ty))::ctx) t in
        (top', ec1, lc1, TArrow (toTyExp ty, ty1))
  | APPLY (t1, t2) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t1 in
    let (top'', ec2, lc2, ty2) = inferTypes top' ctx t2 in
    let e1 = TCons (ty1, TArrow (TVar top'', TVar (top''+1))) in
    let e2 = TCons (ty2, TVar top'') in
      (top''+2, e1::e2::(ec1@ec2), lc1@lc2, TVar (top''+1))
  | IFTHENELSE (t1, t2, t3) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t1 in
    let (top'', ec2, lc2, ty2) = inferTypes top' ctx t2 in
    let (top''', ec3, lc3, ty3) = inferTypes top'' ctx t3 in
    let e1 = TCons (ty1, TBool) in
    let e2 = TCons (ty2, TVar top''') in
    let e3 = TCons (ty3, TVar top''') in
      (top'''+1, e1::e2::e3::(ec1@ec2@ec3), lc1@lc2, TVar top''')
  | SEQUENCE (t1, t2) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t1 in
    let (top'', ec2, lc2, ty2) = inferTypes top' ctx t2 in
    let e1 = TCons (ty1, TUnit) in
      (top'', e1::(ec1@ec2), lc1@lc2, ty2)
  | ASSIGN (t1, t2) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t1 in
    let (top'', ec2, lc2, ty2) = inferTypes top' ctx t2 in
    let e1 = TCons (ty1, TBool) in
    let e2 = TCons (ty2, TBool) in
      (top'', e1::e2::(ec1@ec2), lc1@lc2, TUnit)
  | VAR x -> begin match Par.find ctx x with
    | None -> (top, [], [], TUnit)
    | Some ty -> (top, [], [], ty)
  end
  | UNIT -> (top, [], [], TUnit)
  | BOOL b -> (top, [], [], TBool)
  | XOR (t1, t2) | AND (t1, t2) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t1 in
    let (top'', ec2, lc2, ty2) = inferTypes top' ctx t2 in
    let e1 = TCons (ty1, TBool) in
    let e2 = TCons (ty2, TBool) in
      (top'', e1::e2::(ec1@ec2), lc1@lc2, TBool)
  | ARRAY tlst ->
    let (top', ec, lc) = inferTypes_lst top ctx tlst in
      (top', ec, lc, TArray (ILit (FStar.List.lengthT tlst)))
  | GET_ARRAY (t, i) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t in
    let e1 = TCons (ty1, TArray (IVar top')) in
    let l1 = ICons (ILit i, IVar top') in
      (top'+1, e1::ec1, l1::lc1, TBool)
  | APPEND (t1, t2) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t1 in
    let (top'', ec2, lc2, ty2) = inferTypes top' ctx t2 in
    let e1 = TCons (ty1, TArray (IVar top'')) in
    let e2 = TCons (ty2, TArray (IVar (top''+1))) in
    let e3 = ICons (IVar (top''+2), IPlus (IVar top'', IVar (top''+1))) in
      (top''+3, e1::e2::e3::(ec1@ec2), lc1@lc2, TArray (IVar (top''+2)))
  | ROT (i, t) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t in
    let e1 = TCons (ty1, TArray (IVar top')) in
    let l1 = ICons (ILit (i+1), IVar top') in
      (top'+1, e1::ec1, l1::lc1, TArray (IVar top'))
  | SLICE (t, i, j) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t in
    let e1 = TCons (ty1, TArray (IVar top')) in
    let l1 = ICons (ILit (j+1), IVar top') in
      (top'+1, e1::ec1, l1::lc1, TArray (ILit (j - i + 1)))
  | ASSERT t ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t in
    let e1 = TCons (ty1, TBool) in
      (top', e1::ec1, lc1, TUnit)
  | LOC i -> (top, [], [], TBool)
  | BEXP bexp -> (top, [], [], TBool)
  | _ -> (top, [], [], TUnit)
and inferTypes_lst top ctx lst = match lst with
  | [] -> (top, [], [])
  | x::xs ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx x in
    let (top'', ec2, lc2) = inferTypes_lst top' ctx xs in
    let e1 = TCons (ty1, TBool) in
      (top'', e1::(ec1@ec2), lc1@lc2)


let rec substIExp i iexp x = match x with
  | ILit j -> ILit j
  | IVar j -> if i = j then iexp else IVar j
  | IMinus x -> substIExp i iexp x
  | IPlus (x, y) -> IPlus (substIExp i iexp x, substIExp i iexp y)

let rec substTExp i texp x = match x with
  | TUnit -> TUnit
  | TBool -> TBool
  | TVar j -> if i = j then texp else TVar j
  | TArray iexp -> TArray iexp
  | TArrow (x, y) -> TArrow (substTExp i texp x, substTExp i texp y)

let rec substIExpInTExp i iexp x = match x with
  | TArray iexp' -> TArray (substIExp i iexp iexp')
  | TArrow (x, y) -> TArrow (substIExpInTExp i iexp x, substIExpInTExp i iexp y)
  | _ -> x

let rec iSubst i iexp cons = match cons with
  | [] -> []
  | (ICons c)::xs -> (ICons (substIExp i iexp (fst c), substIExp i iexp (snd c)))::(iSubst i iexp xs)
  | x::xs -> x::(iSubst i iexp xs)

let rec tSubst i texp cons = match cons with
  | [] -> []
  | (TCons c)::xs -> (TCons (substTExp i texp (fst c), substTExp i texp (snd c)))::(tSubst i texp xs)
  | x::xs -> x::(tSubst i texp xs)

val mergeLower : int -> int -> list Cons -> IExp
let rec mergeLower i j bnds = match bnds with
  | [] -> ILit i
  | (ICons (ILit i', i2))::xs ->
    begin match i2 with
      | IVar j' -> if j = j' then mergeLower (max i i') j xs else mergeLower i j xs
      | _ -> mergeLower i j xs
    end
  | _ -> failwith "impossible"

let rec checkBounds check subs = match check with
  | [] -> Some subs
  | (ICons (ILit i, i2))::xs ->
    begin match (normalize i2) with
      | ILit j -> if i < j then checkBounds xs subs else None
      | _ -> None
    end
  | _ -> failwith "impossible"

let rec unify_bnds bnds check subs = match bnds with
  | [] -> checkBounds check subs
  | (ICons (ILit i, i2))::xs ->
    begin match i2 with
      | IVar j ->
        let sub = mergeLower i j xs in
          unify_bnds (iSubst j sub xs) (iSubst j sub check) (iSubst j sub subs)
      | _ -> unify_bnds xs ((ICons (ILit i, i2))::check) subs
    end
  | _ -> failwith "impossible"

let rec unify_eq eqs bnds subs = match eqs with
  | [] -> unify_bnds bnds [] subs
  | (ICons (i1, i2))::xs ->
    begin match (normalize i1, normalize i2) with
      | (IVar i, iexp)
      | (iexp, IVar i) ->
        unify_eq (iSubst i iexp xs) (iSubst i iexp bnds) (iSubst i iexp subs)
      | (ILit i, ILit j) ->
        if i = j then unify_eq xs bnds subs else None
      | (IPlus (IVar i, y), iexp) | (iexp, IPlus (IVar i, y)) ->
        let sub = IPlus (IMinus y, iexp) in
          unify_eq (iSubst i sub eqs) (iSubst i sub bnds) (iSubst i sub subs)
      | (IPlus (IMinus (IVar i), y), iexp) | (iexp, IPlus (IMinus (IVar i), y)) ->
        let sub = IPlus (y, iexp) in
          unify_eq (iSubst i sub eqs) (iSubst i sub bnds) (iSubst i sub subs)
      | _ -> None
    end
  | (TCons (t1, t2))::xs ->
    begin match (t1, t2) with
      | (TVar i, ty)
      | (ty, TVar i) ->
        unify_eq (tSubst i ty xs) (tSubst i ty bnds) ((TCons (TVar i, ty))::subs)
      | (TUnit, TUnit) -> unify_eq xs bnds subs
      | (TBool, TBool) -> unify_eq xs bnds subs
      | (TArray iexp, TArray iexp') ->
        unify_eq ((ICons (iexp, iexp'))::xs) bnds subs
      | (TArrow (t1, t2), TArrow (s1, s2)) ->
        unify_eq ((TCons (t1, s1))::(TCons (t2, s2))::xs) bnds subs
      | _ -> None
    end

let rec applySubs subs tm = match subs with
  | [] -> tm
  | (TCons (TVar i, texp))::xs -> applySubs xs (substTyInGExpr tm i (toGType texp))
  | _ -> failwith "impossible"

let annotate tm =
  let top = varMaxTm tm in
  let (_, eqs, bnds, typ) = inferTypes (top+1) [] tm in
  let res = unify_eq eqs bnds [] in
    match res with
      | None -> Err "Could not infer types"
      | Some subs -> Val (applySubs subs tm)

// (Relational) semantics -- Needs to be updated before using
(*
type env  = list (string * GExpr)
type heap = list bool

type inEnv : env -> string -> GExpr -> Type =
  | Env_zero : s:string -> tm:GExpr -> xs:env -> inEnv ((s, tm)::xs) s tm
  | Env_succ : s:string -> tm:GExpr -> x:(string * GExpr){~(fst x = s)} -> xs:env ->
               inEnv xs s tm ->
               inEnv (x::xs) s tm

type inHeap : heap -> int -> bool -> Type =
  | Heap_zero : b:bool -> xs:heap -> inHeap (b::xs) 0 b
  | Heap_succ : i:int -> b:bool -> b':bool -> xs:heap ->
                inHeap xs i b ->
                inHeap (b'::xs) (i+1) b

val isVal : gexp:GExpr -> Tot bool (decreases %[gexp;1])
val isVal_lst : lst:list GExpr -> Tot bool (decreases %[lst;0])
let rec isVal tm = match tm with
  | UNIT          -> true
  | LAMBDA (s, ty, t) -> true
  | LOC i         -> true
  | ARRAY lst     -> isVal_lst lst
  | _             -> false
and isVal_lst lst = match lst with
  | [] -> true
  | x::xs -> isVal x && isVal_lst xs

val isVal_lst_append : lst1:list GExpr -> lst2:list GExpr ->
  Lemma (requires (isVal_lst lst1 /\ isVal_lst lst2))
        (ensures  (isVal_lst (lst1@lst2)))
  [SMTPat (isVal_lst (lst1@lst2))]
let rec isVal_lst_append lst1 lst2 = match lst1 with
  | [] -> ()
  | x::xs -> isVal_lst_append xs lst2

type config = GExpr * env * heap
type valconfig = c:(GExpr * heap){isVal (fst c)}

// (Canonical) relational semantics
type evalR : config -> valconfig -> Type =
  | EvLet :
      #s:string -> #t1:GExpr -> #t2:GExpr -> #env:env -> #st:heap ->
      #v1:GExpr -> #st':heap -> #v2:GExpr -> #st'':heap ->
      evalR (t1, env, st)           (v1, st') ->
      evalR (t2, (s, v1)::env, st') (v2, st'') ->
      evalR (LET (s, t1, t2), env, st)  (v2, st'')
  | EvApp :
      #t1:GExpr -> #t2:GExpr -> #s:string -> #env:env -> #st:heap -> #ty:GType ->
      #t:GExpr -> #st':heap -> #v:GExpr -> #st'':heap -> #v':GExpr -> #st''':heap ->
      evalR (t1, env, st)          (LAMBDA (s, ty, t), st') ->
      evalR (t2, env, st')         (v, st'') ->
      evalR (t, (s,v)::env, st'')  (v', st''') ->
      evalR (APPLY (t1, t2), env, st) (v', st''')
  | EvSeq :
      #t1:GExpr -> #t2:GExpr -> #env:env -> #st:heap ->
      #st':heap -> #v:GExpr -> #st'':heap ->
      evalR (t1, env, st)             (UNIT, st') ->
      evalR (t2, env, st')            (v, st'') ->
      evalR (SEQUENCE (t1, t2), env, st) (v, st'')
  | EvXor :
      #t1:GExpr -> #t2:GExpr -> #env:env -> #st:heap ->
      #l:int -> #st':heap -> #b:bool -> #l':int -> #st'':heap -> #b':bool ->
      inHeap st' l b ->
      inHeap st'' l' b' ->
      evalR (t1, env, st)        (LOC l, st') ->
      evalR (t2, env, st')       (LOC l', st'') ->
      evalR (XOR (t1, t2), env, st) (LOC (FStar.List.length st''), (b <> b')::st'')
  | EvAnd :
      #t1:GExpr -> #t2:GExpr -> #env:env -> #st:heap ->
      #l:int -> #st':heap -> #b:bool -> #l':int -> #st'':heap -> #b':bool ->
      inHeap st' l b ->
      inHeap st'' l' b' ->
      evalR (t1, env, st)        (LOC l, st')   ->
      evalR (t2, env, st')       (LOC l', st'') ->
      evalR (AND (t1, t2), env, st) (LOC (FStar.List.length st''), (b && b')::st'')
  | EvBoo :
      #b:bool -> #env:env -> #st:heap ->
      evalR (BOOL b, env, st) (LOC (FStar.List.length st), b::st)
  | EvApd :
      #t1:GExpr -> #t2:GExpr -> #env:env -> #st:heap ->
      #lst1:list GExpr -> #st':heap -> #lst2:list GExpr -> #st'':heap ->
      evalR (t1, env, st)           (ARRAY lst1, st') ->
      evalR (t2, env, st')          (ARRAY lst2, st'') ->
      evalR (APPEND (t1, t2), env, st) (ARRAY (lst1@lst2), st'')
  | EvRot :
      #t:GExpr -> #i:int -> #env:env -> #st:heap ->
      #lst:list GExpr -> #st':heap ->
      b2t (i < FStar.List.length lst) ->
      evalR (t, env, st)       (ARRAY lst, st') ->
      evalR (ROT (i, t), env, st) (ARRAY (rotate lst i), st')
  | EvSlc :
      #t:GExpr -> #i:int -> #j:int -> #env:env -> #st:heap ->
      #lst:list GExpr -> #st':heap ->
      b2t (j < FStar.List.length lst && j >= i) ->
      evalR (t, env, st)           (ARRAY lst, st') ->
      evalR (SLICE (t, i, j), env, st) (ARRAY (slice lst i j), st')
  | EvArr :
      #x:GExpr -> #xs:list GExpr -> #env:env -> #st:heap ->
      #v:GExpr -> #st':heap -> #vs:list GExpr -> #st'':heap ->
      evalR (x, env, st)           (v, st') ->
      evalR (ARRAY xs, env, st')   (ARRAY vs, st'') ->
      evalR (ARRAY (x::xs), env, st) (ARRAY (v::vs), st'')
  (*| EvSta :
      evalR (t1, env, st)           (ARRAY lst, st') ->

      evalR (t2, env, st')          (LOC l, st'') ->
      inHeap st'' l b ->
  | EvGta :
      #t:GExpr -> #i:int -> #env:env -> #st:heap ->
      #lst:list GExpr -> #st':heap ->
      evalR (t, env, st)       (ARRAY lst, st') -> i < FStar.List.length lst ->
      evalR (ROT t i, env, st) (ARRAY (rotate lst i), st')
  | EvStv :*)
  | EvGtv :
      #s:string -> #env:env -> #st:heap -> #v:GExpr ->
      inEnv env s v ->
      evalR (VAR s, env, st) (v, st)
  | EvAssert :
      #t:GExpr -> #env:env -> #st:heap -> #l:int -> #st':heap ->
      evalR (t, env, st)        (LOC l, st') ->
      evalR (ASSERT t, env, st) (UNIT, st')
*)
