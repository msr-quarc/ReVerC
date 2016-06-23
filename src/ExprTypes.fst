(** Abstract syntax & general Revs utilities *)
module ExprTypes

(* Abstract syntax of Revs, along with utilities. Eventually a
   relational definition of the semantics should go here *)

open Set
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
  | ARRAY      of list GExpr
  | GET_ARRAY  of GExpr * int
  | APPEND     of GExpr * GExpr
  | ROT        of int * GExpr
  | SLICE      of GExpr * int * int
  | ASSERT     of GExpr
  // Compiler use only
  | LOC        of int
  | BEXP       of BoolExp

val height       : tm:GExpr -> Tot int (decreases %[tm;1])
val height_lst   : tlst:(list GExpr) -> Tot int (decreases %[tlst;0])
val freeIn       : x:string -> tm:GExpr -> Tot bool (decreases %[tm;0])
val freeIn_lst   : x:string -> lst:list GExpr -> Tot bool (decreases %[lst;1])
val freeVars     : tm:GExpr -> Tot (set string) (decreases %[tm;0])
val locsAcc      : set int -> tm:GExpr -> Tot (set int) (decreases %[tm;0])
val locsAcc_lst  : set int -> lst:list GExpr -> Tot (set int) (decreases %[lst;1])
val locs         : tm:GExpr -> Tot (set int) (decreases %[tm;0])
val varMaxTy     : ty:GType -> Tot int (decreases ty)
val varMaxTm     : tm:GExpr -> Tot int (decreases %[tm;0])
val varMaxTm_lst : lst:list GExpr -> Tot int (decreases %[lst;1])

val replicate       : int -> string -> Tot string
val append'         : list string -> list string -> Tot (list string)
val appFront        : string -> list string -> Tot (l:(list string){List.lengthT l > 0})
val appBack         : string -> list string -> Tot (l:(list string){List.lengthT l > 0})
val indent          : int -> list string -> Tot (list string)
val brackets        : list string -> Tot (list string)
val hdT             : l:(list 'a){List.lengthT l >= 1} -> Tot 'a
val tlT             : l:(list 'a){List.lengthT l >= 1} -> Tot (list 'a)
val prettyPrintTy   : GType -> Tot string
val prettyPrint     : GExpr -> Tot (l:(list string){List.lengthT l > 0})
val prettyPrint_lst : list GExpr -> Tot (list (list string))
val show            : GExpr -> Tot string

val substTy            : ty:GType -> int -> GType -> Tot GType (decreases ty)
val substGExpr         : tm:GExpr -> string -> GExpr -> Tot GExpr (decreases %[tm;0])
val substGExpr_lst     : l:list GExpr -> string -> GExpr -> Tot (list GExpr) (decreases %[l;1])
val substTyInGExpr     : tm:GExpr -> int -> GType -> Tot GExpr (decreases %[tm;0])
val substTyInGExpr_lst : l:list GExpr -> int -> GType -> Tot (list GExpr) (decreases %[l;1])

(* Structural properties for helping with proofs *)
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
  | ASSERT t -> locsAcc lset t
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
  | ASSERT t -> varMaxTm t
  | _ -> 0
and varMaxTm_lst lst = match lst with
  | [] -> 0
  | x::xs -> max (varMaxTm x) (varMaxTm_lst xs)

(* Pretty printing *)
let rec replicate i s =
  if i <= 0 then "" else String.strcat s (replicate (i-1) s)
let rec append' lst1 lst2 = match (lst1, lst2) with
  | ([], _)        -> lst2
  | (_, [])        -> lst1
  | (x::[], y::ys) -> (String.strcat x y)::ys
  | (x::xs, _)     -> x::(append' xs lst2)
let appFront s lst = match lst with
  | []    -> [s]
  | x::xs -> (String.strcat s x)::xs
let rec appBack s lst = match lst with
  | []    -> [s]
  | x::[] -> (String.strcat x s)::[]
  | x::xs -> appBack s xs
let indent i l = List.mapT (fun s -> String.strcat (replicate i " ") s) l
let brackets s = appFront "(" (appBack ")" s)

let hdT l = match l with
  | x::xs -> x
let tlT l = match l with
  | x::xs -> xs

let rec prettyPrintTy ty = match ty with
  | GUnit -> "unit"
  | GBool -> "bool"
  | GVar i -> Prims.string_of_int i
  | GArray n -> String.strcat "vec " (Prims.string_of_int n)
  | GConst ty -> String.strcat "const " (prettyPrintTy ty)
  | GFun (ty1, ty2) -> begin match ty1 with
    | GFun _ -> String.strcat "("
               (String.strcat (prettyPrintTy ty1)
               (String.strcat ") -> " (prettyPrintTy ty2)))
    | _ -> String.strcat (prettyPrintTy ty1)
          (String.strcat " -> " (prettyPrintTy ty2))
    end

let rec prettyPrint gexp = match gexp with
  | LET (s, t1, t2) ->
      let st1 = prettyPrint t1 in
      let st2 = prettyPrint t2 in
        [String.strcat "let " (String.strcat s (String.strcat " = " (hdT st1)))] @
        ((indent 2 (tlT st1)) @ st2)
  | LAMBDA (s, ty, t) ->
      let st = prettyPrint t in
      let sty = prettyPrintTy ty in
        [String.strcat "\ " (String.strcat s (String.strcat ":" (String.strcat sty (String.strcat " . " (hdT st)))))] @
        (indent 2 (tlT st))
  | APPLY (t1, t2) ->
      let st1 = prettyPrint t1 in
      let st2 = prettyPrint t2 in
        if forSomeT (fun l -> List.lengthT l > 1) ([st1;st2])
        then (brackets st1) @ (indent 2 st2)
        else [String.strcat (hdT st1) (String.strcat " " (hdT st2))]
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
      //let stlst = List.mapT prettyPrint tlst in -- Doesn't work with > 0 annotation
      let stlst = prettyPrint_lst tlst in
        if forSomeT (fun l -> List.lengthT l > 1) stlst
        then
          let f stlst lst = stlst @ (appBack "," (indent 2 lst)) in
            ["["] @ (List.fold_leftT f [] stlst) @ ["]"]
        else 
          let f str lst = match lst with
            | [] -> str
            | x::xs -> String.strcat str (String.strcat "," x)
          in
            [String.strcat (List.fold_leftT f "[" stlst) "]"]
  | GET_ARRAY (t, i) ->
      let st = prettyPrint t in
        appBack (String.strcat ".[" (String.strcat (Prims.string_of_int i) "]")) st
  | APPEND (t1, t2) ->
      let st1 = prettyPrint t1 in
      let st2 = prettyPrint t2 in
        if forSomeT (fun l -> List.lengthT l > 1) [st1;st2]
        then ["append"] @ (indent 2 st1) @ (indent 2 st2)
        else [String.strcat "append" (String.strcat (hdT st1) (String.strcat " " (hdT st2)))]
  | ROT (i, t) ->
      let st = prettyPrint t in
        appFront (String.strcat "rot " (Prims.string_of_int i)) st
  | SLICE (t, i, j) ->
      let st = prettyPrint t in
        appBack (String.strcat ".["
                (String.strcat (Prims.string_of_int i)
                (String.strcat ".."
                (String.strcat (Prims.string_of_int j) "]")))) st
  | ASSERT t ->
      let st = prettyPrint t in
        appFront "allege " st
  | LOC i -> [String.strcat "loc " (Prims.string_of_int i)]
  | BEXP bexp -> [prettyPrintBexp bexp]
  | _ -> ["NOT SUPPORTED"]
and prettyPrint_lst tlst =  match tlst with
  | [] -> []
  | x::xs -> (prettyPrint x)::(prettyPrint_lst xs)

let show gexp =
  let str = prettyPrint gexp in
  String.concat "\n" str

let print gexp =
  let str = prettyPrint gexp in
  List.iter IO.print_string str

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
  | ASSERT t -> ASSERT (substGExpr t s tm')
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
  | ASSERT t -> ASSERT (substTyInGExpr t k ty)
  | _ -> tm
and substTyInGExpr_lst lst k ty = match lst with
  | [] -> []
  | x::xs -> (substTyInGExpr x k ty)::(substTyInGExpr_lst xs k ty)

(* (Relational) semantics -- commented as it's no longer correct *)
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

(* (Canonical) relational semantics *)
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
