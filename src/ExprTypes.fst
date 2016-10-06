(** Abstract syntax & general Revs utilities *)
module ExprTypes

open FStar.Set
open SetExtra
open Util
open BoolExp

(* Abstract syntax of Revs, along with utilities. Eventually a
   relational definition of the semantics should go here *)

type gType =
  | GUnit
  | GBool
  | GArray of int
  | GFun of gType * gType
  | GConst of gType
  // Compiler use only
  | GVar of int

type gExpr =
  | LET        of string * gExpr * gExpr
  | LAMBDA     of string * gType * gExpr
  | APPLY      of gExpr * gExpr
  | IFTHENELSE of gExpr * gExpr * gExpr
  | SEQUENCE   of gExpr * gExpr
  | ASSIGN     of gExpr * gExpr
  | VAR        of string
  | UNIT
  | BOOL       of bool
  | XOR        of gExpr * gExpr
  | AND        of gExpr * gExpr
  | ARRAY      of list gExpr
  | GET_ARRAY  of gExpr * int
  | APPEND     of gExpr * gExpr
  | ROT        of int * gExpr
  | SLICE      of gExpr * int * int
  | ASSERT     of gExpr
  // Compiler use only
  | LOC        of int
  | BEXP       of boolExp

val height       : tm:gExpr -> Tot int (decreases %[tm;1])
val height_lst   : tlst:(list gExpr) -> Tot int (decreases %[tlst;0])
val freeIn       : x:string -> tm:gExpr -> Tot bool (decreases %[tm;0])
val freeIn_lst   : x:string -> lst:list gExpr -> Tot bool (decreases %[lst;1])
val freeVars     : tm:gExpr -> Tot (set string) (decreases %[tm;0])
val locsAcc      : set int -> tm:gExpr -> Tot (set int) (decreases %[tm;0])
val locsAcc_lst  : set int -> lst:list gExpr -> Tot (set int) (decreases %[lst;1])
val locs         : tm:gExpr -> Tot (set int) (decreases %[tm;0])
val varMaxTy     : ty:gType -> Tot int (decreases ty)
val varMaxTm     : tm:gExpr -> Tot int (decreases %[tm;0])
val varMaxTm_lst : lst:list gExpr -> Tot int (decreases %[lst;1])

val replicate       : int -> string -> Tot string
val append'         : list string -> list string -> Tot (list string)
val appFront        : string -> list string -> Tot (l:(list string){List.lengthT l > 0})
val appBack         : string -> list string -> Tot (l:(list string){List.lengthT l > 0})
val indent          : int -> list string -> Tot (list string)
val brackets        : list string -> Tot (list string)
val hdT             : l:(list 'a){List.lengthT l >= 1} -> Tot 'a
val tlT             : l:(list 'a){List.lengthT l >= 1} -> Tot (list 'a)
val prettyPrintTy   : gType -> Tot string
val prettyPrint     : gExpr -> Tot (l:(list string){List.lengthT l > 0})
val prettyPrint_lst : list gExpr -> Tot (list (list string))
val show            : gExpr -> Tot string

val substTy            : ty:gType -> int -> gType -> Tot gType (decreases ty)
val substgExpr         : tm:gExpr -> string -> gExpr -> Tot gExpr (decreases %[tm;0])
val substgExpr_lst     : l:list gExpr -> string -> gExpr -> Tot (list gExpr) (decreases %[l;1])
val substTyIngExpr     : tm:gExpr -> int -> gType -> Tot gExpr (decreases %[tm;0])
val substTyIngExpr_lst : l:list gExpr -> int -> gType -> Tot (list gExpr) (decreases %[l;1])

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

let rec substgExpr tm s tm' = match tm with
  | LET (x, t1, t2) ->
    if x = s then LET (x, substgExpr t1 s tm', t2)
    else LET (x, substgExpr t1 s tm', substgExpr t2 s tm')
  | LAMBDA (x, ty, t) ->
    if x = s then tm else LAMBDA (x, ty, substgExpr t s tm')
  | APPLY (t1, t2) -> APPLY (substgExpr t1 s tm', substgExpr t2 s tm')
  | IFTHENELSE (t1, t2, t3) ->
    IFTHENELSE (substgExpr t1 s tm', substgExpr t2 s tm', substgExpr t3 s tm')
  | SEQUENCE (t1, t2) -> SEQUENCE (substgExpr t1 s tm', substgExpr t2 s tm')
  | ASSIGN (t1, t2) -> ASSIGN (substgExpr t1 s tm', substgExpr t2 s tm')
  | VAR x -> if x = s then tm' else tm
  | XOR (t1, t2) -> XOR (substgExpr t1 s tm', substgExpr t2 s tm')
  | AND (t1, t2) -> AND (substgExpr t1 s tm', substgExpr t2 s tm')
  | ARRAY tlst -> ARRAY (substgExpr_lst tlst s tm')
  | GET_ARRAY (t, i) -> GET_ARRAY (substgExpr t s tm', i)
  | APPEND (t1, t2) -> APPEND (substgExpr t1 s tm', substgExpr t2 s tm')
  | ROT (i, t) -> ROT (i, substgExpr t s tm')
  | SLICE (t, i, j) -> SLICE (substgExpr t s tm', i, j)
  | ASSERT t -> ASSERT (substgExpr t s tm')
  | _ -> tm
and substgExpr_lst lst s tm' = match lst with
  | [] -> []
  | x::xs -> (substgExpr x s tm')::(substgExpr_lst xs s tm')

let rec substTyIngExpr tm k ty = match tm with
  | LET (x, t1, t2) -> LET (x, substTyIngExpr t1 k ty, substTyIngExpr t2 k ty)
  | LAMBDA (x, ty', t) -> LAMBDA (x, substTy ty' k ty, substTyIngExpr t k ty)
  | APPLY (t1, t2) -> APPLY (substTyIngExpr t1 k ty, substTyIngExpr t2 k ty)
  | IFTHENELSE (t1, t2, t3) -> IFTHENELSE (substTyIngExpr t1 k ty, substTyIngExpr t2 k ty, substTyIngExpr t3 k ty)
  | SEQUENCE (t1, t2) -> SEQUENCE (substTyIngExpr t1 k ty, substTyIngExpr t2 k ty)
  | ASSIGN (t1, t2) -> ASSIGN (substTyIngExpr t1 k ty, substTyIngExpr t2 k ty)
  | XOR (t1, t2) -> XOR (substTyIngExpr t1 k ty, substTyIngExpr t2 k ty)
  | AND (t1, t2) -> AND (substTyIngExpr t1 k ty, substTyIngExpr t2 k ty)
  | ARRAY tlst -> ARRAY (substTyIngExpr_lst tlst k ty)
  | GET_ARRAY (t, i) -> GET_ARRAY (substTyIngExpr t k ty, i)
  | APPEND (t1, t2) -> APPEND (substTyIngExpr t1 k ty, substTyIngExpr t2 k ty)
  | ROT (i, t) -> ROT (i, substTyIngExpr t k ty)
  | SLICE (t, i, j) -> SLICE (substTyIngExpr t k ty, i, j)
  | ASSERT t -> ASSERT (substTyIngExpr t k ty)
  | _ -> tm
and substTyIngExpr_lst lst k ty = match lst with
  | [] -> []
  | x::xs -> (substTyIngExpr x k ty)::(substTyIngExpr_lst xs k ty)

(* (Relational) semantics -- commented as it's no longer correct *)
(*
type env  = list (string * gExpr)
type heap = list bool

type inEnv : env -> string -> gExpr -> Type =
  | Env_zero : s:string -> tm:gExpr -> xs:env -> inEnv ((s, tm)::xs) s tm
  | Env_succ : s:string -> tm:gExpr -> x:(string * gExpr){~(fst x = s)} -> xs:env ->
               inEnv xs s tm ->
               inEnv (x::xs) s tm

type inHeap : heap -> int -> bool -> Type =
  | Heap_zero : b:bool -> xs:heap -> inHeap (b::xs) 0 b
  | Heap_succ : i:int -> b:bool -> b':bool -> xs:heap ->
                inHeap xs i b ->
                inHeap (b'::xs) (i+1) b

val isVal : gexp:gExpr -> Tot bool (decreases %[gexp;1])
val isVal_lst : lst:list gExpr -> Tot bool (decreases %[lst;0])
let rec isVal tm = match tm with
  | UNIT          -> true
  | LAMBDA (s, ty, t) -> true
  | LOC i         -> true
  | ARRAY lst     -> isVal_lst lst
  | _             -> false
and isVal_lst lst = match lst with
  | [] -> true
  | x::xs -> isVal x && isVal_lst xs

val isVal_lst_append : lst1:list gExpr -> lst2:list gExpr ->
  Lemma (requires (isVal_lst lst1 /\ isVal_lst lst2))
        (ensures  (isVal_lst (lst1@lst2)))
  [SMTPat (isVal_lst (lst1@lst2))]
let rec isVal_lst_append lst1 lst2 = match lst1 with
  | [] -> ()
  | x::xs -> isVal_lst_append xs lst2

type config = gExpr * env * heap
type valconfig = c:(gExpr * heap){isVal (fst c)}

(* (Canonical) relational semantics *)
type evalR : config -> valconfig -> Type =
  | EvLet :
      #s:string -> #t1:gExpr -> #t2:gExpr -> #env:env -> #st:heap ->
      #v1:gExpr -> #st':heap -> #v2:gExpr -> #st'':heap ->
      evalR (t1, env, st)           (v1, st') ->
      evalR (t2, (s, v1)::env, st') (v2, st'') ->
      evalR (LET (s, t1, t2), env, st)  (v2, st'')
  | EvApp :
      #t1:gExpr -> #t2:gExpr -> #s:string -> #env:env -> #st:heap -> #ty:gType ->
      #t:gExpr -> #st':heap -> #v:gExpr -> #st'':heap -> #v':gExpr -> #st''':heap ->
      evalR (t1, env, st)          (LAMBDA (s, ty, t), st') ->
      evalR (t2, env, st')         (v, st'') ->
      evalR (t, (s,v)::env, st'')  (v', st''') ->
      evalR (APPLY (t1, t2), env, st) (v', st''')
  | EvSeq :
      #t1:gExpr -> #t2:gExpr -> #env:env -> #st:heap ->
      #st':heap -> #v:gExpr -> #st'':heap ->
      evalR (t1, env, st)             (UNIT, st') ->
      evalR (t2, env, st')            (v, st'') ->
      evalR (SEQUENCE (t1, t2), env, st) (v, st'')
  | EvXor :
      #t1:gExpr -> #t2:gExpr -> #env:env -> #st:heap ->
      #l:int -> #st':heap -> #b:bool -> #l':int -> #st'':heap -> #b':bool ->
      inHeap st' l b ->
      inHeap st'' l' b' ->
      evalR (t1, env, st)        (LOC l, st') ->
      evalR (t2, env, st')       (LOC l', st'') ->
      evalR (XOR (t1, t2), env, st) (LOC (FStar.List.length st''), (b <> b')::st'')
  | EvAnd :
      #t1:gExpr -> #t2:gExpr -> #env:env -> #st:heap ->
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
      #t1:gExpr -> #t2:gExpr -> #env:env -> #st:heap ->
      #lst1:list gExpr -> #st':heap -> #lst2:list gExpr -> #st'':heap ->
      evalR (t1, env, st)           (ARRAY lst1, st') ->
      evalR (t2, env, st')          (ARRAY lst2, st'') ->
      evalR (APPEND (t1, t2), env, st) (ARRAY (lst1@lst2), st'')
  | EvRot :
      #t:gExpr -> #i:int -> #env:env -> #st:heap ->
      #lst:list gExpr -> #st':heap ->
      b2t (i < FStar.List.length lst) ->
      evalR (t, env, st)       (ARRAY lst, st') ->
      evalR (ROT (i, t), env, st) (ARRAY (rotate lst i), st')
  | EvSlc :
      #t:gExpr -> #i:int -> #j:int -> #env:env -> #st:heap ->
      #lst:list gExpr -> #st':heap ->
      b2t (j < FStar.List.length lst && j >= i) ->
      evalR (t, env, st)           (ARRAY lst, st') ->
      evalR (SLICE (t, i, j), env, st) (ARRAY (slice lst i j), st')
  | EvArr :
      #x:gExpr -> #xs:list gExpr -> #env:env -> #st:heap ->
      #v:gExpr -> #st':heap -> #vs:list gExpr -> #st'':heap ->
      evalR (x, env, st)           (v, st') ->
      evalR (ARRAY xs, env, st')   (ARRAY vs, st'') ->
      evalR (ARRAY (x::xs), env, st) (ARRAY (v::vs), st'')
  (*| EvSta :
      evalR (t1, env, st)           (ARRAY lst, st') ->

      evalR (t2, env, st')          (LOC l, st'') ->
      inHeap st'' l b ->
  | EvGta :
      #t:gExpr -> #i:int -> #env:env -> #st:heap ->
      #lst:list gExpr -> #st':heap ->
      evalR (t, env, st)       (ARRAY lst, st') -> i < FStar.List.length lst ->
      evalR (ROT t i, env, st) (ARRAY (rotate lst i), st')
  | EvStv :*)
  | EvGtv :
      #s:string -> #env:env -> #st:heap -> #v:gExpr ->
      inEnv env s v ->
      evalR (VAR s, env, st) (v, st)
  | EvAssert :
      #t:gExpr -> #env:env -> #st:heap -> #l:int -> #st':heap ->
      evalR (t, env, st)        (LOC l, st') ->
      evalR (ASSERT t, env, st) (UNIT, st')
*)
