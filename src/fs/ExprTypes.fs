module ExprTypes

open Util
open BoolExp

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
  | ARRAY      of list<GExpr>
  | GET_ARRAY  of GExpr * int
  | APPEND     of GExpr * GExpr
  | ROT        of int * GExpr
  | SLICE      of GExpr * int * int
  | CLEAN      of GExpr
  | ASSERT     of GExpr
  // Compiler use only
  | LOC        of int
  | BEXP       of BoolExp

//val freeIn : x:string -> tm:GExpr -> Tot bool (decreases %[tm;0])
//val freeIn_lst : x:string -> lst:list GExpr -> Tot bool (decreases %[lst;1])
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
  | CLEAN t -> freeIn x t
  | ASSERT t -> freeIn x t
  | LOC i -> false
  | BEXP bexp -> false
  | _ -> false
and freeIn_lst x lst = match lst with
  | [] -> false
  | t::xs -> freeIn x t || freeIn_lst x xs

//val freeVars : tm:GExpr -> Tot (set string) (decreases %[tm;0])
let freeVars tm = fun x -> freeIn x tm

// Pretty printing
//val replicate : int -> string -> Tot string
//val append'   : list string -> list string -> Tot (list string)
//val appFront  : string -> list string -> Tot (list string)
//val appBack   : string -> list string -> Tot (list string)

let rec replicate i s =
  if i <= 0 then "" else s ^ (replicate (i-1) s)
let rec append' lst1 lst2 = match (lst1, lst2) with
  | ([], _)        -> lst2
  | (_, [])        -> lst1
  | (x::[], y::ys) -> (x ^ y)::ys
  | (x::xs, _)     -> x::(append' xs lst2)
let appFront s lst = match lst with
  | []    -> [s]
  | x::xs -> (s ^ x)::xs
let rec appBack s lst = match lst with
  | []    -> [s]
  | x::[] -> (x ^ s)::[]
  | x::xs -> appBack s xs

//val hdT : l:(list 'a){List.lengthT l >= 1} -> Tot 'a
//val tlT : l:(list 'a){List.lengthT l >= 1} -> Tot (list 'a)
let hdT l = match l with
  | x::xs -> x
let tlT l = match l with
  | x::xs -> xs

//val prettyPrintTy : GType -> string
let rec prettyPrintTy ty = match ty with
  | GUnit -> "unit"
  | GBool -> "bool"
  | GVar i -> IO.string_of_int i
  | GArray n -> "vec " ^ (IO.string_of_int n)
  | GFun (ty1, ty2) -> begin match ty1 with
    | GFun _ -> "(" ^ (prettyPrintTy ty1) ^ ") -> " ^ (prettyPrintTy ty2)
    | _ -> (prettyPrintTy ty1) ^ " -> " ^ (prettyPrintTy ty2)
    end

//val prettyPrint : GExpr -> list string
let rec prettyPrint gexp =
  let indent i = List.map (fun s -> (replicate i " ") ^ s) in
  let brackets s = appFront "(" (appBack ")" s) in
  let flatten s lst = String.concat s (List.map List.head lst) in
  match gexp with
    | LET (s, t1, t2) ->
        let st1 = prettyPrint t1 in
        let st2 = prettyPrint t2 in
          ["let " ^ s ^ " = " ^ (List.head st1)] @
          (indent 2 (List.tail st1)) @ st2
    | LAMBDA (s, ty, t) ->
        let st = prettyPrint t in
        let sty = prettyPrintTy ty in
          ["fun " ^ s ^ ":" ^ sty ^ " . " ^ (List.head st)] @
          (indent 2 (List.tail st))
    | APPLY (t1, t2) ->
        let st1 = prettyPrint t1 in
        let st2 = prettyPrint t2 in
          if for_someT (fun l -> List.length l > 1) ([st1;st2])
          then (brackets st1) @ (indent 2 st2)
          else [(List.head st1) ^ " " ^ (flatten " " [st2])]
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
        let stlst = List.map prettyPrint tlst in
          if for_someT (fun l -> List.length l > 1) stlst
          then ["["] @ (List.foldBack (fun lst acc -> (appBack "," (indent 2 lst)) @ acc) stlst []) @ ["]"]
          else ["[" ^ (flatten "," stlst) ^ "]"]
    | GET_ARRAY (t, i) ->
        let st = prettyPrint t in
          appBack (".[" ^ (IO.string_of_int i) ^ "]") st
    | APPEND (t1, t2) ->
        let st1 = prettyPrint t1 in
        let st2 = prettyPrint t2 in
          if for_someT (fun l -> List.length l > 1) [st1;st2]
          then ["append "] @ (indent 2 st1) @ (indent 2 st2)
          else ["append " ^ (List.head st1) ^ " " ^ (List.head st2)]
    | ROT (i, t) ->
        let st = prettyPrint t in
          appFront ("rot " ^ (IO.string_of_int i)) st
    | SLICE (t, i, j) ->
        let st = prettyPrint t in
          appBack (".[" ^ (IO.string_of_int i) ^ ".." ^ (IO.string_of_int j) ^ "]") st
    | CLEAN t ->
        let st = prettyPrint t in
          appFront "clean " st
    | ASSERT t ->
        let st = prettyPrint t in
          appFront "allege " st
    | LOC i -> ["loc " ^ (IO.string_of_int i)]
    | BEXP bexp -> [prettyPrintBexp bexp]
    | _ -> []

//val show : GExpr -> Tot string
let show gexp =
  let str = prettyPrint gexp in
  String.concat "\n" str

let print gexp =
  let str = prettyPrint gexp in
  List.iter IO.print_string str

// Substitutions
//val substTy : ty:GType -> int -> GType -> Tot GType (decreases ty)
let rec substTy ty i ty' = match ty with
  | GUnit | GBool | GArray _ -> ty
  | GVar j -> if i = j then ty' else ty
  | GFun (ty1, ty2) -> GFun (substTy ty1 i ty', substTy ty2 i ty')

//val substGExpr : tm:GExpr -> string -> GExpr -> Tot GExpr (decreases %[tm;0])
//val substGExpr_lst : l:list GExpr -> string -> GExpr -> Tot (list GExpr) (decreases %[l;1])
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
  | CLEAN t -> CLEAN (substGExpr t s tm')
  | ASSERT t -> ASSERT (substGExpr t s tm')
  | _ -> tm
and substGExpr_lst lst s tm' = match lst with
  | [] -> []
  | x::xs -> (substGExpr x s tm')::(substGExpr_lst xs s tm')

//val substTyInGExpr : tm:GExpr -> int -> GType -> Tot GExpr (decreases %[tm;0])
//val substTyInGExpr_lst : l:list GExpr -> int -> GType -> Tot (list GExpr) (decreases %[l;1])
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
  | CLEAN t -> CLEAN (substTyInGExpr t k ty)
  | ASSERT t -> ASSERT (substTyInGExpr t k ty)
  | _ -> tm
and substTyInGExpr_lst lst k ty = match lst with
  | [] -> []
  | x::xs -> (substTyInGExpr x k ty)::(substTyInGExpr_lst xs k ty)

// Typechecking
open Maps
type ctxt = Par.map<string, GType>

//val subtype : t1:GType -> t2:GType -> Tot bool
//val suptype : t1:GType -> t2:GType -> Tot bool
let rec subtype t1 t2 = if t1 = t2 then true else match (t1, t2) with
  | (GArray i, GArray j) -> j <= i
  | (GFun (t1, t2), GFun (s1, s2)) -> (suptype t1 s1) && (subtype t2 s2)
  | _ -> false
and suptype t1 t2 = if t1 = t2 then true else match (t1, t2) with
  | (GArray i, GArray j) -> j >= i
  | (GFun (t1, t2), GFun (s1, s2)) -> (subtype t1 s1) && (suptype t2 s2)
  | _ -> false

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

//val normalize : IExp -> IExp
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

//val toTyExp : GType -> Tot TyExp
let rec toTyExp ty = match ty with
  | GUnit -> TUnit
  | GBool -> TBool
  | GVar i -> TVar i
  | GArray n -> TArray (ILit n)
  | GFun (ty1, ty2) -> TArrow (toTyExp ty1, toTyExp ty2)

//val toGType : TyExp -> GType
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

type ctxt' = Par.map<string, TyExp>

//val inferTypes : int -> ctxt' -> tm:GExpr -> Tot (int * list Cons * list Cons * TyExp) (decreases %[tm;0])
//val inferTypes_lst : int -> ctxt' -> l:list GExpr -> Tot (int * list Cons * list Cons) (decreases %[l;1])
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
//    let e1 = TCons (ty1, TArrow (TVar top'', TVar (top''+1))) in
//    let e2 = TCons (ty2, TVar top'') in
//      (top''+2, e1::e2::(ec1@ec2), lc1@lc2, TVar (top''+1))
    let e = TCons (ty1, TArrow (TVar top'', TVar (top''+1))) in
    let c = TCons (ty2, TVar top'') in
      (top''+2, e::(ec1@ec2), c::(lc1@lc2), TVar (top''+1))
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
  | VAR x -> 
    begin match Par.find ctx x with
      | None -> (top, [], [], TUnit)
      | Some ty -> (top, [], [], ty)
    end
  | UNIT -> (top, [], [], TUnit)
  | BOOL b -> (top, [], [], TBool)
  | XOR (t1, t2) 
  | AND (t1, t2) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t1 in
    let (top'', ec2, lc2, ty2) = inferTypes top' ctx t2 in
    let e1 = TCons (ty1, TBool) in
    let e2 = TCons (ty2, TBool) in
      (top'', e1::e2::(ec1@ec2), lc1@lc2, TBool)
  | ARRAY tlst ->
    let (top', ec, lc) = inferTypes_lst top ctx tlst in
      (top', ec, lc, TArray (ILit (List.length tlst)))
  | GET_ARRAY (t, i) ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t in
    let e1 = TCons (ty1, TArray (IVar top')) in
    let l1 = ICons (ILit (i+1), IVar top') in
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
  | CLEAN t ->
    let (top', ec1, lc1, ty1) = inferTypes top ctx t in
      (top', ec1, lc1, TUnit)
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
  | (ICons (c1, c2))::xs -> (ICons (substIExp i iexp c1, substIExp i iexp c2))::(iSubst i iexp xs)
  | (TCons (c1, c2))::xs -> (TCons (substIExpInTExp i iexp c1, substIExpInTExp i iexp c2))::(iSubst i iexp xs)

let rec tSubst i texp cons = match cons with
  | [] -> []
  | (TCons (c1, c2))::xs -> (TCons (substTExp i texp c1, substTExp i texp c2))::(tSubst i texp xs)
  | x::xs -> x::(tSubst i texp xs)

let rec mergeLower iexp j bnds = match bnds with
  | [] -> Some iexp
  | (ICons (iexp', IVar h))::xs when h = j -> 
    begin match (normalize iexp, normalize iexp') with
      | (ILit x, ILit y) -> mergeLower (ILit (max x y)) j xs
      | (IVar x, IVar y) -> if x = y then mergeLower (IVar x) j xs else None
      | _ -> None
    end
  | _::xs -> mergeLower iexp j xs

let rec unify_bnds top bnds subs = 
//  printf "Unifying constraints:\n%A\n" bnds;
  match bnds with
  | [] -> Some subs
  | (ICons (i1, i2))::xs ->
    begin match (normalize i1, normalize i2) with
      | (iexp, IVar j) ->
        begin match (mergeLower iexp j xs) with
          | Some sub -> unify_bnds top (iSubst j sub xs) (iSubst j sub subs)
          | None -> unify_bnds top (xs @ [ICons (iexp, IVar j)]) subs
        end
      | (ILit x, ILit y) -> if x <= y then unify_bnds top xs subs else None
      | (iexp, iexp') -> unify_bnds top (xs @ [ICons (iexp, iexp')]) subs
    end
  | (TCons (t1, t2))::xs ->
    begin match (t1, t2) with
      | (TVar i, TUnit) | (TUnit, TVar i) -> unify_bnds top (tSubst i TUnit xs) (tSubst i TUnit subs)
      | (TVar i, TBool) | (TBool, TVar i) -> unify_bnds top (tSubst i TBool xs) (tSubst i TBool subs)
      | (TVar i, TArray iexp) -> 
          let sub = TArray (IVar top) in
            unify_bnds (top+1) (tSubst i sub ((ICons (iexp, IVar top))::xs)) ((TCons (TVar i, sub))::(tSubst i sub subs))
      | (TArray iexp, TVar i) -> 
          let sub = TArray (IVar top) in
            unify_bnds (top+1) (tSubst i sub ((ICons (IVar top, iexp))::xs)) ((TCons (TVar i, sub))::(tSubst i sub subs))
      | (TVar i, TArrow (t1, t2)) -> 
          let sub = TArrow (TVar top, TVar (top+1)) in
            unify_bnds (top+2) (tSubst i sub ((TCons (t1, TVar top))::(TCons (TVar (top+1), t2))::xs)) ((TCons (TVar i, sub))::(tSubst i sub subs))
      | (TArrow (t1, t2), TVar i) -> 
          let sub = TArrow (TVar top, TVar (top+1)) in
            unify_bnds (top+2) (tSubst i sub ((TCons (TVar top, t1))::(TCons (t2, TVar (top+1)))::xs)) ((TCons (TVar i, sub))::(tSubst i sub subs))
      | (TVar i, TVar j) -> unify_bnds top (xs @ [TCons (t1, t2)]) subs
      | (TUnit, TUnit) -> unify_bnds top xs subs
      | (TBool, TBool) -> unify_bnds top xs subs
      | (TArray iexp, TArray iexp') -> unify_bnds top ((ICons (iexp', iexp))::xs) subs
      | (TArrow (t1, t2), TArrow (s1, s2)) -> unify_bnds top ((TCons (s1, t1))::(TCons (t2, s2))::xs) subs
      | _ -> None
    end

let rec unify_eq top eqs bnds subs = match eqs with
  | [] -> unify_bnds top bnds subs
  | (ICons (i1, i2))::xs ->
    begin match (normalize i1, normalize i2) with
      | (IVar i, iexp)
      | (iexp, IVar i) -> unify_eq top (iSubst i iexp xs) (iSubst i iexp bnds) (iSubst i iexp subs)
      | (ILit i, ILit j) -> if i = j then unify_eq top xs bnds subs else None
      | (IPlus (IVar i, y), iexp) | (iexp, IPlus (IVar i, y)) ->
        let sub = IPlus (IMinus y, iexp) in
          unify_eq top (iSubst i sub eqs) (iSubst i sub bnds) (iSubst i sub subs)
      | (IPlus (IMinus (IVar i), y), iexp) | (iexp, IPlus (IMinus (IVar i), y)) ->
        let sub = IPlus (y, iexp) in
          unify_eq top (iSubst i sub eqs) (iSubst i sub bnds) (iSubst i sub subs)
      | _ -> printf "No matching case for ICons\n"; None
    end
  | (TCons (t1, t2))::xs ->
    begin match (t1, t2) with
      | (TVar i, ty)
      | (ty, TVar i) -> unify_eq top (tSubst i ty xs) (tSubst i ty bnds) ((TCons (TVar i, ty))::(tSubst i ty subs))
      | (TUnit, TUnit) -> unify_eq top xs bnds subs
      | (TBool, TBool) -> unify_eq top xs bnds subs
      | (TArray iexp, TArray iexp') -> unify_eq top ((ICons (iexp, iexp'))::xs) bnds subs
      | (TArrow (t1, t2), TArrow (s1, s2)) -> unify_eq top ((TCons (t1, s1))::(TCons (t2, s2))::xs) bnds subs
      | _ -> None
    end

let rec applySubs subs tm = match subs with
  | [] -> tm
  | (TCons (TVar i, texp))::xs -> applySubs xs (substTyInGExpr tm i (toGType texp))
  | _ -> failwith "impossible"

let annotate tm =
  let (top, eqs, bnds, typ) = inferTypes 0 [] tm in
  let res = unify_eq top eqs bnds [] in
    match res with
      | None -> Err "Could not infer types"
      | Some subs -> Val (applySubs subs tm)

