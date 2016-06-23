(** Utilities and compilation for Boolean expressions *)
module BoolExp

(* Boolean expressions over false, not, and, xor, and free variables.
   This module also defines compilation to circuits in three ways:
   No cleanup of ancillas, cleanup of ancillas after compilation,
   and intermittent cleanup during compilation. All three are proven
   correct with respect to the output and the cleanliness of ancillas.
   Boolean simplifications are also defined here and proven correct *)

open Total
open Util
open AncillaHeap
open Circuit

type BoolExp =
  | BFalse
  | BVar of int
  | BNot of BoolExp
  | BAnd of BoolExp * BoolExp
  | BXor of BoolExp * BoolExp

type compilerResult = AncHeap * int * (list<int>) * (Circuit)

(* Printing *)
let rec prettyPrintBexp bexp = match bexp with
  | BFalse -> "false"
  | BVar i -> Prims.string_of_int i
  | BNot x -> FStar.String.strcat "~" (prettyPrintBexp x)
  | BAnd (x, y) -> FStar.String.strcat "(" (FStar.String.strcat (prettyPrintBexp x) (FStar.String.strcat " && " (FStar.String.strcat (prettyPrintBexp y) ")")))
  | BXor (x, y) -> FStar.String.strcat "(" (FStar.String.strcat (prettyPrintBexp x) (FStar.String.strcat " <> " (FStar.String.strcat (prettyPrintBexp y) ")")))

(* Membership *)
let rec occursInBexp i exp = match exp with
  | BFalse      -> false
  | BVar n      -> n = i
  | BAnd (x, y) -> occursInBexp i x || occursInBexp i y
  | BXor (x, y) -> occursInBexp i x || occursInBexp i y
  | BNot x      -> occursInBexp i x

(* Use getVars for computational stuff *)
let rec getVars_acc acc exp = match exp with
  | BFalse   -> acc
  | BVar n   -> Set.add n acc
  | BAnd (x, y) -> getVars_acc (getVars_acc acc x) y
  | BXor (x, y) -> getVars_acc (getVars_acc acc x) y
  | BNot exp -> getVars_acc acc exp

let getVars exp = getVars_acc Set.empty exp
let vars = getVars

(* Maximums, counting -- Replace this with a version defined directly on BoolExp *)
let max x y = if x > y then x else y

let rec listMax lst = match lst with
  | [] -> 0
  | x::xs -> max x (listMax xs)

let varCount exp = Set.count (getVars exp)

let varMax exp = listMax (Set.toList (getVars exp))

let rec gtVars i bexp = match bexp with
  | BFalse -> false
  | BVar j -> i > j
  | BNot x -> gtVars i x
  | BXor (x, y) | BAnd (x, y) -> gtVars i x && gtVars i y

let rec andDepth bexp = match bexp with
  | BNot x   -> andDepth x
  | BAnd (x, y) -> (andDepth x) + (andDepth y) + 1
  | BXor (x, y) -> max (andDepth x) (andDepth y)
  | _ -> 0

(* Substitutions *)
let rec substBexp bexp sub = match bexp with
  | BFalse   -> BFalse
  | BVar i   -> lookup sub i
  | BNot x   -> BNot (substBexp x sub)
  | BAnd (x, y) -> BAnd ((substBexp x sub), (substBexp y sub))
  | BXor (x, y) -> BXor ((substBexp x sub), (substBexp y sub))

let rec substVar bexp sub = match bexp with
  | BFalse   -> BFalse
  | BVar i   -> BVar (lookup sub i)
  | BNot x   -> BNot (substVar x sub)
  | BAnd (x, y) -> BAnd ((substVar x sub), (substVar y sub))
  | BXor (x, y) -> BXor ((substVar x sub), (substVar y sub))

(* Evaluation *)
let rec evalBexp bexp st = match bexp with
  | BFalse   -> false
  | BVar i   -> lookup st i
  | BNot x   -> not (evalBexp x st)
  | BAnd (x, y) -> (evalBexp x st) && (evalBexp y st)
  | BXor (x, y) -> (evalBexp x st) <> (evalBexp y st)

(* Optimizations *)
let rec simplify exp = match exp with
  | BFalse -> BFalse
  | BVar x -> exp
  | BAnd (x, y) ->
    let x' = simplify x in
    let y' = simplify y in (
      match (x', y') with
        | (BFalse, _) | (_, BFalse) -> BFalse
        | (BVar x, BAnd (BVar y, z))
        | (BVar x, BAnd (z, BVar y))
        | (BAnd (BVar y, z), BVar x)
        | (BAnd (z, BVar y), BVar x) -> 
            if x = y then BAnd (BVar x, z) else BAnd (x', y')
        | _ -> BAnd (x', y')
    )
  | BXor (x, y) ->
    let x' = simplify x in
    let y' = simplify y in (
      match (x', y') with
        | (BFalse, z) | (z, BFalse) -> z
        | (BVar x, BXor (BVar y, z))
        | (BVar x, BXor (z, BVar y))
        | (BXor (BVar y, z), BVar x)
        | (BXor (z, BVar y), BVar x) -> 
            if x = y then z else BXor (x', y')
        | _ -> BXor (x', y')
    )
  | BNot x ->
    let x' = simplify x in begin match x' with
      | BNot y -> y
      | _ -> BNot x'
    end

let rec factorAs exp targ = match exp with
  | BFalse -> None
  | BVar i -> if i = targ then Some BFalse else None
  | BNot x -> (
    match factorAs x targ with
      | None -> None
      | Some x' -> Some (BNot x')
    )
  | BAnd (x, y) -> None
  | BXor (x, y) ->
    if not (occursInBexp targ y) then (
      match factorAs x targ with
        | None -> None
        | Some x' -> Some (BXor (x', y))
    ) else if not (occursInBexp targ x) then (
      match factorAs y targ with
        | None -> None
        | Some y' -> Some (BXor (x, y'))
    ) else None

(* ESOP forms *)
type esop = list<list<int> >

let esfalse = []
let estrue  = [[]]
let esvar v = [[v]]
let esnot x = listSymdiff estrue x
let esxor x y = listSymdiff x y
let esmul s y = List.map (listUnion s) y
let esand x y = FStar.List.fold_left (fun x s -> listSymdiff x (esmul s y)) [] x

let rec toESOP exp = match exp with
  | BFalse -> esfalse
  | BVar v -> esvar v
  | BNot x -> esnot (toESOP x)
  | BXor (x, y) -> esxor (toESOP x) (toESOP y)
  | BAnd (x, y) -> esand (toESOP x) (toESOP y)

let rec fromESOP es = match es with
  | [] -> BFalse
  | []::xs -> BXor (BNot BFalse, fromESOP xs)
  | (y::ys)::xs -> BXor (FStar.List.fold_left (fun exp v -> BAnd (exp, (BVar v))) (BVar y) ys, fromESOP xs)

let rec distrib x y = match (x, y) with
  | (BXor (x1, x2), _) -> BXor (distrib x1 y, distrib x2 y)
  | (_, BXor (y1, y2)) -> BXor (distrib x y1, distrib x y2)
  | _                  -> BAnd (x, y)

let rec distributeAnds exp = match exp with
  | BNot x      -> BXor (BNot BFalse, distributeAnds x)
  | BAnd (x, y) -> distrib (distributeAnds x) (distributeAnds y)
  | BXor (x, y) -> BXor (distributeAnds x, distributeAnds y)
  | _ -> exp

let rec undistributeAnds exp = match exp with
  | BFalse -> BFalse
  | BVar v -> BVar v
  | BNot x -> BNot (undistributeAnds x)
  | BAnd (x, y) -> BAnd (undistributeAnds x, undistributeAnds y)
  | BXor (x, y) ->
    begin match (undistributeAnds x, undistributeAnds y) with
      | (BAnd (a, b), BAnd (c, d)) ->
        if a = c then BAnd (a, BXor (b, d))
        else if a = d then BAnd (a, BXor (b, c))
        else if b = c then BAnd (b, BXor (a, d))
        else if b = d then BAnd (b, BXor (a, c))
        else BXor (BAnd (a, b), BAnd (c, d))
      | (x', y') -> BXor (x', y')
    end

(* Compilation *)
let rec compileBexp ah targ exp = match exp with
  | BFalse   -> (ah, targ, [], [])
  | BVar v   -> (ah, targ, [], [RCNOT (v, targ)])
  | BAnd (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexp_oop ah x in
    let (ah'', yres, yanc, ygate) = compileBexp_oop ah' y in
      (ah'', targ, xanc @ yanc, (xgate @ ygate) @ [RTOFF (xres, yres, targ)])
  | BXor (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexp ah targ x in
    let (ah'', yres, yanc, ygate) = compileBexp ah' targ y in
      (ah'', targ, xanc @ yanc, xgate @ ygate)
  | BNot exp  ->
    let (ah', xres, xanc, xgate) = compileBexp ah targ exp in
      (ah', targ, xanc, xgate @ [RNOT xres])
and compileBexp_oop ah exp = match exp with
  | BVar v -> (ah, v, [], [])
  | _ ->
    let (ah', targ) = popMin ah in
    let (ah'', res, anc, gate) = compileBexp ah' targ exp in
      (ah'', res, targ::anc, gate)

let compileBexpClean ah targ exp =
  let (ah', res, anc, circ) = compileBexp ah targ exp in
  let cleanup = uncompute circ res in
  let ah'' = FStar.List.fold_left insert ah' anc in
    (ah'', res, [], circ@(FStar.List.rev cleanup))
let compileBexpClean_oop ah exp = match exp with
  | BVar v -> (ah, v, [], [])
  | _ ->
    let (ah', targ) = popMin ah in
    let (ah'', res, anc, gate) = compileBexpClean ah' targ exp in
      (ah'', res, targ::anc, gate)

let rec compileBexpPebbled ah targ exp = match exp with
  | BFalse   -> (ah, targ, [], [])
  | BVar v   -> (ah, targ, [], [RCNOT (v, targ)])
  | BAnd (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexpPebbled_oop ah x in
    let (ah'', yres, yanc, ygate) = compileBexpPebbled_oop ah' y in
    let cleanup = uncompute (xgate @ ygate) targ in
    let ah''' = FStar.List.fold_left insert  ah'' (xanc@yanc) in
      (ah''', targ, [], (xgate @ ygate) @ [RTOFF (xres, yres, targ)] @ (FStar.List.rev cleanup))
  | BXor (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexpPebbled ah targ x in
    let (ah'', yres, yanc, ygate) = compileBexpPebbled ah' targ y in
      (ah'', targ, xanc @ yanc, xgate @ ygate)
  | BNot exp  ->
    let (ah', xres, xanc, xgate) = compileBexpPebbled ah targ exp in
      (ah', targ, xanc, xgate @ [RNOT xres])
and compileBexpPebbled_oop ah exp = match exp with
  | BVar v -> (ah, v, [], [])
  | _ ->
    let (ah', targ) = popMin ah in
    let (ah'', res, anc, gate) = compileBexpPebbled ah' targ exp in
      (ah'', res, targ::anc, gate)

