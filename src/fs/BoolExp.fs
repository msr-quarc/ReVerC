module BoolExp

open Util
open Maps.Total
open AncillaHeap
open Circuit

type BoolExp =
  | BFalse
  | BVar of int
  | BNot of BoolExp
  | BAnd of BoolExp * BoolExp
  | BXor of BoolExp * BoolExp

// Printing
//val prettyPrintBexp : BoolExp -> string
let rec prettyPrintBexp bexp = match bexp with
  | BFalse -> "false"
  | BVar i -> IO.string_of_int i
  | BNot x -> "~" ^ (prettyPrintBexp x)
  | BAnd (x, y) -> "(" ^ (prettyPrintBexp x) ^ " && " ^ (prettyPrintBexp y) ^ ")"
  | BXor (x, y) -> "(" ^ (prettyPrintBexp x) ^ " <> " ^ (prettyPrintBexp y) ^ ")"

// Membership
//val occursInBexp : int -> exp:BoolExp -> Tot bool (decreases exp)
let rec occursInBexp i exp = match exp with
  | BFalse      -> false
  | BVar n      -> n = i
  | BAnd (x, y) -> occursInBexp i x || occursInBexp i y
  | BXor (x, y) -> occursInBexp i x || occursInBexp i y
  | BNot x      -> occursInBexp i x

//val vars : BoolExp -> Tot (set int)
let vars exp = fun i -> occursInBexp i exp

// Use getVars for computational stuff
//val getVars_acc : list int -> exp:BoolExp -> Tot (list int) (decreases exp)
let rec getVars_acc acc exp = match exp with
  | BFalse   -> []
  | BVar n   -> if listmem n acc then acc else n::acc
  | BAnd (x, y) -> getVars_acc (getVars_acc acc x) y
  | BXor (x, y) -> getVars_acc (getVars_acc acc x) y
  | BNot exp -> getVars_acc acc exp

//val getVars : BoolExp -> Tot (list int)
let getVars exp = getVars_acc [] exp

// Maximums, counting -- Replace this with a version defined directly on BoolExp
//val listMax : (list int) -> Tot int
let rec listMax lst = match lst with
  | [] -> 0
  | x::xs -> max x (listMax xs)

//val varCount : BoolExp -> Tot int
let varCount exp = List.length (getVars exp)

//val varMax : BoolExp -> Tot int
let varMax exp = listMax (getVars exp)

//val gtVars : int -> BoolExp -> Tot bool
let rec gtVars i bexp = match bexp with
  | BFalse -> false
  | BVar j -> i > j
  | BNot x -> gtVars i x
  | BXor (x, y) | BAnd (x, y) -> gtVars i x && gtVars i y

// Substitutions
//val substBexp : BoolExp -> Total.map int BoolExp -> Tot BoolExp
let rec substBexp bexp sub = match bexp with
  | BFalse   -> BFalse
  | BVar i   -> sub i
  | BNot x   -> BNot (substBexp x sub)
  | BAnd (x, y) -> BAnd ((substBexp x sub), (substBexp y sub))
  | BXor (x, y) -> BXor ((substBexp x sub), (substBexp y sub))

//val substVar : BoolExp -> Total.map int int -> Tot BoolExp
let rec substVar bexp sub = match bexp with
  | BFalse   -> BFalse
  | BVar i   -> BVar (sub i)
  | BNot x   -> BNot (substVar x sub)
  | BAnd (x, y) -> BAnd ((substVar x sub), (substVar y sub))
  | BXor (x, y) -> BXor ((substVar x sub), (substVar y sub))

// Evaluation
//val evalBexp : bexp:BoolExp -> state -> Tot bool
let rec evalBexp bexp st = match bexp with
  | BFalse   -> false
  | BVar i   -> st i
  | BNot x   -> not (evalBexp x st)
  | BAnd (x, y) -> (evalBexp x st) && (evalBexp y st)
  | BXor (x, y) -> (evalBexp x st) <> (evalBexp y st)

// Optimizations
//val simplify : exp:BoolExp -> Tot BoolExp
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

//val factorAs : exp:BoolExp -> targ:int -> Tot (option BoolExp)
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

//val distributeAnds : exp:BoolExp -> Tot BoolExp
let rec distributeAnds exp = match exp with
  | BFalse -> BFalse
  | BVar v -> BVar v
  | BNot x -> BNot (distributeAnds x)
  | BAnd (x, y) ->
    begin match (distributeAnds x, distributeAnds y) with
      | (BXor (a, b), BXor (c, d)) ->
        BXor (BXor (BAnd (a, c), BAnd (b, c)), BXor (BAnd (a, d), BAnd (b, d)))
      | (x', BXor (c, d)) -> BXor (BAnd (x', c), BAnd (x', d))
      | (BXor (a, b), y') -> BXor (BAnd (a, y'), BAnd (b, y'))
      | (x', y') -> BAnd (x', y')
    end
  | BXor (x, y) -> BXor (distributeAnds x, distributeAnds y)

//val undistributeAnds : exp:BoolExp -> Tot BoolExp
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

// Compilation stuff
type compilerResult = AncHeap * int * (list<int>) * (list<Gate>)

//val compileBexp : AncHeap -> int -> exp:BoolExp -> Tot compilerResult (decreases %[exp;0])
//val compileBexp_oop : AncHeap -> exp:BoolExp -> Tot compilerResult (decreases %[exp;1])
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

//val compileBexpClean : AncHeap -> int -> BoolExp -> Tot compilerResult
//val compileBexpClean_oop : AncHeap -> BoolExp -> Tot compilerResult
let compileBexpClean ah targ exp =
  let (ah', res, anc, circ) = compileBexp ah targ exp in
  let cleanup = uncompute circ res in
  let ah'' = List.fold insert ah' anc in
    (ah'', res, [], circ@(List.rev cleanup))
let compileBexpClean_oop ah exp = match exp with
  | BVar v -> (ah, v, [], [])
  | _ ->
    let (ah', targ) = popMin ah in
    let (ah'', res, anc, gate) = compileBexpClean ah' targ exp in
      (ah'', res, targ::anc, gate)

//val compileBexpPebbled : AncHeap -> int -> exp:BoolExp -> Tot compilerResult (decreases %[exp;0])
//val compileBexpPebbled_oop : AncHeap -> exp:BoolExp -> Tot compilerResult (decreases %[exp;1])
let rec compileBexpPebbled ah targ exp = match exp with
  | BFalse   -> (ah, targ, [], [])
  | BVar v   -> (ah, targ, [], [RCNOT (v, targ)])
  | BAnd (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexpPebbled_oop ah x in
    let (ah'', yres, yanc, ygate) = compileBexpPebbled_oop ah' y in
    let cleanup = uncompute (xgate @ ygate) targ in
    let ah''' = List.fold insert  ah'' (xanc@yanc) in
      (ah''', targ, [], (xgate @ ygate) @ [RTOFF (xres, yres, targ)] @ (List.rev cleanup))
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

