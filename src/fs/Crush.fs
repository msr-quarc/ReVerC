(** Program transformation/compiler based on minimal ESOP forms *)
module Crush

open Util
open Total
open BoolExp
open ExprTypes
open Interpreter

(* Boolean expression interpretation -- for generating the fully
   inlined classical circuit of the Revs program *)
type BExpState = int * (Total.t int BoolExp)

let bexpInit : BExpState = (0, constMap BFalse)
let bexpAlloc (top, st) = (top, (top + 1, st))
let bexpAssign (top, st) l bexp = (top, update st l (substBexp bexp st))
let bexpEval (top, st) ivals i = evalBexp (lookup st i) ivals

let bexpInterp = {
  alloc = bexpAlloc;
  assign = bexpAssign;
  clean = fun st t l -> st;
  assertion = fun st t l -> st;
  eval = bexpEval
}

type CleanupStrategy =
  | Pebbled
  | Boundaries
  | Bennett

let simps bexp = simplify (toXDNF bexp)

val allocN : list GExpr * BExpState -> i:int ->
  Tot (list GExpr * BExpState) (decreases i)
let rec allocN (locs, (top, st)) i =
  if i <= 0 then (List.rev locs, (top, st))
  else allocN (((LOC top)::locs), (top+1, update st top (BVar top))) (i-1)

val allocTy : GType -> BExpState -> Tot (result (GExpr * BExpState))
let allocTy ty (top, st) = match ty with
  | GBool -> Val (LOC top, (top + 1, update st top (BVar top)))
  | GArray n ->
    let (locs, st') = allocN ([], (top, st)) n in
      Val (ARRAY locs, st')
  | _ -> Err "Invalid parameter type for circuit generation"

val lookupLst : lst:(list GExpr){isVal_lst lst} -> st:BExpState -> Tot (list BoolExp)
let rec lookupLst lst st = match lst with
  | [] -> []
  | (LOC l)::xs -> (lookup (snd st) l)::(lookupLst xs st)

open AncillaHeap
open Circuit

val foldPebble : (AncHeap * list int * list int * list Gate) ->
  BoolExp -> Tot (AncHeap * list int * list int * list Gate)
let foldPebble (ah, outs, anc, circ) bexp =
  let (ah', res, anc', circ') = compileBexpPebbled_oop ah (simps bexp) in
    (ah', res::outs, anc'@anc, circ@circ')

val foldClean : (AncHeap * list int * list int * list Gate) ->
  BoolExp -> Tot (AncHeap * list int * list int * list Gate)
let foldClean (ah, outs, anc, circ) bexp =
  let (ah', res, anc', circ') = compileBexpClean_oop ah (simps bexp) in
    (ah', res::outs, anc'@anc, circ@circ')

val foldBennett : (AncHeap * list int * list int * list Gate * list Gate) ->
  BoolExp -> Tot (AncHeap * list int * list int * list Gate * list Gate)
let foldBennett (ah, outs, anc, circ, ucirc) bexp =
  let (ah', res, anc', circ') = compileBexp_oop ah (simps bexp) in
    (ah', res::outs, anc'@anc, circ@circ', (List.rev (uncompute circ' res))@ucirc)

(* Compilation wrapper. The main point of interest is its action when the
   program is a function. In that case it allocates some new free variables
   corresponding to the inputs of the function, then evaluates the function
   body. Note also that this wrapper is not verified currently. Eventually this
   should be done. *)
val compile : config BExpState -> CleanupStrategy -> Dv (result (list int * list Gate))
let rec compile (gexp, st) strategy =
  if isVal gexp then match gexp with
    | UNIT -> Val ([], [])
    | LAMBDA (x, ty, t) ->
      begin match allocTy ty st with
        | Err s -> Err s
        | Val (v, st') -> compile (substGExpr t x v, st') strategy
      end
    | LOC l ->
      let bexp = lookup (snd st) l in
      let max = varMax bexp in
      let (ah, res, anc, circ) = match strategy with
        | Pebbled -> compileBexpPebbled_oop (above (max+1)) (simps bexp)
        | Boundaries -> compileBexpClean_oop (above (max+1)) (simps bexp)
        | Bennett -> compileBexpClean_oop (above (max+1)) (simps bexp)
      in
        Val ([res], circ)
    | ARRAY lst ->
      let cmp x y = 
	let xd = andDepth x in
	let yd = andDepth y in
	  if xd < yd then 1 else if xd = yd then 0 else -1
      in
      let blst = List.sortWithT cmp (lookupLst lst st) in
      let max = listMax (List.mapT varMax blst) in
      let (ah, outs, anc, circ) = match strategy with
        | Pebbled ->
          let (ah, outs, anc, circ) =
            List.fold_leftT foldPebble (above (max+1), [], [], []) blst
          in
            (ah, List.rev outs, List.rev anc, circ)
        | Boundaries ->
          let (ah, outs, anc, circ) =
            List.fold_leftT foldClean (above (max+1), [], [], []) blst
          in
            (ah, List.rev outs, List.rev anc, circ)
        | Bennett ->
          let (ah, outs, anc, circ, ucirc) =
            List.fold_leftT foldBennett (above (max+1), [], [], [], []) blst
          in
            (ah, List.rev outs, List.rev anc, circ@ucirc)
      in
        Val (outs, circ)
  else match (step (gexp, st) bexpInterp) with
    | Err s -> Err s
    | Val c' -> compile c' strategy
