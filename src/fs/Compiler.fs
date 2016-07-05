(** Main compiler transformation *)
module Compiler

open Util
open Set
open Total
open AncillaHeap
open BoolExp
open Circuit
open ExprTypes
open Interpreter

(* Reversible circuit interpretation -- compiles a Revs program
   to a reversible circuit in a "natural" way. Specifically, 
   the circuit reflects the structure of the program *)
type circState =
  { top : int;
    ah : AncHeap;
    gates : list<Gate>;
    subs : Total.t<int, int>;
    zero : Total.t<int, bool> }

let circInit = {top = 0; ah = emptyHeap; gates = []; subs = constMap 0}
let circAlloc cs =
  let (ah', bit) = popMin cs.ah in
  let cs' = 
    { top = cs.top + 1; 
      ah = ah'; 
      gates = cs.gates; 
      subs = update cs.subs cs.top bit;
      zero = update cs.zero bit true }
  in
    (cs.top, cs')
let circAssign cs l bexp =
  let l' = lookup cs.subs l in
  let bexp' = substVar bexp cs.subs in
  match factorAs bexp' l' with
    | Some bexp'' -> 
        let (ah', res, ancs, circ') = compileBexpPebbled cs.ah l' (simplify bexp'') in
          { top   = cs.top;
            ah    = ah';
            gates = cs.gates@circ';
            subs  = update cs.subs l res;
            zero  = update cs.zero l' false }
    | None -> 
        if (lookup cs.zero l' = true) then
          let (ah', res, ancs, circ') = compileBexpPebbled cs.ah l' (simplify bexp') in
            { top   = cs.top;
              ah    = ah';
              gates = cs.gates@circ';
              subs  = update cs.subs l res;
              zero  = update cs.zero l' false }
        else
          let (ah', res, ancs, circ') = compileBexpPebbled_oop cs.ah (simplify bexp') in
            { top   = cs.top;
              ah    = ah';
              gates = cs.gates@circ';
              subs  = update cs.subs l res;
              zero  = update cs.zero res false }
let circClean cs _ l =
  let bit = lookup cs.subs l in
    { top   = cs.top;
      ah    = insert cs.ah bit;
      gates = cs.gates;
      subs  = cs.subs;
      zero  = update cs.zero bit true }
let circEval cs ivals i = lookup (evalCirc cs.gates ivals) (lookup cs.subs i)

let circInterp = {
  alloc = circAlloc;
  assign = circAssign;
  clean = circClean;
  assertion = fun st t l -> st;
  eval = circEval
}

val allocNcirc : list GExpr * circState -> i:int ->
  Tot (list GExpr * circState) (decreases i)
let rec allocNcirc (locs, cs) i =
  if i <= 0 then (List.rev locs, cs)
  else
    let (ah', res) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                subs = update cs.subs cs.top res;
                zero = update cs.zero res false }
    in
      allocNcirc (((LOC cs.top)::locs), cs') (i-1)

val allocTycirc : GType -> circState -> Tot (result (GExpr * circState))
let allocTycirc ty cs = match ty with
  | GBool ->
    let (ah', res) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                subs = update cs.subs cs.top res;
                zero = update cs.zero res false }
    in
      Val (LOC cs.top, cs')
  | GArray n ->
    let (locs, st') = allocNcirc ([], cs) n in
      Val (ARRAY locs, st')
  | _ -> Err "Invalid parameter type for circuit generation"

val lookup_Lst : st:Total.t int int -> lst:(list GExpr){isVal_lst lst} -> Tot (list int)
let rec lookup_Lst st lst = match lst with
  | [] -> []
  | (LOC l)::xs -> (lookup st l)::(lookup_Lst st xs)

val compileCirc : config circState -> Dv (result (list int * list Gate))
let rec compileCirc (gexp, cs) =
  if isVal gexp then match gexp with
    | UNIT -> Val ([], [])
    | LAMBDA (x, ty, t) ->
      begin match allocTycirc ty cs with
        | Err s -> Err s
        | Val (v, cs') -> compileCirc (substGExpr t x v, cs')
      end
    | LOC l ->
      let res = lookup cs.subs l in
        Val ([res], cs.gates)
    | ARRAY lst ->
      let res = lookup_Lst cs.subs lst in
        Val (res, cs.gates)
  else match (step (gexp, cs) circInterp) with
    | Err s -> Err s
    | Val c' -> compileCirc c'
