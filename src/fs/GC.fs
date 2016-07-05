(** Garbage collection *)
module GC

open Util
open Total
open AncillaHeap
open BoolExp
open Circuit
open ExprTypes
open Interpreter

(* Garbage-collected reversible circuit compilation -- experimental *)

type circGCState =
  { top    : int;
    ah     : AncHeap;
    gates  : list<Gate>;
    symtab : Total.t<int, int>;
    isanc  : Total.t<int, bool>;
    cvals  : Total.t<int, BoolExp> }

  (* The garbage collector needs to:
    -compile the current value in place (i.e. ival + cval + cval = ival),
     -if the qubit is an ancilla, push it back onto the heap, and
     -update the current value of all other bits by substituting q.id with ival + cval *)
let garbageCollect cs bit = 
  let cval = lookup cs.cvals bit in
  if Set.mem bit (vars cval) then cs else
  let (ah', res, ancs, circ) = compileBexp cs.ah bit cval in
  match lookup cs.isanc bit with
    | true ->
      let f bexp = substOneVar bexp bit cval in
      let cvals' = mapVals f cs.cvals in
        { top    = cs.top; 
          ah     = insert ah' bit; 
          gates  = cs.gates @ circ; 
          symtab = cs.symtab;
          isanc  = cs.isanc;
          cvals  = cvals' }
    | false ->
      let f bexp = substOneVar bexp bit (BXor (BVar bit, cval)) in
      let cvals' = mapVals f cs.cvals in
        { top    = cs.top; 
          ah     = ah'; 
          gates  = cs.gates @ circ; 
          symtab = cs.symtab;
          isanc  = cs.isanc;
          cvals  = cvals' }

let circGCInit = 
  { top    = 0; 
    ah     = emptyHeap; 
    gates  = []; 
    symtab = constMap 0;
    isanc  = constMap true;
    cvals  = constMap BFalse }

let circGCAlloc cs = 
  let (ah', bit) = popMin cs.ah in
  let cs' =
    { top    = cs.top + 1;
      ah     = ah';
      gates  = cs.gates;
      symtab = update cs.symtab cs.top bit;
      isanc  = update cs.isanc bit true;
      cvals  = update cs.cvals bit BFalse }
  in
  (cs.top, cs')

let circGCAssign cs l bexp =
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  match (lookup cs.cvals bit, factorAs bexp' bit, lookup cs.isanc bit) with
    | (BFalse, _, true) -> // substitute bit with BFalse, compile in place
      let bexp'' = simplify (substOneVar bexp' bit BFalse) in
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit BFalse in
      let cvals' = update (mapVals f cs.cvals) bit bexp'' in
      { top    = cs.top; 
        ah     = ah'; 
        gates  = cs.gates @ circ; 
        symtab = cs.symtab;
        isanc  = cs.isanc;
        cvals  = cvals'}
    | (cval, Some bexp0, _) -> // compile in place, substitute q.id with q.id \oplus bexp''
      let bexp'' = simplify bexp0 in
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit (BXor (BVar bit, bexp'')) in
      let cvals' = mapVals f cs.cvals in
      { top    = cs.top; 
        ah     = ah'; 
        gates  = cs.gates @ circ'; 
        symtab = cs.symtab;
        isanc  = cs.isanc;
        cvals  = update cvals' bit (BXor (bexp'', lookup cvals' bit)) }
    | _                -> // Compile out of place, clean q.id
      let bexp'' = simplify bexp' in
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ') = compileBexp ah' bit' bexp'' in
      let cs' = 
        { top    = cs.top; 
          ah     = ah''; 
          gates  = cs.gates @ circ'; 
          symtab = update cs.symtab l bit';
          isanc  = update cs.isanc bit' true;
          cvals  = update cs.cvals bit' bexp'' } 
      in
      garbageCollect cs' bit

let circGCClean cs _ l =
  let bit = lookup cs.symtab l in
  { top    = cs.top; 
    ah     = insert cs.ah bit; 
    gates  = cs.gates; 
    symtab = cs.symtab;
    isanc  = update cs.isanc bit true;
    cvals  = update cs.cvals bit BFalse } 

let circGCEval cs st i = lookup (evalCirc cs.gates st) (lookup cs.symtab i)

let circGCInterp = {
  alloc = circGCAlloc;
  assign = circGCAssign;
  clean = circGCClean;
  assertion = fun st t l -> st;
  eval = circGCEval }

let rec allocNcircGC (locs, cs) i =
  if i <= 0 then (List.rev locs, cs) else
  let (ah', bit) = popMin cs.ah in
  let cs' = { top = cs.top + 1;
              ah = ah';
              gates = cs.gates;
              symtab = update cs.symtab cs.top bit;
              isanc = update cs.isanc bit false;
              cvals = update cs.cvals bit BFalse }
  in
  allocNcircGC (((LOC cs.top)::locs), cs') (i-1)

let allocTycircGC ty cs = match ty with
  | GBool ->
    let (ah', bit) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                symtab = update cs.symtab cs.top bit;
                isanc = update cs.isanc bit false;
                cvals = update cs.cvals bit BFalse }
    in
    Val (LOC cs.top, cs')
  | GArray n ->
    let (locs, st') = allocNcircGC ([], cs) n in
    Val (ARRAY locs, st')
  | _ -> Err "Invalid parameter type for circuit generation"

let rec lookup_Lst_gc symtab lst = match lst with
  | [] -> []
  | (LOC l)::xs -> ((lookup symtab l))::(lookup_Lst_gc symtab xs)

  (* Scrubs the state with respect to the remainder of the program *)
let findGarbage gexp cs = Set.diff (keys cs.symtab) (locs gexp)
let garbageCollector gexp cs = 
  let garbage = findGarbage gexp cs in
  let f cs l = 
    let q = lookup cs.symtab l in
    let cs' = garbageCollect cs q in
    { top    = cs'.top; 
      ah     = cs'.ah; 
      gates  = cs'.gates; 
      symtab = delete cs'.symtab l;
      isanc  = cs'.isanc;
      cvals  = cs'.cvals }
  in
  Set.fold f cs garbage

let rec compileGCCirc (gexp, cs) =
  let cs = garbageCollector gexp cs in
  if isVal gexp then match gexp with
    | UNIT -> Val ([], [])
    | LAMBDA (x, ty, t) ->
      begin match allocTycircGC ty cs with
        | Err s -> Err s
        | Val (v, cs') -> compileGCCirc (substGExpr t x v, cs')
      end
    | LOC l ->
      let bit = lookup cs.symtab l in
      Val ([bit], cs.gates)
    | ARRAY lst ->
      let bits = lookup_Lst_gc cs.symtab lst in
      Val (bits, cs.gates)
  else match (step (gexp, cs) circGCInterp) with
    | Err s -> Err s
    | Val c' -> compileGCCirc c'
