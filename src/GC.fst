(** Garbage collection *)
module GC

(* Garbage-collected reversible circuit compilation -- experimental *)
type qubit =
  { id   : int;
    ival : BoolExp;
    cval : BoolExp }

val null_q : qubit
val get_subst : Total.t int qubit -> int -> Tot int
val data_q : int -> Tot qubit
val anc_q  : int -> Tot qubit

let nullq = { id = 0; ival = BFalse; cval = BFalse }
let get_subst m = fun i -> (m i).id
let data_q i = { id = i; ival = BVar i; cval = BFalse }
let anc_q i  = { id = i; ival = BFalse; cval = BFalse }

type circGCState =
  { top    : int;
    ah     : AncHeap;
    gates  : list Gate;
    symtab : Total.t int qubit }

val circGC       : circGCState -> int -> Tot circGCState
val circGCInit   : circGCState
val circGCAlloc  : circGCState -> BoolExp -> Tot (int * circGCState)
val circGCAssign : circGCState -> int -> BoolExp -> Tot circGCState
val circGCEval   : circGCState -> state -> int -> Tot bool

// The garbage collector needs to:
//  -compile the current value in place (i.e. ival + cval + cval = ival),
//  -if the qubit is an ancilla, push it back onto the heap, and
//  -update the current value of all other bits by substituting q.id with ival + cval
val garbageCollect : circGCState -> qubit -> Tot circGCState
let garbageCollect cs q = 
  let (ah', res, ancs, circ) = compileBexp cs.ah q.id q.cval in
  let ah'' = if q.ival = BFalse then insert ah' q.id else ah' in
  let f q' = 
    let subq = fun v -> if v = q.id then BXor (q.ival, q.cval) else BVar v in
      { id = q'.id; ival = q'.ival; cval = simplify (substBexp q'.cval subq) }
  in
  let symtab' = mapVal f cs.symtab in
    { top = cs.top; ah = ah''; gates = cs.gates @ circ; symtab = symtab' }

let circGCInit = { top = 0; ah = emptyHeap; gates = []; subs = constMap nullq;
symtab = constMap nullq }
let circGCAlloc cs bexp = 
  let bexp' = simplify (substVar bexp (get_subst cs.symtab)) in
  let (ah', bit) = popMin cs.ah in
  let (ah'', res, ancs, circ') = compileBexp ah' bit bexp' in
  let q = { id = bit; ival = BFalse; cval = bexp' } in
  let top' = cs.top + 1 in
  let gates' = cs.gates @ circ' in
  let symtab' = update cs.symtab cs.top q in
  (cs.top, {top = top'; ah = ah''; gates = gates'; symtab = symtab'})
let circGCAssign cs l bexp =
  let q = lookup cs.symtab l in
  let bexp' = simplify (substVar bexp (get_subst cs.symtab)) in
  let bexpfac = factorAs bexp' q.id in
  match (q.cval, bexpfac) with
    | (BFalse, _)      -> // substitute q.id with BFalse, compile in place
      let bexp'' = substBexp bexp' (fun v -> if v = q.id then BFalse else BVar v) in
      let (ah', res, ancs, circ) = compileBexp cs.ah q.id bexp'' in
      let q' = { id = q.id; ival = q.ival; cval = bexp'' } in
        {top = cs.top; ah = ah'; gates = cs.gates @ circ; symtab = update cs.symtab l q' }
    | (_, Some bexp'') -> // compile in place, substitute q.id with q.id \oplus bexp''
      let (ah', res, ancs, circ') = compileBexp cs.ah q.id bexp'' in
      let q' = { id = q.id; ival = q.ival; cval = simplify (BXor (q.cval, bexp'')) } in
      let f b = 
        let subq = fun v -> if v = q.id then BXor (BVar q.id, bexp'') else BVar v in
          { id = b.id; ival = b.ival; cval = simplify (substBexp b.cval subq) }
      in
      let symtab' = update (mapVal f cs.symtab) l q' in
        {top = cs.top; ah = ah'; gates = cs.gates @ circ'; symtab = update cs.symtab l q' }
    | _                -> // Compile out of place, clean q.id
      let (ah', res, ancs, circ') = compileBexp_oop cs.ah bexp' in
      let q' = { id = res; ival = BFalse; cval = bexp' } in
      let cs' = { top = cs.top; ah = ah'; gates = cs.gates @ circ'; symtab = update cs.symtab l q' } in
        garbageCollect cs' q
let circGCEval cs st i = false

let circGCInterp = {
  alloc = circGCAlloc;
  assign = circGCAssign;
  eval = circGCEval
}

val allocNcircGC : list GExpr * circGCState -> i:int ->
  Tot (list GExpr * circGCState) (decreases i)
let rec allocNcircGC (locs, cs) i =
  if i <= 0 then (List.rev locs, cs)
  else
    let (ah', res) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                symtab = update cs.symtab cs.top (data_q res) }
    in
      allocNcircGC (((LOC cs.top)::locs), cs') (i-1)

val allocTycircGC : GType -> circGCState -> Tot (result (GExpr * circGCState))
let allocTycircGC ty cs = match ty with
  | GBool ->
    let (ah', res) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                symtab = update cs.symtab cs.top (data_q res) }
    in
      Val (LOC cs.top, cs')
  | GArray n ->
    let (locs, st') = allocNcircGC ([], cs) n in
      Val (ARRAY locs, st')
  | _ -> Err "Invalid parameter type for circuit generation"

val lookup_Lst_gc : Total.t int qubit -> lst:(list GExpr){isVal_lst lst} -> Tot (list int)
let rec lookup_Lst_gc symtab lst = match lst with
  | [] -> []
  | (LOC l)::xs -> ((lookup symtab l).id)::(lookup_Lst_gc symtab xs)

val compileGCCirc : config circGCState -> Dv (result (list int * list Gate))
let rec compileGCCirc (gexp, cs) =
  if isVal gexp then match gexp with
    | UNIT -> Val ([], [])
    | LAMBDA (x, ty, t) ->
      begin match allocTycircGC ty cs with
        | Err s -> Err s
        | Val (v, cs') -> compileGCCirc (substGExpr t x v, cs')
      end
    | LOC l ->
      let res = lookup cs.symtab l in
        Val ([res.id], cs.gates)
    | ARRAY lst ->
      let res = lookup_Lst_gc cs.symtab lst in
        Val (res, cs.gates)
  else match (step (gexp, cs) circGCInterp) with
    | Err s -> Err s
    | Val c' -> compileGCCirc c'

