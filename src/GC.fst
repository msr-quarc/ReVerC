(** Garbage collection *)
module GC

open Util
open Set
open Total
open AncillaHeap
open BoolExp
open Circuit
open ExprTypes
open Interpreter

(* Garbage-collected reversible circuit compilation -- experimental *)
type qubit =
  { id   : int;
    ival : BoolExp;
    cval : BoolExp }

val null_q  : qubit
val getSubs : Total.t int qubit -> Tot (Total.t int int)
val ids     : Total.t int qubit -> Tot (set int)
val data_q  : int -> Tot qubit
val anc_q   : int -> Tot qubit

let nullq    = { id = 0; ival = BFalse; cval = BFalse }
let getSubs  = mapVals (fun q -> q.id)
let ids m    = vals (getSubs m)
let data_q i = { id = i; ival = BVar i; cval = BFalse }
let anc_q i  = { id = i; ival = BFalse; cval = BFalse }


type circGCState =
  { top    : int;
    ah     : AncHeap;
    gates  : list Gate;
    symtab : Total.t int qubit }

val circGC       : circGCState -> int -> Tot circGCState
val circGCInit   : circGCState
val circGCAlloc  : circGCState -> Tot (int * circGCState)
val circGCAssign : circGCState -> int -> BoolExp -> Tot circGCState
val circGCEval   : circGCState -> state -> int -> Tot bool

(* The garbage collector needs to:
     -compile the current value in place (i.e. ival + cval + cval = ival),
     -if the qubit is an ancilla, push it back onto the heap, and
     -update the current value of all other bits by substituting q.id with ival + cval *)
val garbageCollect : circGCState -> qubit -> Tot circGCState
let garbageCollect cs q = 
  let (ah', res, ancs, circ) = compileBexp cs.ah q.id q.cval in
  let ah'' = if q.ival = BFalse then insert ah' q.id else ah' in
  let f q' = 
    let subq = fun v -> if v = q.id then BXor (q.ival, q.cval) else BVar v in
      { id   = q'.id; 
        ival = q'.ival; 
	cval = substBexpf q'.cval subq }
  in
  let symtab' = mapVals f cs.symtab in
    { top    = cs.top; 
      ah     = ah''; 
      gates  = cs.gates @ circ; 
      symtab = symtab' }

let circGCInit = 
  { top    = 0; 
    ah     = emptyHeap; 
    gates  = []; 
    symtab = constMap nullq }

let circGCAlloc cs = 
  let (ah', bit) = popMin cs.ah in
  let q = { id = bit; 
	    ival = BFalse; 
	    cval = BFalse } 
  in
  let cs' =
    { top = cs.top + 1;
      ah = ah';
      gates = cs.gates;
      smtab = update cs.symtab cs.top q }
  in
    (cs.top, cs')

let circGCAssign cs l bexp =
  let q = lookup cs.symtab l in
  let bexp' = substVar bexp (getSubs cs.symtab) in
  let bexpfac = factorAs bexp' q.id in
  match (q.cval, bexpfac) with
    | (BFalse, _)      -> // substitute q.id with BFalse, compile in place
      let bexp'' = substBexpf bexp' (fun v -> if v = q.id then BFalse else BVar v) in
      let (ah', res, ancs, circ) = compileBexp cs.ah q.id bexp'' in
      let q' = { id = q.id; ival = q.ival; cval = bexp'' } in
      let f b =
	let subq = fun v -> if v = q.id then bexp'' else BVar v in
	  { id = b.id; 
	    ival = b.ival; 
	    cval = substBexpf b.cval subq }
      in
      let symtab' = update (mapVals f cs.symtab) l q' in
        { top = cs.top; 
	  ah = ah'; 
	  gates = cs.gates @ circ; 
	  symtab = symtab' }
    | (_, Some bexp'') -> // compile in place, substitute q.id with q.id \oplus bexp''
      let (ah', res, ancs, circ') = compileBexp cs.ah q.id bexp'' in
      let q' = { id = q.id; ival = q.ival; cval = BXor (q.cval, bexp'') } in
      let f b = 
        let subq = fun v -> if v = q.id then BXor (BVar q.id, bexp'') else BVar v in
	  { id = b.id; 
	    ival = b.ival; 
	    cval = substBexpf b.cval subq }
      in
      let symtab' = update (mapVals f cs.symtab) l q' in
        { top = cs.top; 
	  ah = ah'; 
	  gates = cs.gates @ circ'; 
	  symtab = symtab' }
    | _                -> // Compile out of place, clean q.id
      let (ah', res, ancs, circ') = compileBexp_oop cs.ah bexp' in
      let q' = { id = res; ival = BFalse; cval = bexp' } in
      let cs' = 
	{ top = cs.top; 
	  ah = ah'; 
	  gates = cs.gates @ circ'; 
	  symtab = update cs.symtab l q' } 
      in
        garbageCollect cs' q

let circGCEval cs st i = lookup (evalCirc cs.gates st) (lookup cs.symtab i).id

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

(* Scrubs the state with respect to the remainder of the program
let findGarbage gexp cs = Set.diff (keys cs.symtab) (locs gexp)
let garbageCollector gexp cs = 
  let garbage = findGarbage gexp cs in
  let f cs l = 
    let q = lookup cs.symtab l in
    let cs' = garbageCollect cs q in
    { top = cs'.top; ah = cs'.ah; gates = cs'.gates; symtab = remove cs'.symtab l }
  in
    cs
  //Set.fold f cs garbage *)

val compileGCCirc : config circGCState -> Dv (result (list int * list Gate))
let rec compileGCCirc (gexp, cs) =
  let cs = cs in //garbageCollector gexp cs in
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

(** Verification utilities *)

(* A GCstate is valid w.r.t a set of initial values if
     - the heap starts above 0
     - everything on the heap is 0-valued after executing the circuit
     - no active qubit is in the heap
     - for every active qubit, q.ival = q' <> q.cval' *)
type validGCState (cs:circGCState) (init:state) =
  zeroHeap (evalCirc cs.gates init) cs.ah /\ 
  disjoint (ids cs.symtab) (elts cs.ah) /\
  (forall q. Set.mem q (vals cs.symtab) ==> 
    evalBexp q.ival init = evalBexp (BXor (BVar q.id, q.cval)) (evalCirc cs.gates init))

val subst_subset_active : cs:circGCState -> bexp:BoolExp ->
  Lemma (subset (vars (substVar bexp (getSubs cs.symtab))) (ids cs.symtab))
  (decreases bexp)
let rec subst_subset_active cs bexp = match bexp with
  | BFalse -> ()
  | BVar i -> admit() //lookup_is_val cs.symtab i -- no reason this should fail
  | BNot x -> subst_subset_active cs x
  | BAnd (x, y) | BXor (x, y) -> 
    subst_subset_active cs x;
    subst_subset_active cs y

(* These proofs are too big, takes forever to develop *)
val valid_alloc1 : cs:circGCState -> init:state -> bexp:BoolExp -> cs':circGCState ->
  Lemma (requires (validGCState cs init /\ cs' = snd (circGCAlloc cs bexp)))
	(ensures  (zeroHeap (evalCirc cs'.gates init) cs'.ah))
let valid_alloc1 cs init bexp cs' =
  let bexp' = substVar bexp (getSubs cs.symtab) in
  let (ah, bit) = popMin cs.ah in
  let (ah', _, _, gates) = compileBexp ah bit bexp' in
  let q = { id = bit; 
            ival = BFalse; 
            cval = bexp' } 
  in
  let init' = evalCirc cs'.gates init in
    pop_proper_subset cs.ah;
    zeroHeap_subset (evalCirc cs.gates init) cs.ah ah;
    compile_decreases_heap ah bit bexp';
    zeroHeap_subset (evalCirc cs.gates init) ah cs'.ah;
    //------------
    subst_subset_active cs bexp;
    disjoint_subset (elts ah) (elts cs.ah) (ids cs.symtab);
    disjoint_subset (vars bexp') (ids cs.symtab) (elts ah);
    compile_partition ah bit bexp';
    zeroHeap_st_impl (evalCirc cs.gates init) cs'.ah gates

val valid_alloc2 : cs:circGCState -> init:state -> bexp:BoolExp -> cs':circGCState ->
  Lemma (requires (validGCState cs init /\ cs' = snd (circGCAlloc cs bexp)))
	(ensures  (disjoint (ids cs'.symtab) (elts cs'.ah)))
let valid_alloc2 cs init bexp cs' =
  let bexp' = substVar bexp (getSubs cs.symtab) in
  let (ah, bit) = popMin cs.ah in
  let (ah', _, _, gates) = compileBexp ah bit bexp' in
  let q = { id = bit; 
            ival = BFalse; 
            cval = bexp' } 
  in
  let init' = evalCirc cs'.gates init in
    pop_proper_subset cs.ah;
    compile_decreases_heap ah bit bexp'

val valid_alloc4 : cs:circGCState -> init:state -> bexp:BoolExp -> cs':circGCState -> bit:int ->
  Lemma (requires (validGCState cs init /\ cs' = snd (circGCAlloc cs bexp)))
        (ensures  (evalBexp BFalse init = evalBexp (BXor (BVar (get_min cs.ah), 
	                                                  (substVar bexp (getSubs cs.symtab))))
	                                           (evalCirc cs'.gates init)))
let valid_alloc4 cs init bexp cs' bit =
  let bexp' = substVar bexp (getSubs cs.symtab) in
  let (ah, bit) = popMin cs.ah in
  let (ah', _, _, gates) = compileBexp ah bit bexp' in
  let q = { id = bit; 
            ival = BFalse; 
            cval = bexp' } 
  in
  let init' = evalCirc cs'.gates init in
    pop_proper_subset cs.ah;
    zeroHeap_subset (evalCirc cs.gates init) cs.ah ah;
    //------------
    subst_subset_active cs bexp;
    disjoint_subset (elts ah) (elts cs.ah) (ids cs.symtab);
    disjoint_subset (vars bexp') (ids cs.symtab) (elts ah);
    //------------
    compile_bexp_correct ah bit bexp' (evalCirc cs.gates init);
    eval_mod (evalCirc cs.gates init) gates;
    eval_state_swap (BXor (BVar q.id, q.cval)) (evalCirc cs.gates init) init'

val valid_alloc3 : cs:circGCState -> init:state -> bexp:BoolExp -> cs':circGCState ->
  Lemma (requires (validGCState cs init /\ cs' = snd (circGCAlloc cs bexp)))
	(ensures  (forall q. Set.mem q (vals cs.symtab) ==> 
                     evalBexp q.ival init = evalBexp (BXor (BVar q.id, q.cval)) (evalCirc cs'.gates init)))
let valid_alloc3 cs init bexp cs' =
  let bexp' = substVar bexp (getSubs cs.symtab) in
  let (ah, bit) = popMin cs.ah in
  let (ah', _, _, gates) = compileBexp ah bit bexp' in
  let q = { id = bit; 
            ival = BFalse; 
            cval = bexp' } 
  in
  let init' = evalCirc cs'.gates init in
    compile_mods ah bit bexp'

val valid_alloc : cs:circGCState -> init:state -> bexp:BoolExp ->
  Lemma (requires (validGCState cs init))
	(ensures  (validGCState (snd (circGCAlloc cs bexp)) init))
let valid_alloc cs init bexp =
  let bexp' = substVar bexp (getSubs cs.symtab) in
  let (ah, bit) = popMin cs.ah in
  let (ah', _, _, gates) = compileBexp ah bit bexp' in
  let q = { id = bit; 
            ival = BFalse; 
            cval = bexp' } 
  in
  let cs' = snd (circGCAlloc cs bexp) in
  let init' = evalCirc cs'.gates init in
  let zeroHeap_pres = admitP(zeroHeap init' ah')(*
    //------------ 
    pop_proper_subset cs.ah;
    zeroHeap_subset (evalCirc cs.gates init) cs.ah ah;
    compile_decreases_heap ah bit bexp';
    zeroHeap_subset (evalCirc cs.gates init) ah cs'.ah;
    //------------
    subst_subset_active cs bexp;
    disjoint_subset (elts ah) (elts cs.ah) (ids cs.symtab);
    disjoint_subset (vars bexp') (ids cs.symtab) (elts ah);
    compile_partition ah bit bexp';
    zeroHeap_st_impl (evalCirc cs.gates init) cs'.ah gates*)
  in
  let disjoint_pres = //admitP(disjoint (ids cs'.symtab) (elts cs'.ah))
    pop_proper_subset cs.ah;
    compile_decreases_heap ah bit bexp'
  in
  let cleanup_pres =
    //admitP(forall q. Set.mem q (vals cs.symtab) ==> 
    //                      evalBexp q.ival init = evalBexp (BXor (BVar q.id, q.cval)) init')
    compile_mods ah bit bexp'
  in
  let alloc_correct : u:unit{evalBexp q.ival init = evalBexp (BXor (BVar q.id, q.cval)) init'} =(*
    pop_proper_subset cs.ah;
    zeroHeap_subset (evalCirc cs.gates init) cs.ah ah;
    //------------
    subst_subset_active cs bexp;
    disjoint_subset (elts ah) (elts cs.ah) (ids cs.symtab);
    disjoint_subset (vars bexp') (ids cs.symtab) (elts ah);
    //------------
    compile_bexp_correct ah bit bexp' (evalCirc cs.gates init);
    eval_mod (evalCirc cs.gates init) gates;
    eval_state_swap (BXor (BVar q.id, q.cval)) (evalCirc cs.gates init) init';*)
    admitP(b2t(evalBexp q.ival init = evalBexp (BXor (BVar q.id, q.cval)) init'))
  in
    ()

type circ_equiv (st:boolState) (cs:circGCState) (init:state) =
  validGCState cs init /\ fst st = cs.top /\ (forall i. boolEval st init i = circGCEval cs init i)
