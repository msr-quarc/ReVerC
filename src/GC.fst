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

type circGCState =
  { top    : int;
    ah     : AncHeap;
    gates  : list Gate;
    symtab : Total.t int int;
    ivals  : Total.t int BoolExp;
    cvals  : Total.t int BoolExp }

val circGC       : circGCState -> int -> Tot circGCState
val circGCInit   : circGCState
val circGCAlloc  : circGCState -> Tot (int * circGCState)
val circGCAssign : circGCState -> int -> BoolExp -> Tot circGCState
val circGCEval   : circGCState -> state -> int -> Tot bool

(* The garbage collector needs to:
     -compile the current value in place (i.e. ival + cval + cval = ival),
     -if the qubit is an ancilla, push it back onto the heap, and
     -update the current value of all other bits by substituting q.id with ival + cval *)
val garbageCollect : circGCState -> int -> Tot circGCState
let garbageCollect cs bit = 
  let ival = lookup cs.ivals bit in
  let cval = lookup cs.cvals bit in
  let (ah', res, ancs, circ) = compileBexp cs.ah bit cval in
  let ah'' = if ival = BFalse then insert ah' bit else ah' in
  let f bexp = substOneVar bexp bit (BXor (ival, cval)) in
  let cvals' = mapVals f cs.cvals in
    { top    = cs.top; 
      ah     = ah''; 
      gates  = cs.gates @ circ; 
      symtab = cs.symtab;
      ivals  = cs.ivals;
      cvals  = cvals' }

let circGCInit = 
  { top    = 0; 
    ah     = emptyHeap; 
    gates  = []; 
    symtab = constMap 0;
    ivals  = constMap BFalse;
    cvals  = constMap BFalse }

let circGCAlloc cs = 
  let (ah', bit) = popMin cs.ah in
  let cs' =
    { top    = cs.top + 1;
      ah     = ah';
      gates  = cs.gates;
      symtab = update cs.symtab cs.top bit;
      ivals  = update cs.ivals bit BFalse;
      cvals  = update cs.cvals bit BFalse }
  in
    (cs.top, cs')

let circGCAssign cs l bexp =
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  let bexpfac = factorAs bexp' bit in
  match (lookup cs.cvals bit, bexpfac) with
    | (BFalse, _)      -> // substitute bit with BFalse, compile in place
      let bexp'' = substOneVar bexp' bit BFalse in
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit bexp'' in
      let cvals' = update (mapVals f cs.cvals) bit bexp'' in
        { top    = cs.top; 
	  ah     = ah'; 
	  gates  = cs.gates @ circ; 
	  symtab = cs.symtab;
	  ivals  = cs.ivals;
	  cvals  = cvals'}
    | (cval, Some bexp'') -> // compile in place, substitute q.id with q.id \oplus bexp''
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit (BXor (BVar bit, bexp'')) in
      let cvals' = update (mapVals f cs.cvals) bit (BXor (cval, bexp'')) in
        { top    = cs.top; 
	  ah     = ah'; 
	  gates  = cs.gates @ circ'; 
	  symtab = cs.symtab;
	  ivals  = cs.ivals;
	  cvals  = cvals' }
    | _                -> // Compile out of place, clean q.id
      let (ah', bit', _, circ') = compileBexp_oop cs.ah bexp' in
      let symtab' = update cs.symtab l bit' in
      let ivals' = update cs.ivals bit' BFalse in
      let cvals' = update cs.cvals bit' bexp' in
      let cs' = 
	{ top    = cs.top; 
	  ah     = ah'; 
	  gates  = cs.gates @ circ'; 
	  symtab = symtab';
	  ivals  = ivals';
	  cvals  = cvals' } 
      in
        garbageCollect cs' bit

let circGCEval cs st i = lookup (evalCirc cs.gates st) (lookup cs.symtab i)

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
    let (ah', bit) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                symtab = update cs.symtab cs.top bit;
		ivals = update cs.ivals bit (BVar bit);
		cvals = update cs.cvals bit BFalse }
    in
      allocNcircGC (((LOC cs.top)::locs), cs') (i-1)

val allocTycircGC : GType -> circGCState -> Tot (result (GExpr * circGCState))
let allocTycircGC ty cs = match ty with
  | GBool ->
    let (ah', bit) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                symtab = update cs.symtab cs.top bit;
		ivals = update cs.ivals bit (BVar bit);
		cvals = update cs.cvals bit BFalse }
    in
      Val (LOC cs.top, cs')
  | GArray n ->
    let (locs, st') = allocNcircGC ([], cs) n in
      Val (ARRAY locs, st')
  | _ -> Err "Invalid parameter type for circuit generation"

val lookup_Lst_gc : Total.t int int -> lst:(list GExpr){isVal_lst lst} -> Tot (list int)
let rec lookup_Lst_gc symtab lst = match lst with
  | [] -> []
  | (LOC l)::xs -> ((lookup symtab l))::(lookup_Lst_gc symtab xs)

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
      let bit = lookup cs.symtab l in
        Val ([bit], cs.gates)
    | ARRAY lst ->
      let bits = lookup_Lst_gc cs.symtab lst in
        Val (bits, cs.gates)
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
  disjoint (vals cs.symtab) (elts cs.ah) /\
  (forall bit. Set.mem bit (vals cs.symtab) ==> 
    evalBexp (lookup cs.ivals bit) init = 
    evalBexp (BXor (BVar bit, (lookup cs.cvals bit))) (evalCirc cs.gates init))

val valid_alloc : cs:circGCState -> init:state ->
  Lemma (requires (validGCState cs init))
	(ensures  (validGCState (snd (circGCAlloc cs)) init))
let valid_alloc cs init =
  let (ah', bit) = popMin cs.ah in
  let cs' = snd (circGCAlloc cs) in
    pop_proper_subset cs.ah;
    zeroHeap_subset (evalCirc cs.gates init) cs.ah cs'.ah

val cvals_vars_lem : cvals:Total.t int BoolExp -> bit:int -> exp:BoolExp ->
  Lemma (forall exp'. Set.mem exp' (vals cvals) ==> 
	   subset (vars (substOneVar exp' bit exp)) (union (rem bit (vars exp')) (vars exp)))
  (decreases (cvals.elts))
let rec cvals_vars_lem cvals bit exp = match cvals.elts with
  | [] -> substOneVar_elems cvals.dval bit exp
  | x::xs -> 
    let cvals' = { elts = xs; dval = cvals.dval } in
      substOneVar_elems (snd x) bit exp; 
      cvals_vars_lem cvals' bit exp

val cvals_update_lem : cvals:Total.t int BoolExp -> bit:int -> exp:BoolExp -> st:state -> st':state ->
  Lemma (requires (evalBexp (BVar bit) st = evalBexp exp st' /\ 
                   (forall exp'. Set.mem exp' (vals cvals) ==> agree_on st st' (rem bit (vars exp')))))
	(ensures  (forall exp'. Set.mem exp' (vals cvals) ==> 
		     evalBexp exp' st = evalBexp (substOneVar exp' bit exp) st'))
  (decreases (cvals.elts))
let rec cvals_update_lem cvals bit exp st st' = match cvals.elts with
  | [] -> subst_value_pres cvals.dval bit exp st st'
  | x::xs -> 
    let cvals' = { elts = xs; dval = cvals.dval } in
      subst_value_pres (snd x) bit exp st st'; 
      cvals_update_lem cvals' bit exp st st'

(* More precisely tuned version *)
val cvals_vars_lem2 : symtab:Total.t int int -> cvals:Total.t int BoolExp -> 
		      bit:int -> exp:BoolExp -> s:set int ->
  Lemma (requires (subset (vars exp) s /\ 
		  (forall bit'. Set.mem bit' (vals symtab) ==> subset (vars (lookup cvals bit')) s)))
	(ensures  (forall bit'. Set.mem bit' (vals symtab) ==> 
		     subset (vars (substOneVar (lookup cvals bit') bit exp)) s))
  (decreases (symtab.elts))
let rec cvals_vars_lem2 symtab cvals bit exp s = match symtab.elts with
  | [] -> substOneVar_elems (lookup cvals symtab.dval) bit exp
  | x::xs -> 
    let symtab' = { elts = xs; dval = symtab.dval } in
      substOneVar_elems (lookup cvals (snd x)) bit exp; 
      cvals_vars_lem2 symtab' cvals bit exp s

(* These lemmas relate to the partitioning of the ancilla heap wrt the allocated values.
   Note that the statement actually doesn't require that all bits used in the circuit
   are not in the ancilla heap, only that all active bits are not in the heap. This will
   be important if we want to use a pebble strategy *)

val garbage_partition_lemma : cs:circGCState -> bit:int -> cs':circGCState ->
  Lemma (requires (cs' = garbageCollect cs bit /\ 
		   disjoint (vals cs.symtab) (elts cs.ah) /\
		   (forall bit. Set.mem bit (vals cs.symtab) ==> 
		     subset (vars (lookup cs.cvals bit)) (vals cs.symtab))))
	(ensures  (disjoint (vals cs'.symtab) (elts cs'.ah) /\
		   (forall bit. Set.mem bit (vals cs'.symtab) ==> 
		     subset (vars (lookup cs'.cvals bit)) (vals cs'.symtab))))
let garbage_partition_lemma cs bit cs' =
  let ival = lookup cs.ivals bit in
  let cval = lookup cs.cvals bit in
  let (ah', res, ancs, circ) = compileBexp cs.ah bit cval in
  let ah'' = if ival = BFalse then insert ah' bit else ah' in
  let f bexp = substOneVar bexp bit (BXor (ival, cval)) in
  let cvals' = mapVals f cs.cvals in
    assert(elts cs'.ah = ins bit (elts cs.ah));
    admitP(disjoint (vals cs'.symtab) (elts cs'.ah));
    admitP(forall bit. Set.mem bit (vals cs'.symtab) ==> 
             subset (vars (lookup cs'.cvals bit)) (vals cs'.symtab))

val assign_partition_lemma : cs:circGCState -> l:int -> bexp:BoolExp -> cs':circGCState ->
  Lemma (requires (cs' = circGCAssign cs l bexp /\ 
		   disjoint (vals cs.symtab) (elts cs.ah) /\
		   (forall bit. Set.mem bit (vals cs.symtab) ==> 
		     subset (vars (lookup cs.cvals bit)) (vals cs.symtab))))
	(ensures  (disjoint (vals cs'.symtab) (elts cs'.ah) /\
		   (forall bit. Set.mem bit (vals cs'.symtab) ==> 
		     subset (vars (lookup cs'.cvals bit)) (vals cs'.symtab))))
let assign_partition_lemma cs l bexp cs' =
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  let bexpfac = factorAs bexp' bit in
  substVar_elems bexp cs.symtab;      // subset (vars bexp') (vals cs.symtab)
  match (lookup cs.cvals bit, bexpfac) with
    | (BFalse, _)      ->
      let bexp'' = substOneVar bexp' bit BFalse in
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit bexp'' in
	compile_decreases_heap cs.ah bit bexp'';                  // subset cs.ah' cs.ah
	disjoint_subset (elts ah') (elts cs.ah) (vals cs.symtab); // disjoint cs.ah' (ids cs.symtab)
	//admitP(disjoint (vals cs'.symtab) (elts cs'.ah));
	substOneVar_elems bexp' bit BFalse; // subset (vars bexp'') (vars bexp' \ bit)
	cvals_vars_lem2 cs.symtab cs.cvals bit bexp'' (vals cs'.symtab)
	//admitP(forall bit. Set.mem bit (vals cs'.symtab) ==> 
	//	 subset (vars (lookup cs'.cvals bit)) (vals cs'.symtab))
    | (_, Some bexp'') ->
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit (BXor (BVar bit, bexp'')) in
	compile_decreases_heap cs.ah bit bexp'';                  // subset cs.ah' cs.ah
	disjoint_subset (elts ah') (elts cs.ah) (vals cs.symtab); // disjoint cs.ah' (ids cs.symtab)
	//admitP(disjoint (vals cs'.symtab) (elts cs'.ah));
	factorAs_vars bexp' bit; // subset (vars bexp'') (vars bexp' \ bit)
	ins_subset_pres bit (vars bexp'') (rem bit (vars bexp'));
	cvals_vars_lem2 cs.symtab cs.cvals bit (BXor (BVar bit, bexp'')) (vals cs'.symtab)
	//admitP(forall bit. Set.mem bit (vals cs'.symtab) ==> 
	//	 subset (vars (lookup cs'.cvals bit)) (vals cs'.symtab))
    | _                ->
      let (ah', bit', _, circ') = compileBexp_oop cs.ah bexp' in
      let symtab' = update cs.symtab l bit' in
      let ivals' = update cs.ivals bit' BFalse in
      let cvals' = update cs.cvals bit' bexp' in
      let cs'' = 
	{ top    = cs.top; 
	  ah     = ah'; 
	  gates  = cs.gates @ circ'; 
	  symtab = symtab';
	  ivals  = ivals';
	  cvals  = cvals' } 
      in
	compile_decreases_heap_oop cs.ah bexp';
	disjoint_subset (elts ah') (elts cs.ah) (vals cs.symtab); // disjoint cs.ah' (vals cs.symtab)
	compile_partition_oop cs.ah bexp';
	//admitP(disjoint (vals cs''.symtab) (elts cs''.ah));
	//admitP(forall bit. Set.mem bit (vals cs''.symtab) ==> 
	//	 subset (vars (lookup cs''.cvals bit)) (vals cs''.symtab));
	garbage_partition_lemma cs'' bit cs'

val valid_assign : cs:circGCState -> l:int -> bexp:BoolExp -> init:state ->
  Lemma (requires (validGCState cs init))
	(ensures  (validGCState (circGCAssign cs l bexp) init))
let valid_assign cs l bexp init =
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  let bexpfac = factorAs bexp' bit in
  let cs' = circGCAssign cs l bexp in
  let st = evalCirc cs.gates init in
  let st' = evalCirc cs'.gates init in
  match (lookup cs.cvals bit, bexpfac) with
    | (BFalse, _)      -> 
      let bexp'' = substOneVar bexp' bit BFalse in
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit bexp'' in
	substVar_elems bexp cs.symtab;      // subset (vars bexp') (vals cs.symtab)
	substOneVar_elems bexp' bit BFalse; // subset (vars bexp'') (vars bexp' \ bit)
	lookup_is_val cs.symtab l;          // bit in (vals symtab)
	compile_bexp_zero cs.ah bit bexp'' st;
	//admitP(zeroHeap (evalCirc cs'.gates init) cs'.ah);
	compile_decreases_heap cs.ah bit bexp'';                  // subset cs.ah' cs.ah
	disjoint_subset (elts ah') (elts cs.ah) (vals cs.symtab); // disjoint cs.ah' (ids cs.symtab)
	//admitP(disjoint (ids cs'.symtab) (elts cs'.ah));
	compile_bexp_correct cs.ah bit bexp'' st; // lookup bit st' = lookup bit st <> evalBexp bexp'' st 
	compile_mods cs.ah bit bexp'';            // subset (mods circ) (ins bit (elts cs.ah))
	eval_mod st circ;                         // agree_on st st' complement (mods circ)
	eval_state_swap bexp'' st st';            // evalBexp bexp'' st = evalBexp bexp'' st'
	admitP(b2t(evalBexp (BXor (BVar bit, (lookup cs.cvals bit))) st =
	           evalBexp (BXor (BVar bit, (lookup cs'.cvals bit))) st'));
	disjoint_is_subset_compl (rem bit (vals cs'.symtab)) (ins bit (elts cs.ah));
	subset_compl_reverse (mods circ) (ins bit (elts cs.ah));
	subset_trans (rem bit (vals cs'.symtab)) (complement (ins bit (elts cs.ah))) (complement (mods circ));
	agree_on_subset st st' (complement (mods circ)) (rem bit (vals cs'.symtab));
	//assert(forall b. (Set.mem b (rem bit (vals cs'.symtab))) ==> evalBexp (BVar b) st = evalBexp (BVar b) st');
	//assert(agree_on st st' (rem bit (vals cs'.symtab))); 
	admitP(forall b. (Set.mem b (vals cs'.symtab) /\ not (b = bit)) ==> 
	  evalBexp (BXor (BVar b, (lookup cs.cvals b))) (evalCirc cs.gates init) =
	  evalBexp (BXor (BVar b, (lookup cs'.cvals b))) (evalCirc cs'.gates init))
    | (_, Some bexp'') ->
	admitP(validGCState cs' init) (*
	admitP(zeroHeap (evalCirc cs'.gates init) cs'.ah);
	admitP(disjoint (ids cs'.symtab) (elts cs'.ah));
	admitP(forall q. Set.mem q (vals cs'.symtab) ==> 
	  evalBexp q.ival init = evalBexp (BXor (BVar q.id, q.cval)) (evalCirc cs'.gates init))*)
    | _                ->
	admitP(validGCState cs' init)(*
	admitP(zeroHeap (evalCirc cs'.gates init) cs'.ah);
	admitP(disjoint (ids cs'.symtab) (elts cs'.ah));
	admitP(forall q. Set.mem q (vals cs'.symtab) ==> 
	  evalBexp q.ival init = evalBexp (BXor (BVar q.id, q.cval)) (evalCirc cs'.gates init))*)

type circ_equiv (st:boolState) (cs:circGCState) (init:state) =
  validGCState cs init /\ fst st = cs.top /\ (forall i. boolEval st init i = circGCEval cs init i)
