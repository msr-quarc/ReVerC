(** Garbage collection *)
module GC

open Utils
open FStar.Set
open SetExtra
open Total
open AncillaHeap
open BoolExp
open Circuit
open ExprTypes
open Interpreter

(* Garbage-collected reversible circuit compilation -- experimental *)

type circGCState =
  { top    : int;
    ah     : ancHeap;
    gates  : list gate;
    symtab : Total.t int int;
    isanc  : Total.t int bool;
    cvals  : Total.t int boolExp }

val circGCInit   : circGCState
val circGCAlloc  : circGCState -> Tot (int * circGCState)
val circGCAssign : circGCState -> int -> boolExp -> Tot circGCState
val circGCEval   : circGCState -> state -> int -> Tot bool

(* The garbage collector needs to:
     -compile the current value in place (i.e. ival + cval + cval = ival),
     -if the qubit is an ancilla, push it back onto the heap, and
     -update the current value of all other bits by substituting q.id with ival + cval *)
val garbageCollect : circGCState -> int -> Tot circGCState
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
      let bexp'' = substOneVar bexp' bit BFalse in
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit BFalse in
      let cvals' = update (mapVals f cs.cvals) bit bexp'' in
        { top    = cs.top; 
	  ah     = ah'; 
	  gates  = cs.gates @ circ; 
	  symtab = cs.symtab;
	  isanc  = cs.isanc;
	  cvals  = cvals'}
    | (cval, Some bexp'', _) -> // compile in place, substitute q.id with q.id \oplus bexp''
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
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ') = compileBexp ah' bit' bexp' in
      let cs' = 
	{ top    = cs.top; 
	  ah     = ah''; 
	  gates  = cs.gates @ circ'; 
	  symtab = update cs.symtab l bit';
	  isanc  = update cs.isanc bit' true;
	  cvals  = update cs.cvals bit' bexp' } 
      in
        garbageCollect cs' bit

let circGCEval cs st i = lookup (evalCirc cs.gates st) (lookup cs.symtab i)

let circGCInterp = {
  alloc = circGCAlloc;
  assign = circGCAssign;
  eval = circGCEval
}

val allocNcircGC : list gExpr * circGCState -> i:int ->
  Tot (list gExpr * circGCState) (decreases i)
let rec allocNcircGC (locs, cs) i =
  if i <= 0 then (FStar.List.Tot.rev locs, cs)
  else
    let (ah', bit) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                symtab = update cs.symtab cs.top bit;
		isanc = update cs.isanc bit false;
		cvals = update cs.cvals bit BFalse }
    in
      allocNcircGC (((LOC cs.top)::locs), cs') (i-1)

val allocTycircGC : gType -> circGCState -> Tot (result (gExpr * circGCState))
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

val lookup_Lst_gc : Total.t int int -> lst:(list gExpr){isVal_lst lst} -> Tot (list int)
let rec lookup_Lst_gc symtab lst = match lst with
  | [] -> []
  | (LOC l)::xs -> ((lookup symtab l))::(lookup_Lst_gc symtab xs)

(* Scrubs the state with respect to the remainder of the program *)
let findGarbage gexp cs = SetExtra.diff (keys cs.symtab) (locs gexp)
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
    SetExtra.fold f cs garbage

val compileGCCirc : config circGCState -> Dv (result (list int * list gate))
let rec compileGCCirc (gexp, cs) =
  let cs = cs in //garbageCollector gexp cs in
  if isVal gexp then match gexp with
    | UNIT -> Val ([], cs.gates)
    | LAMBDA (x, ty, t) ->
      begin match allocTycircGC ty cs with
        | Err s -> Err s
        | Val (v, cs') -> compileGCCirc (substgExpr t x v, cs')
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

(* More precisely tuned lemmas *)
val cvals_vars_lemma : symtab:Total.t int int -> cvals:Total.t int boolExp ->
		       bit:int -> exp:boolExp -> s:set int ->
  Lemma (requires (disjoint (vars exp) s /\ not (Set.mem bit (vars exp)) /\
		  (forall bit'. Set.mem bit' (vals symtab) ==> 
		    disjoint (vars (lookup cvals bit')) s)))
	(ensures  (forall bit'. Set.mem bit' (vals symtab) ==> 
		    disjoint (vars (substOneVar (lookup cvals bit') bit exp)) (ins bit s)))
  (decreases symtab.elts)
let rec cvals_vars_lemma symtab cvals bit exp s = match symtab.elts with
  | [] -> substOneVar_elems (lookup cvals symtab.dval) bit exp
  | x::xs ->
    let symtab' = { elts = xs; dval = symtab.dval } in
      substOneVar_elems (lookup cvals (snd x)) bit exp; 
      destruct_vals x symtab symtab';
      cvals_vars_lemma symtab' cvals bit exp s

val cvals_vars_lemma2 : symtab:Total.t int int -> cvals:Total.t int boolExp ->
		       bit:int -> exp:boolExp -> s:set int ->
  Lemma (requires (disjoint (vars exp) s /\
		  (forall bit'. Set.mem bit' (vals symtab) ==> 
		    disjoint (vars (lookup cvals bit')) s)))
	(ensures  (forall bit'. Set.mem bit' (vals symtab) ==> 
		    disjoint (vars (substOneVar (lookup cvals bit') bit exp)) s))
  (decreases symtab.elts)
let rec cvals_vars_lemma2 symtab cvals bit exp s = match symtab.elts with
  | [] -> substOneVar_elems (lookup cvals symtab.dval) bit exp
  | x::xs ->
    let symtab' = { elts = xs; dval = symtab.dval } in
      substOneVar_elems (lookup cvals (snd x)) bit exp; 
      destruct_vals x symtab symtab';
      cvals_vars_lemma2 symtab' cvals bit exp s

(* These lemmas relate to the partitioning of the ancilla heap wrt the allocated values.
   Note that the statement actually doesn't require that all bits used in the circuit
   are not in the ancilla heap, only that all active bits are not in the heap. This will
   be important if we want to use a pebble strategy *)

val garbage_partition_lemma : cs:circGCState -> bit:int -> cs':circGCState ->
  Lemma (requires (cs' = garbageCollect cs bit /\ 
		   not (Set.mem bit (vals cs.symtab)) /\
		   not (Set.mem bit (elts cs.ah)) /\
		   disjoint (vals cs.symtab) (elts cs.ah) /\
		   disjoint (vars (lookup cs.cvals bit)) (elts cs.ah) /\
		   (forall bit. Set.mem bit (vals cs.symtab) ==> 
		     disjoint (vars (lookup cs.cvals bit)) (elts cs.ah))))
	(ensures  (disjoint (vals cs'.symtab) (elts cs'.ah) /\
		   (forall bit. Set.mem bit (vals cs'.symtab) ==> 
		     disjoint (vars (lookup cs'.cvals bit)) (elts cs'.ah))))
let garbage_partition_lemma cs bit cs' =
  let cval = lookup cs.cvals bit in
  if Set.mem bit (vars cval) then () else
  let (ah', _, _, circ) = compileBexp cs.ah bit cval in
    match lookup cs.isanc bit with
      | true ->
	let f bexp = substOneVar bexp bit cval in
	let cvals' = mapVals f cs.cvals in
	let ah''   = insert ah' bit in
          compile_decreases_heap cs.ah bit cval;                    // subset ah' cs.ah
          disjoint_subset (elts ah') (elts cs.ah) (vals cs.symtab); // disjoint ah' (vals cs.symtab)
          elts_insert ah' bit;                                      // subset ah'' (ins bit ah')
          disjoint_subset (elts ah') (elts cs.ah) (vars cval);      // disjoint ah' (vars cval)
	  cvals_vars_lemma cs.symtab cs.cvals bit cval (elts ah')
      | false -> 
        let f bexp = substOneVar bexp bit (BXor (BVar bit, cval)) in
        let cvals' = mapVals f cs.cvals in
          compile_decreases_heap cs.ah bit cval;                    // subset ah' cs.ah
          disjoint_subset (elts ah') (elts cs.ah) (vals cs.symtab); // disjoint ah' (vals cs.symtab)
	  cvals_vars_lemma2 cs.symtab cs.cvals bit (BXor (BVar bit, cval)) (elts ah')

val assign_partition_lemma : cs:circGCState -> l:int -> bexp:boolExp -> cs':circGCState ->
  Lemma (requires ((cs' = circGCAssign cs l bexp) /\ 
                   (forall l l'. not (l = l') ==> not (lookup cs.symtab l = lookup cs.symtab l')) /\
		   (disjoint (vals cs.symtab) (elts cs.ah)) /\
		   (forall bit. Set.mem bit (vals cs.symtab) ==> 
		     disjoint (vars (lookup cs.cvals bit)) (elts cs.ah))))
	(ensures  (disjoint (vals cs'.symtab) (elts cs'.ah) /\
		   (forall bit. Set.mem bit (vals cs'.symtab) ==> 
		     disjoint (vars (lookup cs'.cvals bit)) (elts cs'.ah))))
let assign_partition_lemma cs l bexp cs' =
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  substVar_elems bexp cs.symtab;
  match (lookup cs.cvals bit, factorAs bexp' bit, lookup cs.isanc bit) with
    | (BFalse, _, true)      ->
      let bexp'' = substOneVar bexp' bit BFalse in
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit BFalse in
	compile_decreases_heap cs.ah bit bexp'';
	disjoint_subset (elts ah') (elts cs.ah) (vals cs.symtab);
	substOneVar_elems bexp' bit BFalse;
	cvals_vars_lemma2 cs.symtab cs.cvals bit BFalse (elts cs'.ah)
    | (_, Some bexp'', _) ->
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit (BXor (BVar bit, bexp'')) in
	compile_decreases_heap cs.ah bit bexp'';
	disjoint_subset (elts ah') (elts cs.ah) (vals cs.symtab);
	factorAs_vars bexp' bit;
	ins_subset_pres bit (vars bexp'') (rem bit (vars bexp'));
	ins_rem_equal bit (vars bexp');
	mem_ins_equal bit (vars bexp');
	cvals_vars_lemma2 cs.symtab cs.cvals bit (BXor (BVar bit, bexp'')) (elts cs'.ah)
    | _                ->   // This part could use some optimizing
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ') = compileBexp ah' bit' bexp' in
      let cs'' = 
	{ top    = cs.top; 
	  ah     = ah''; 
	  gates  = cs.gates @ circ'; 
	  symtab = update cs.symtab l bit';
	  isanc  = update cs.isanc bit' true;
	  cvals  = update cs.cvals bit' bexp' } 
      in
        pop_proper_subset cs.ah;
	compile_decreases_heap ah' bit' bexp';
	lookup_subset cs.symtab cs.top bit';
	subset_trans (elts ah'') (elts ah') (elts cs.ah);
	disjoint_subset (elts ah'') (elts cs.ah) (vals cs.symtab);
	compile_partition ah' bit' bexp';
	lookup_is_val cs.symtab l;
        lookup_converse2 cs''.symtab bit;
	garbage_partition_lemma cs'' bit cs'

(* These lemmas establish zero-ness of the ancilla heap *)

val garbage_zeroHeap_lemma : cs:circGCState -> bit:int -> init:state -> cs':circGCState ->
  Lemma (requires ((cs' = garbageCollect cs bit) /\ 
		   (not (Set.mem bit (elts cs.ah))) /\
		   (disjoint (vars (lookup cs.cvals bit)) (elts cs.ah)) /\
		   (zeroHeap init cs.ah) /\
		   (zeroHeap (evalCirc cs.gates init) cs.ah) /\
		   (b2t(lookup cs.isanc bit) ==> lookup init bit = false) /\
		   (evalBexp (BXor (BVar bit, (lookup cs.cvals bit))) (evalCirc cs.gates init) =
		      lookup init bit)))
	(ensures  (zeroHeap init cs'.ah /\
	           zeroHeap (evalCirc cs'.gates init) cs'.ah))
let garbage_zeroHeap_lemma cs bit init cs' =
  let cval = lookup cs.cvals bit in
  if Set.mem bit (vars cval) then () else
  let (ah', _, _, circ) = compileBexp cs.ah bit cval in
    match lookup cs.isanc bit with
      | true ->
	compile_decreases_heap cs.ah bit cval;
	zeroHeap_subset init cs.ah ah';
	compile_bexp_zero cs.ah bit cval (evalCirc cs.gates init);
	compile_bexp_correct cs.ah bit cval (evalCirc cs.gates init);
	zeroHeap_insert init ah' bit;
	zeroHeap_insert (evalCirc cs'.gates init) ah' bit
      | false ->
	compile_decreases_heap cs.ah bit cval;
	zeroHeap_subset init cs.ah ah';
	compile_bexp_zero cs.ah bit cval (evalCirc cs.gates init)

val assign_zeroHeap_lemma : cs:circGCState -> l:int -> bexp:boolExp -> init:state -> cs':circGCState ->
  Lemma (requires ((cs' = circGCAssign cs l bexp) /\ 
		   (zeroHeap init cs.ah) /\
		   (zeroHeap (evalCirc cs.gates init) cs.ah) /\
		   (disjoint (vals cs.symtab) (elts cs.ah)) /\
		   (forall bit. Set.mem bit (vals cs.symtab) ==> 
		     disjoint (vars (lookup cs.cvals bit)) (elts cs.ah)) /\
		   (forall bit. Set.mem bit (vals cs.symtab) ==>
		     b2t(lookup cs.isanc bit) ==> lookup init bit = false) /\
		   (forall bit. Set.mem bit (vals cs.symtab) ==>
		     evalBexp (BXor (BVar bit, (lookup cs.cvals bit))) (evalCirc cs.gates init) =
		     lookup init bit)))
	(ensures  (zeroHeap init cs'.ah /\
	           zeroHeap (evalCirc cs'.gates init) cs'.ah))
let assign_zeroHeap_lemma cs l bexp init cs' =
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  let st  = evalCirc cs.gates init in
  lookup_is_val cs.symtab l;
  substVar_elems bexp cs.symtab;
  match (lookup cs.cvals bit, factorAs bexp' bit, lookup cs.isanc bit) with
    | (BFalse, _, true)      ->
      let bexp'' = substOneVar bexp' bit BFalse in
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
	compile_decreases_heap cs.ah bit bexp'';
	zeroHeap_subset init cs.ah ah';
	substOneVar_elems bexp' bit BFalse;
	compile_bexp_zero cs.ah bit bexp'' st
    | (_, Some bexp'', _) ->
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
	compile_decreases_heap cs.ah bit bexp'';
	zeroHeap_subset init cs.ah ah';
	factorAs_vars bexp' bit;
	compile_bexp_zero cs.ah bit bexp'' st
    | _                ->
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ') = compileBexp ah' bit' bexp' in
      let cs'' = 
	{ top    = cs.top; 
	  ah     = ah''; 
	  gates  = cs.gates @ circ'; 
	  symtab = update cs.symtab l bit';
	  isanc  = update cs.isanc bit' true;
	  cvals  = update cs.cvals bit' bexp' } 
      in
      let st' = evalCirc cs''.gates init in
	pop_proper_subset cs.ah;
	pop_elt cs.ah;
	compile_decreases_heap ah' bit' bexp';
	compile_bexp_zero ah' bit' bexp' st;
	compile_mods ah' bit' bexp';
	eval_mod st circ';
	disjoint_is_subset_compl (vars (BXor (BVar bit, lookup cs.cvals bit))) (complement (mods circ'));
	agree_on_subset st st' (complement (mods circ')) (vars (BXor (BVar bit, lookup cs.cvals bit)));
	eval_state_swap (BXor (BVar bit, lookup cs.cvals bit)) st st';
	garbage_zeroHeap_lemma cs'' bit init cs'

(* (internal) Correctness properties *)
val cvals_update_lemma : symtab:Total.t int int -> cvals:Total.t int boolExp -> 
		         bit:int -> exp:boolExp -> st:state -> st':state ->
  Lemma (requires (lookup st bit = evalBexp exp st' /\ 
                  (forall bit'. Set.mem bit' (vals symtab) ==> 
		     agree_on st st' (rem bit (vars (lookup cvals bit'))))))
	(ensures  (forall bit'. Set.mem bit' (vals symtab) ==> 
		     evalBexp (lookup cvals bit') st = evalBexp (substOneVar (lookup cvals bit') bit exp) st'))
  (decreases (symtab.elts))
let rec cvals_update_lemma symtab cvals bit exp st st' = match symtab.elts with
  | [] -> subst_value_pres (lookup cvals symtab.dval) bit exp st st'
  | x::xs -> 
    let symtab' = { elts = xs; dval = symtab.dval } in
      destruct_val x symtab;
      destruct_vals x symtab symtab';
      subst_value_pres (lookup cvals (snd x)) bit exp st st'; 
      cvals_update_lemma symtab' cvals bit exp st st'

val cvals_agree_lemma : symtab:Total.t int int -> cvals:Total.t int boolExp -> 
		         bit:int -> exp:boolExp -> st:state -> circ:circuit ->
  Lemma (requires (forall bit'. Set.mem bit' (vals symtab) ==> 
		     disjoint (rem bit (vars (lookup cvals bit'))) (mods circ)))
	(ensures  (forall bit'. Set.mem bit' (vals symtab) ==> 
		     agree_on st (evalCirc circ st) (rem bit (vars (lookup cvals bit')))))
  (decreases (symtab.elts))
let rec cvals_agree_lemma symtab cvals bit exp st circ = match symtab.elts with
  | [] -> 
    let bit' = symtab.dval in
      disjoint_is_subset_compl (rem bit (vars (lookup cvals bit'))) (mods circ);
      eval_mod st circ;
      agree_on_subset st (evalCirc circ st) (complement (mods circ)) (rem bit (vars (lookup cvals bit')))
  | x::xs -> 
    let bit' = snd x in
    let symtab' = { elts = xs; dval = symtab.dval } in
      destruct_val x symtab;
      destruct_vals x symtab symtab';
      disjoint_is_subset_compl (rem bit (vars (lookup cvals bit'))) (mods circ);
      eval_mod st circ;
      agree_on_subset st (evalCirc circ st) (complement (mods circ)) (rem bit (vars (lookup cvals bit')));
      cvals_agree_lemma symtab' cvals bit exp st circ

val cvals_lemma : symtab:Total.t int int -> cvals:Total.t int boolExp -> 
		  bit:int -> exp:boolExp -> st:state -> circ:circuit ->
  Lemma (requires (lookup st bit = evalBexp exp (evalCirc circ st) /\
                  (forall bit'. Set.mem bit' (vals symtab) ==> 
		     disjoint (rem bit (vars (lookup cvals bit'))) (mods circ))))
	(ensures  (forall bit'. Set.mem bit' (vals symtab) ==> 
		     evalBexp (lookup cvals bit') st = 
		       evalBexp (substOneVar (lookup cvals bit') bit exp) (evalCirc circ st)))
let cvals_lemma symtab cvals bit exp st circ =
  cvals_agree_lemma symtab cvals bit exp st circ;
  cvals_update_lemma symtab cvals bit exp st (evalCirc circ st)

val cvals_pres_lemma : symtab:Total.t int int -> cvals:Total.t int boolExp -> 
		  bit:int -> st:state -> circ:circuit ->
  Lemma (requires (forall bit'. Set.mem bit' (vals symtab) ==> 
		     disjoint (vars (lookup cvals bit')) (mods circ)))
	(ensures  (forall bit'. Set.mem bit' (vals symtab) ==> 
	             evalBexp (lookup cvals bit') st = evalBexp (lookup cvals bit') (evalCirc circ st)))
  (decreases (symtab.elts))
let rec cvals_pres_lemma symtab cvals bit st circ = match symtab.elts with
  | [] ->
    let bit' = symtab.dval in
      disjoint_is_subset_compl (vars (lookup cvals bit')) (mods circ);
      eval_mod st circ;
      agree_on_subset st (evalCirc circ st) (complement (mods circ)) (vars (lookup cvals bit'));
      eval_state_swap (lookup cvals bit') st (evalCirc circ st)
  | x::xs ->
    let bit' = snd x in
    let symtab' = { elts = xs; dval = symtab.dval } in
      destruct_val x symtab;
      destruct_vals x symtab symtab';
      disjoint_is_subset_compl (vars (lookup cvals bit')) (mods circ);
      eval_mod st circ;
      agree_on_subset st (evalCirc circ st) (complement (mods circ)) (vars (lookup cvals bit'));
      eval_state_swap (lookup cvals bit') st (evalCirc circ st);
      cvals_pres_lemma symtab' cvals bit st circ

val xor_inverse : b:bool -> Lemma (b <> b = false)
val xor_assoc   : b1:bool -> b2:bool -> b3:bool -> Lemma (b1 <> (b2 <> b3) = (b1 <> b2) <> b3)

let xor_inverse b = ()
let xor_assoc b1 b2 b3 = ()

(* The interactive mode doesn't seem to be registering large preconditions *)
type precond1 (cs:circGCState) (bit:int) (init:state) =
  (not (Set.mem bit (vals cs.symtab))) /\
  (not (Set.mem bit (elts cs.ah))) /\
  (disjoint (vals cs.symtab) (elts cs.ah)) /\
  (disjoint (vars (lookup cs.cvals bit)) (elts cs.ah)) /\
  (zeroHeap (evalCirc cs.gates init) cs.ah) /\
  (b2t(lookup cs.isanc bit) ==> lookup init bit = false) /\
  (evalBexp (BXor (BVar bit, (lookup cs.cvals bit))) (evalCirc cs.gates init) = lookup init bit) /\
  (forall bit. Set.mem bit (vals cs.symtab) ==> disjoint (vars (lookup cs.cvals bit)) (elts cs.ah))

(* This lemma is very slow interactively, may not pass *)
val garbage_value_lemma : cs:circGCState -> bit:int -> init:state -> cs':circGCState ->
  Lemma (requires (cs' = garbageCollect cs bit /\
                   precond1 cs bit init))
	(ensures  (forall bit'. Set.mem bit' (vals cs.symtab) ==>
		     (lookup (evalCirc cs.gates init) bit' = lookup (evalCirc cs'.gates init) bit' /\
		      evalBexp (lookup cs.cvals bit') (evalCirc cs.gates init) =
		      evalBexp (lookup cs'.cvals bit') (evalCirc cs'.gates init))))
let garbage_value_lemma cs bit init cs'=
  let cval = lookup cs.cvals bit in
  if Set.mem bit (vars cval) then () else
  let (ah', _, _, circ') = compileBexp cs.ah bit cval in
  let st  = evalCirc cs.gates init in
  let st' = evalCirc cs'.gates init in
  let bexp' = if lookup cs.isanc bit then cval else (BXor (BVar bit, cval)) in
  compile_decreases_heap cs.ah bit cval;
  compile_mods cs.ah bit cval;
  eval_mod st circ';
  disjoint_subset (elts ah') (elts cs.ah) (vals cs.symtab);
  disjoint_is_subset_compl (vals cs.symtab) (mods circ');
  agree_on_subset st st' (complement (mods circ')) (vals cs.symtab);
  //---------------------------------------------------------------
  //forall bit'. Set.mem bit' (vals cs.symtab) ==> 
  //  lookup st bit' = lookup st' bit');
  //---------------------------------------------------------------
  compile_bexp_correct cs.ah bit cval st;
  eval_state_swap cval st st';
  xor_assoc (lookup st bit) (evalBexp cval st) (evalBexp cval st);
  xor_inverse (evalBexp cval st);
  //---------------------------------------------------------------
  //b2t(lookup st bit = evalBexp bexp' st'));
  //---------------------------------------------------------------
  compile_mods cs.ah bit cval;
  cvals_agree_lemma cs.symtab cs.cvals bit bexp' st circ';
  cvals_update_lemma cs.symtab cs.cvals bit bexp' st st'
  //---------------------------------------------------------------
  //forall bit'. Set.mem bit' (vals cs.symtab) ==> 
  //  evalBexp (lookup cs.cvals bit') st = evalBexp (lookup cs'.cvals bit') st');

type precond3 (cs:circGCState) (l:int) (bexp:boolExp) (init:state) =
  (forall l'. not (l' = l) ==> not (lookup cs.symtab l = lookup cs.symtab l')) /\
  (disjoint (vals cs.symtab) (elts cs.ah)) /\
  (zeroHeap init cs.ah) /\
  (zeroHeap (evalCirc cs.gates init) cs.ah) /\
  (forall bit. Set.mem bit (vals cs.symtab) ==>
    (disjoint (vars (lookup cs.cvals bit)) (elts cs.ah))) /\
  (forall bit. Set.mem bit (vals cs.symtab) ==>
     (b2t(lookup cs.isanc bit) ==> lookup init bit = false)) /\
  (forall bit. Set.mem bit (vals cs.symtab) ==>
     (evalBexp (BXor (BVar bit, (lookup cs.cvals bit))) (evalCirc cs.gates init) = lookup init bit))

val assign_value_lemma : cs:circGCState -> l:int -> bexp:boolExp -> init:state -> cs':circGCState ->
  Lemma (requires (cs' = circGCAssign cs l bexp /\
                   precond3 cs l bexp init))
	(ensures  ((lookup (evalCirc cs'.gates init) (lookup cs'.symtab l) = 
		    evalBexp (substVar bexp cs.symtab) (evalCirc cs.gates init)) /\
		   (forall bit. (not (bit = lookup cs.symtab l) /\ Set.mem bit (vals cs.symtab)) ==>
	              lookup (evalCirc cs'.gates init) bit = lookup (evalCirc cs.gates init) bit) /\
	           (forall bit. Set.mem bit (vals cs'.symtab) ==>
		      b2t(lookup cs'.isanc bit) ==> lookup init bit = false) /\
		   (forall bit. Set.mem bit (vals cs'.symtab) ==>
		      evalBexp (BXor (BVar bit, lookup cs'.cvals bit)) (evalCirc cs'.gates init) = 
		       lookup init bit)))
let assign_value_lemma cs l bexp init cs' =
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  match (lookup cs.cvals bit, factorAs bexp' bit, lookup cs.isanc bit) with
    | (BFalse, _, true)      ->
      let bexp'' = substOneVar bexp' bit BFalse in
      let f bexp = substOneVar bexp bit BFalse in
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
        // Correctness of output
	lookup_is_val cs.symtab l;
	substVar_elems bexp cs.symtab;
	substOneVar_elems bexp' bit BFalse;
	disjoint_subset (vars bexp'') (rem bit (vals cs.symtab)) (ins bit (elts cs.ah));
	compile_bexp_correct cs.ah bit bexp'' (evalCirc cs.gates init);
	subst_value_pres bexp' bit BFalse (evalCirc cs.gates init) (evalCirc cs.gates init);
	assert(b2t(lookup (evalCirc cs'.gates init) bit = 
		 evalBexp (substVar bexp cs.symtab) (evalCirc cs.gates init)));
        // Preservation of other values
	compile_mods cs.ah bit bexp'';
        disjoint_subset (mods circ') (ins bit (elts cs.ah)) (rem bit (vals cs.symtab));
        disjoint_is_subset_compl (rem bit (vals cs.symtab)) (mods circ');
	eval_mod (evalCirc cs.gates init) circ';
        agree_on_subset (evalCirc cs.gates init) 
	                (evalCirc cs'.gates init) 
	                (complement (mods circ')) 
	                (rem bit (vals cs.symtab));
	assert(forall bit. (not (bit = lookup cs.symtab l) /\ Set.mem bit (vals cs.symtab)) ==>
	         lookup (evalCirc cs'.gates init) bit = lookup (evalCirc cs.gates init) bit);
	// Correctness of isanc
	assert(forall bit. Set.mem bit (vals cs'.symtab) ==>
		 b2t(lookup cs'.isanc bit) ==> lookup init bit = false);
	// Correctness of cvals
	lookup_is_val cs.symtab l;
        compile_mods cs.ah bit bexp'';
	cvals_lemma cs.symtab cs.cvals bit BFalse (evalCirc cs.gates init) circ';
        disjoint_is_subset_compl (vars bexp'') (mods circ');
        agree_on_subset (evalCirc cs.gates init) 
	                (evalCirc cs'.gates init) 
	                (complement (mods circ')) 
	                (vars bexp'');
	eval_state_swap bexp'' (evalCirc cs.gates init) (evalCirc cs'.gates init);
        xor_inverse (evalBexp bexp'' (evalCirc cs.gates init));
	assert(forall bit'. Set.mem bit' (vals cs'.symtab) ==>
	         evalBexp (BXor (BVar bit', lookup cs'.cvals bit')) (evalCirc cs'.gates init) = 
		   lookup init bit');
        ()
    | (_, Some bexp'', _) ->
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit (BXor (BVar bit, bexp'')) in
        // Correctness of output
	lookup_is_val cs.symtab l;
	substVar_elems bexp cs.symtab;
	factorAs_vars bexp' bit;
	disjoint_subset (vars bexp'') (rem bit (vals cs.symtab)) (ins bit (elts cs.ah));
	compile_bexp_correct cs.ah bit bexp'' (evalCirc cs.gates init);
	factorAs_correct bexp' bit (evalCirc cs.gates init);
	assert(b2t(lookup (evalCirc cs'.gates init) bit = 
		 evalBexp (substVar bexp cs.symtab) (evalCirc cs.gates init)));
        // Preservation of other values
	compile_mods cs.ah bit bexp'';
        disjoint_subset (mods circ') (ins bit (elts cs.ah)) (rem bit (vals cs.symtab));
        disjoint_is_subset_compl (rem bit (vals cs.symtab)) (mods circ');
	eval_mod (evalCirc cs.gates init) circ';
        agree_on_subset (evalCirc cs.gates init) 
	                (evalCirc cs'.gates init) 
	                (complement (mods circ')) 
	                (rem bit (vals cs.symtab));
	assert(forall bit. (not (bit = lookup cs.symtab l) /\ Set.mem bit (vals cs.symtab)) ==>
	         lookup (evalCirc cs'.gates init) bit = lookup (evalCirc cs.gates init) bit);
	// Correctness of isanc
	assert(forall bit. Set.mem bit (vals cs'.symtab) ==>
		 b2t(lookup cs'.isanc bit) ==> lookup init bit = false);
	// Correctness of cvals
        disjoint_is_subset_compl (vars bexp'') (mods circ');
        agree_on_subset (evalCirc cs.gates init) 
	                (evalCirc cs'.gates init) 
	                (complement (mods circ')) 
	                (vars bexp'');
	eval_state_swap bexp'' (evalCirc cs.gates init) (evalCirc cs'.gates init);
        xor_assoc (lookup (evalCirc cs.gates init) bit) 
	          (evalBexp bexp'' (evalCirc cs.gates init))
		  (evalBexp bexp'' (evalCirc cs.gates init));
        xor_inverse (evalBexp bexp'' (evalCirc cs.gates init));
	cvals_lemma cs.symtab cs.cvals bit (BXor (BVar bit, bexp'')) (evalCirc cs.gates init) circ';
	assert(forall bit'. Set.mem bit' (vals cs'.symtab) ==>
	         evalBexp (BXor (BVar bit', lookup cs'.cvals bit')) (evalCirc cs'.gates init) = 
		   lookup init bit');
	()
    | _                ->
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ') = compileBexp ah' bit' bexp' in
      let cs'' = 
	{ top    = cs.top; 
	  ah     = ah''; 
	  gates  = cs.gates @ circ'; 
	  symtab = update cs.symtab l bit';
	  isanc  = update cs.isanc bit' true;
	  cvals  = update cs.cvals bit' bexp' } 
      in
      lookup_is_val cs.symtab l;
      substVar_elems bexp cs.symtab;
      pop_proper_subset cs.ah;
      pop_elt cs.ah;
      compile_bexp_correct ah' bit' bexp' (evalCirc cs.gates init);
      compile_decreases_heap ah' bit' bexp';
      compile_bexp_zero ah' bit' bexp' (evalCirc cs.gates init);
      lookup_converse2 cs''.symtab bit;
      lookup_subset cs.symtab l bit';
      lookup_is_val cs.cvals bit;
      compile_mods ah' bit' bexp';
      eval_mod (evalCirc cs.gates init) circ';
      agree_on_subset (evalCirc cs.gates init) 
	              (evalCirc cs''.gates init) 
	              (complement (mods circ')) 
	              (ins bit (vars (lookup cs.cvals bit)));
      eval_state_swap (BXor (BVar bit, (lookup cs.cvals bit))) 
                      (evalCirc cs.gates init) 
		      (evalCirc cs''.gates init);
      assert(precond1 cs'' bit init);
      garbage_value_lemma cs'' bit init cs';
      // Correctness of output
	lookup_is_valF cs''.symtab;
	assert(b2t(lookup (evalCirc cs'.gates init) bit' = 
	    evalBexp (substVar bexp cs.symtab) (evalCirc cs.gates init)));
      // Preservation of other values
	update_subset cs.symtab l bit';
	assert(forall bit. (not (bit = lookup cs.symtab l) /\ Set.mem bit (vals cs.symtab)) ==>
	    lookup (evalCirc cs'.gates init) bit = lookup (evalCirc cs.gates init) bit);
      // Correctness of isanc
        pop_is_zero init cs.ah;
	assert(forall bit. Set.mem bit (vals cs'.symtab) ==>
	    b2t(lookup cs'.isanc bit) ==> lookup init bit = false);
      // Correctness of cvals
        xor_inverse (evalBexp bexp' (evalCirc cs.gates init));
	eval_state_swap bexp' (evalCirc cs.gates init) (evalCirc cs''.gates init);
	cvals_pres_lemma cs.symtab cs.cvals bit' (evalCirc cs.gates init) circ';
	assert(forall bit'. Set.mem bit' (vals cs'.symtab) ==>
		    evalBexp (BXor (BVar bit', lookup cs'.cvals bit')) (evalCirc cs'.gates init) = 
		    lookup init bit');
      ()

(* Fixpoint of the above preconditions w.r.t. garbagecollection, alloc and assign *)
type valid_GC_state (cs:circGCState) (init:state) =
  (forall l l'. not (l = l') ==> not (lookup cs.symtab l = lookup cs.symtab l')) /\
  (disjoint (vals cs.symtab) (elts cs.ah)) /\
  (zeroHeap init cs.ah) /\
  (zeroHeap (evalCirc cs.gates init) cs.ah) /\
  (forall bit. Set.mem bit (vals cs.symtab) ==>
    (disjoint (vars (lookup cs.cvals bit)) (elts cs.ah))) /\
  (forall bit. Set.mem bit (vals cs.symtab) ==>
    (b2t(lookup cs.isanc bit) ==> lookup init bit = false)) /\
  (forall bit. Set.mem bit (vals cs.symtab) ==>
    (evalBexp (BXor (BVar bit, (lookup cs.cvals bit))) (evalCirc cs.gates init) = lookup init bit))

val garbageCollect_pres_valid : cs:circGCState -> bit:int -> init:state ->
  Lemma (requires ((valid_GC_state cs init) /\
                   (not (Set.mem bit (vals cs.symtab))) /\
                   (not (Set.mem bit (elts cs.ah))) /\
                   (disjoint (vars (lookup cs.cvals bit)) (elts cs.ah)) /\
                   (b2t(lookup cs.isanc bit) ==> lookup init bit = false) /\
                   (evalBexp (BXor (BVar bit, (lookup cs.cvals bit))) (evalCirc cs.gates init) = 
		     lookup init bit)))
	(ensures  (valid_GC_state (garbageCollect cs bit) init))
let garbageCollect_pres_valid cs bit init =
  let cs' = garbageCollect cs bit in
  garbage_partition_lemma cs bit cs';
  garbage_zeroHeap_lemma cs bit init cs';
  garbage_value_lemma cs bit init cs'

(* For whatever reason this lemma needs to be separate *)
val minor_lemma1 : m1:Total.t int int -> m2:Total.t int int -> loc:int ->
  Lemma (requires (not (Set.mem (lookup m2 loc) (vals m1)) /\
                  (forall l l'. not (l = l') ==> not (lookup m1 l = lookup m1 l')) /\
                  (forall l. not (l = loc) ==> lookup m1 l = lookup m2 l)))
        (ensures  (forall l l'. not (l = l') ==> not (lookup m2 l = lookup m2 l')))
let minor_lemma1 m1 m2 loc = lookup_converse m1 (lookup m2 loc)

val alloc_pres_valid : cs:circGCState -> init:state ->
  Lemma (requires (valid_GC_state cs init))
	(ensures  (valid_GC_state (snd (circGCAlloc cs)) init))
let alloc_pres_valid cs init =
  let (ah', bit) = popMin cs.ah in
  let (loc, cs') = circGCAlloc cs in
  pop_proper_subset cs.ah;
  pop_is_zero init cs.ah;
  pop_is_zero (evalCirc cs.gates init) cs.ah;
  lookup_subset cs.symtab cs.top bit;
  minor_lemma1 cs.symtab cs'.symtab loc

val assign_pres_valid : cs:circGCState -> l:int -> bexp:boolExp -> init:state ->
  Lemma (requires (valid_GC_state cs init))
	(ensures  (valid_GC_state (circGCAssign cs l bexp) init))
let assign_pres_valid cs l bexp init =
  let cs' = circGCAssign cs l bexp in
  assign_partition_lemma cs l bexp cs';
  assign_zeroHeap_lemma cs l bexp init cs';
  assign_value_lemma cs l bexp init cs';
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  match (lookup cs.cvals bit, factorAs bexp' bit, lookup cs.isanc bit) with
    | (BFalse, _, true)      -> ()
    | (_, Some bexp'', _) -> ()
    | _ ->
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ') = compileBexp ah' bit' bexp' in
      let cs'' = 
        { top    = cs.top; 
          ah     = ah''; 
          gates  = cs.gates @ circ'; 
	  symtab = update cs.symtab l bit'; 
	  isanc  = update cs.isanc bit' true; 
	  cvals  = update cs.cvals bit' bexp' } 
      in
        pop_proper_subset cs.ah;
	pop_elt cs.ah;
        pop_is_zero init cs.ah;
        pop_is_zero (evalCirc cs.gates init) cs.ah;
        lookup_subset cs.symtab cs.top bit;
        minor_lemma1 cs.symtab cs''.symtab l

(* (external) Correctness properties *)
type equiv_state (cs:circGCState) (bs:boolState) (init:state) =
  cs.top = fst bs /\ (forall i. circGCEval cs init i = boolEval bs init i)

val garbageCollect_pres_equiv : cs:circGCState -> bs:boolState -> bit:int -> init:state ->
  Lemma (requires ((equiv_state cs bs init) /\
                   (precond1 cs bit init)))
	(ensures  (equiv_state (garbageCollect cs bit) bs init))
let garbageCollect_pres_equiv cs bs bit init =
  let cs' = garbageCollect cs bit in
  garbage_value_lemma cs bit init cs';
  lookup_is_valF cs.symtab

val alloc_pres_equiv : cs:circGCState -> bs:boolState -> init:state ->
  Lemma (requires (valid_GC_state cs init /\ equiv_state cs bs init))
	(ensures  (valid_GC_state (snd (circGCAlloc cs)) init /\
	           equiv_state (snd (circGCAlloc cs)) (snd (boolAlloc bs)) init))
let alloc_pres_equiv cs bs init =
  let (l, cs') = circGCAlloc cs in
  let (k, bs') = boolAlloc bs in
  pop_proper_subset cs.ah;
  pop_elt cs.ah;
  pop_is_zero init cs.ah;
  pop_is_zero (evalCirc cs.gates init) cs.ah;
  alloc_pres_valid cs init;
  lookup_is_valF cs.symtab

val assign_pres_equiv : cs:circGCState -> bs:boolState -> l:int -> bexp:boolExp -> init:state ->
  Lemma (requires (valid_GC_state cs init /\ equiv_state cs bs init))
	(ensures  (valid_GC_state (circGCAssign cs l bexp) init /\
	           equiv_state (circGCAssign cs l bexp) (boolAssign bs l bexp) init))
let assign_pres_equiv cs bs l bexp init =
  let cs' = circGCAssign cs l bexp in
  let bs' = boolAssign bs l bexp in
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  match (lookup cs.cvals bit, factorAs bexp' bit, lookup cs.isanc bit) with
    | (BFalse, _, true)   ->
	assign_value_lemma cs l bexp init cs';
	assign_pres_valid cs l bexp init;
	lookup_is_valF cs.symtab;
	substVar_value_pres bexp cs.symtab (snd bs) (evalCirc cs.gates init)
    | (_, Some bexp'', _) ->
	assign_value_lemma cs l bexp init cs';
	assign_pres_valid cs l bexp init;
	lookup_is_valF cs.symtab;
	substVar_value_pres bexp cs.symtab (snd bs) (evalCirc cs.gates init)
    | _ ->
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ') = compileBexp ah' bit' bexp' in
      let cs'' = 
        { top    = cs.top; 
          ah     = ah''; 
          gates  = cs.gates @ circ'; 
	  symtab = update cs.symtab l bit'; 
	  isanc  = update cs.isanc bit' true; 
	  cvals  = update cs.cvals bit' bexp' } 
      in
	assign_pres_valid cs l bexp init;
	lookup_is_val cs.symtab l;
	substVar_elems bexp cs.symtab;
	pop_proper_subset cs.ah;
	pop_elt cs.ah;
	compile_bexp_correct ah' bit' bexp' (evalCirc cs.gates init);
	compile_decreases_heap ah' bit' bexp';
	compile_bexp_zero ah' bit' bexp' (evalCirc cs.gates init);
	lookup_converse2 cs''.symtab bit;
	lookup_subset cs.symtab l bit';
	lookup_is_val cs.cvals bit;
	compile_mods ah' bit' bexp';
	eval_mod (evalCirc cs.gates init) circ';
	agree_on_subset (evalCirc cs.gates init) 
			(evalCirc cs''.gates init) 
			(complement (mods circ')) 
			(ins bit (vars (lookup cs.cvals bit)));
	eval_state_swap (BXor (BVar bit, (lookup cs.cvals bit))) 
			(evalCirc cs.gates init) 
			(evalCirc cs''.gates init);
	assert(precond1 cs'' bit init);
	lookup_is_valF cs.symtab;
	substVar_value_pres bexp cs.symtab (snd bs) (evalCirc cs.gates init);
        assert(equiv_state cs'' bs' init);
        garbageCollect_pres_equiv cs'' bs' bit init

// Copy-pasted from Compiler mostly...
// Huge impact on verification
irreducible type p_gc (cs:circGCState) (bs:boolState) (init:state) = 
  valid_GC_state cs init /\ equiv_state cs bs init

(* NOTE: p_circ needs to be irreducible for step_pres_equiv to be provable (given reasonable
   resource limitations), but then assign_pres_equiv is unprovable. How can we solve this
   mess? Can't seem to find any sort of local type checker commands so for now the only
   solution is to assume the existence of this lemma. *)
val expand_p : cs:circGCState -> bs:boolState -> init:state ->
  Lemma (requires True)
        (ensures (p_gc cs bs init <==> valid_GC_state cs init /\ equiv_state cs bs init))
  //[SMTPat (p_circ cs bs init)]
let expand_p cs bs init = admit()

val step_pres_equiv : cs:circGCState -> bs:boolState -> gexp:gExpr -> init:state ->
  Lemma (requires (p_gc cs bs init))
        (ensures  ((is_Err (step (gexp, cs) circGCInterp) /\ is_Err (step (gexp, bs) boolInterp)) \/
                   (is_Val (step (gexp, cs) circGCInterp) /\ is_Val (step (gexp, bs) boolInterp) /\
		    p_gc (snd (getVal (step (gexp, cs) circGCInterp))) 
		         (snd (getVal (step (gexp, bs) boolInterp)))
			 init)))
  (decreases %[gexp;1])
val step_lst_pres_equiv : cs:circGCState -> bs:boolState -> lst:list gExpr -> init:state ->
  Lemma (requires (p_gc cs bs init))
        (ensures  ((is_Err (step_lst (lst, cs) circGCInterp) /\ is_Err (step_lst (lst, bs) boolInterp)) \/
                   (is_Val (step_lst (lst, cs) circGCInterp) /\ is_Val (step_lst (lst, bs) boolInterp) /\
		    p_gc (snd (getVal (step_lst (lst, cs) circGCInterp))) 
		         (snd (getVal (step_lst (lst, bs) boolInterp)))
			 init)))
  (decreases %[lst;0])
let rec step_pres_equiv cs bs gexp init = match gexp with
  | LET (x, t1, t2) -> step_pres_equiv cs bs t1 init
  | APPLY (t1, t2) ->
    step_pres_equiv cs bs t1 init;
    step_pres_equiv cs bs t2 init
  | SEQUENCE (t1, t2) ->
    step_pres_equiv cs bs t1 init;
    step_pres_equiv cs bs t2 init
  | ASSIGN (t1, t2) ->
    step_pres_equiv cs bs t1 init;
    step_pres_equiv cs bs t2 init;
    if (isVal t1 && isBexp t2) then
      begin match t1 with
        | LOC l -> 
	  expand_p cs bs init;
	  assign_pres_equiv cs bs l (get_bexp t2) init;
	  expand_p (snd (getVal (step (gexp, cs) circGCInterp))) (snd (getVal (step (gexp, bs) boolInterp))) init
        | _ -> ()
      end 
  | XOR (t1, t2) ->
    step_pres_equiv cs bs t1 init;
    step_pres_equiv cs bs t2 init
  | AND (t1, t2) ->
    step_pres_equiv cs bs t1 init;
    step_pres_equiv cs bs t2 init
  | BOOL b -> ()
  | APPEND (t1, t2) ->
    step_pres_equiv cs bs t1 init;
    step_pres_equiv cs bs t2 init
  | ROT (i, t) ->
    step_pres_equiv cs bs t init
  | SLICE (t, i, j) ->
    step_pres_equiv cs bs t init
  | ARRAY lst -> 
    admit() // See note in Interpreter.fst, mutual recursion here no longer works due to new equality types
    //step_lst_pres_equiv cs bs lst init
  | GET_ARRAY (t, i) ->
    step_pres_equiv cs bs t init
  | ASSERT t ->
    step_pres_equiv cs bs t init
  | BEXP bexp ->
    let (l, cs') = circGCAlloc cs in
    let (l', bs') = boolAlloc bs in
      expand_p cs bs init;
      alloc_pres_equiv cs bs init;
      assign_pres_equiv cs' bs' l (BXor (BVar l, bexp)) init;
      expand_p (snd (getVal (step (gexp, cs) circGCInterp))) (snd (getVal (step (gexp, bs) boolInterp))) init
  | _ -> ()
and step_lst_pres_equiv cs bs lst init = match lst with
  | [] -> ()
  | x::xs -> admit() // Mutual recursion again
    //step_pres_equiv cs bs x init
    //step_lst_pres_equiv cs bs xs init
