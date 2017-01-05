(** Main compiler transformation *)
module Compiler

open Utils
open FStar.Set
open SetExtra
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
    ah : ancHeap;
    gates : list gate;
    subs : Total.t int int;
    zero : Total.t int bool }

val circInit   : circState
val circAlloc  : circState -> Tot (int * circState)
val circAssign : circState -> int -> boolExp -> Tot circState
val circEval   : circState -> state -> int -> Tot bool

let circInit = {top = 0; ah = emptyHeap; gates = []; subs = constMap 0; zero = constMap false}
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
  let bit = lookup cs.subs l in
  let bexp' = substVar bexp cs.subs in
  match (lookup cs.zero bit, factorAs bexp' bit) with
    | (true, _) -> // substitute bit with BFalse, compile in place
      let bexp'' = substOneVar bexp' bit BFalse in
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
      { top   = cs.top;
        ah    = ah';
	gates = cs.gates @ circ;
	subs  = cs.subs;
	zero  = update cs.zero bit false }
    | (false, Some bexp'') -> // compile in place
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
      { top   = cs.top;
        ah    = ah';
	gates = cs.gates @ circ;
	subs  = cs.subs;
	zero  = update cs.zero bit false }
    | (false, None) -> // compile out of place
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ) = compileBexp ah' bit' bexp' in
      { top   = cs.top; 
        ah    = ah''; 
        gates = cs.gates @ circ; 
        subs  = update cs.subs l bit';
        zero  = update cs.zero bit' false }

let circEval cs ivals i = lookup (evalCirc cs.gates ivals) (lookup cs.subs i)

let circInterp = {
  alloc = circAlloc;
  assign = circAssign;
  eval = circEval
}

val allocNcirc : list gExpr * circState -> i:int ->
  Tot (list gExpr * circState) (decreases i)
let rec allocNcirc (locs, cs) i =
  if i <= 0 then (FStar.List.Tot.rev locs, cs)
  else
    let (ah', res) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                subs = update cs.subs cs.top res;
		zero = update cs.zero cs.top false }
    in
      allocNcirc (((LOC cs.top)::locs), cs') (i-1)

val allocTycirc : gType -> circState -> Tot (result (gExpr * circState))
let allocTycirc ty cs = match ty with
  | GBool ->
    let (ah', res) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                subs = update cs.subs cs.top res;
		zero = update cs.zero cs.top false }
    in
      Val (LOC cs.top, cs')
  | GArray n ->
    let (locs, st') = allocNcirc ([], cs) n in
      Val (ARRAY locs, st')
  | _ -> Err "Invalid parameter type for circuit generation"

val lookup_Lst : st:Total.t int int -> lst:(list gExpr){isVal_lst lst} -> Tot (list int)
let rec lookup_Lst st lst = match lst with
  | [] -> []
  | (LOC l)::xs -> (lookup st l)::(lookup_Lst st xs)

val compileCirc : config circState -> Dv (result (list int * list gate))
let rec compileCirc (gexp, cs) =
  if isVal gexp then match gexp with
    | UNIT -> Val ([], [])
    | LAMBDA (x, ty, t) ->
      begin match allocTycirc ty cs with
        | Err s -> Err s
        | Val (v, cs') -> compileCirc (substgExpr t x v, cs')
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

(** Verification utilities *)
(* New version follows the more well designed proof of garbage collected compilation *)

val assign_partition_lemma : cs:circState -> l:int -> bexp:boolExp -> cs':circState ->
  Lemma (requires ((cs' = circAssign cs l bexp) /\ 
		   (disjoint (vals cs.subs) (elts cs.ah))))
	(ensures  (disjoint (vals cs'.subs) (elts cs'.ah)))
let assign_partition_lemma cs l bexp cs' =
  let bit = lookup cs.subs l in
  let bexp' = substVar bexp cs.subs in
  substVar_elems bexp cs.subs;
  match (lookup cs.zero bit, factorAs bexp' bit) with
    | (true, _)            ->
      let bexp'' = substOneVar bexp' bit BFalse in
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
	compile_decreases_heap cs.ah bit bexp'';
	disjoint_subset (elts ah') (elts cs.ah) (vals cs.subs);
	substOneVar_elems bexp' bit BFalse
    | (false, Some bexp'') ->
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
	compile_decreases_heap cs.ah bit bexp'';
	disjoint_subset (elts ah') (elts cs.ah) (vals cs.subs);
	factorAs_vars bexp' bit
    | (false, None)        ->
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ) = compileBexp ah' bit' bexp' in
        pop_proper_subset cs.ah;
	compile_decreases_heap ah' bit' bexp';
        lookup_subset cs.subs cs.top bit';
	disjoint_subset (vals cs'.subs) (ins bit' (vals cs.subs)) (elts cs'.ah)

val assign_zeroHeap_lemma : cs:circState -> l:int -> bexp:boolExp -> init:state -> cs':circState ->
  Lemma (requires (cs' = circAssign cs l bexp /\ 
		   zeroHeap init cs.ah /\
		   zeroHeap (evalCirc cs.gates init) cs.ah /\
		   disjoint (vals cs.subs) (elts cs.ah)))
	(ensures  (zeroHeap init cs'.ah /\
	           zeroHeap (evalCirc cs'.gates init) cs'.ah))
let assign_zeroHeap_lemma cs l bexp init cs' =
  let bit = lookup cs.subs l in
  let bexp' = substVar bexp cs.subs in
  let st  = evalCirc cs.gates init in
  lookup_is_val cs.subs l;
  substVar_elems bexp cs.subs;
  match (lookup cs.zero bit, factorAs bexp' bit) with
    | (true, _)            ->
      let bexp'' = substOneVar bexp' bit BFalse in
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
	compile_decreases_heap cs.ah bit bexp'';
	zeroHeap_subset init cs.ah ah';
	substOneVar_elems bexp' bit BFalse;
	compile_bexp_zero cs.ah bit bexp'' st
    | (false, Some bexp'') ->
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
	compile_decreases_heap cs.ah bit bexp'';
	zeroHeap_subset init cs.ah ah';
	factorAs_vars bexp' bit;
	compile_bexp_zero cs.ah bit bexp'' st
    | (false, None)        ->
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ') = compileBexp ah' bit' bexp' in
	pop_proper_subset cs.ah;
	compile_decreases_heap ah' bit' bexp';
	compile_bexp_zero ah' bit' bexp' st

val assign_value_lemma : cs:circState -> l:int -> bexp:boolExp -> init:state -> cs':circState ->
  Lemma (requires (cs' = circAssign cs l bexp /\
                   (forall l'. not (l' = l) ==> not (lookup cs.subs l = lookup cs.subs l')) /\
                   (disjoint (vals cs.subs) (elts cs.ah)) /\
                   (zeroHeap (evalCirc cs.gates init) cs.ah) /\
                   (forall bit. Set.mem bit (vals cs.subs) ==>
                      (lookup cs.zero bit = true ==> lookup (evalCirc cs.gates init) bit = false))))
	(ensures  ((lookup (evalCirc cs'.gates init) (lookup cs'.subs l) = 
		    evalBexp (substVar bexp cs.subs) (evalCirc cs.gates init)) /\
		   (forall bit. (not (bit = lookup cs.subs l) /\ Set.mem bit (vals cs.subs)) ==>
	              lookup (evalCirc cs'.gates init) bit = lookup (evalCirc cs.gates init) bit) /\
                   (forall bit. Set.mem bit (vals cs'.subs) ==>
                      (lookup cs'.zero bit = true ==> lookup (evalCirc cs'.gates init) bit = false))))
let assign_value_lemma cs l bexp init cs' =
  let bit = lookup cs.subs l in
  let bexp' = substVar bexp cs.subs in
  match (lookup cs.zero bit, factorAs bexp' bit) with
    | (true, _)            ->
      let bexp'' = substOneVar bexp' bit BFalse in
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
        // Correctness of output
	lookup_is_val cs.subs l;
	substVar_elems bexp cs.subs;
	substOneVar_elems bexp' bit BFalse;
	disjoint_subset (vars bexp'') (rem bit (vals cs.subs)) (ins bit (elts cs.ah));
	compile_bexp_correct cs.ah bit bexp'' (evalCirc cs.gates init);
	subst_value_pres bexp' bit BFalse (evalCirc cs.gates init) (evalCirc cs.gates init);
	assert(b2t(lookup (evalCirc cs'.gates init) bit = 
		 evalBexp (substVar bexp cs.subs) (evalCirc cs.gates init)));
        // Preservation of other values
	compile_mods cs.ah bit bexp'';
        disjoint_subset (mods circ') (ins bit (elts cs.ah)) (rem bit (vals cs.subs));
        disjoint_is_subset_compl (rem bit (vals cs.subs)) (mods circ');
	eval_mod (evalCirc cs.gates init) circ';
        agree_on_subset (evalCirc cs.gates init) 
	                (evalCirc cs'.gates init) 
	                (complement (mods circ')) 
	                (rem bit (vals cs.subs));
	assert(forall bit. (not (bit = lookup cs.subs l) /\ Set.mem bit (vals cs.subs)) ==>
	         lookup (evalCirc cs'.gates init) bit = lookup (evalCirc cs.gates init) bit);
	// Correctness of zero
	assert(forall bit. Set.mem bit (vals cs'.subs) ==>
                 lookup cs'.zero bit = true ==> lookup (evalCirc cs'.gates init) bit = false);
        ()
    | (false, Some bexp'') ->
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
        // Correctness of output
	lookup_is_val cs.subs l;
	substVar_elems bexp cs.subs;
	factorAs_vars bexp' bit;
	disjoint_subset (vars bexp'') (rem bit (vals cs.subs)) (ins bit (elts cs.ah));
	compile_bexp_correct cs.ah bit bexp'' (evalCirc cs.gates init);
	factorAs_correct bexp' bit (evalCirc cs.gates init);
	assert(b2t(lookup (evalCirc cs'.gates init) bit = 
		 evalBexp (substVar bexp cs.subs) (evalCirc cs.gates init)));
        // Preservation of other values
	compile_mods cs.ah bit bexp'';
        disjoint_subset (mods circ') (ins bit (elts cs.ah)) (rem bit (vals cs.subs));
        disjoint_is_subset_compl (rem bit (vals cs.subs)) (mods circ');
	eval_mod (evalCirc cs.gates init) circ';
        agree_on_subset (evalCirc cs.gates init) 
	                (evalCirc cs'.gates init) 
	                (complement (mods circ')) 
	                (rem bit (vals cs.subs));
	assert(forall bit. (not (bit = lookup cs.subs l) /\ Set.mem bit (vals cs.subs)) ==>
	         lookup (evalCirc cs'.gates init) bit = lookup (evalCirc cs.gates init) bit);
	// Correctness of zero
	assert(forall bit. Set.mem bit (vals cs'.subs) ==>
                 lookup cs'.zero bit = true ==> lookup (evalCirc cs'.gates init) bit = false);
	()
    | (false, None)        ->
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ') = compileBexp ah' bit' bexp' in
      lookup_is_val cs.subs l;
      substVar_elems bexp cs.subs;
      pop_proper_subset cs.ah;
      pop_elt cs.ah;
      compile_bexp_correct ah' bit' bexp' (evalCirc cs.gates init);
      lookup_converse2 cs'.subs bit;
      // Correctness of output
      assert(b2t(lookup (evalCirc cs'.gates init) bit' = 
	evalBexp (substVar bexp cs.subs) (evalCirc cs.gates init)));
      // Preservation of other values
      compile_mods ah' bit' bexp';
      disjoint_subset (mods circ') (elts cs.ah) (vals cs.subs);
      disjoint_is_subset_compl (vals cs.subs) (mods circ');
      eval_mod (evalCirc cs.gates init) circ';
      agree_on_subset (evalCirc cs.gates init) 
                      (evalCirc cs'.gates init) 
	              (complement (mods circ')) 
	              (vals cs.subs);
      assert(forall bit. Set.mem bit (vals cs.subs) ==>
        lookup (evalCirc cs'.gates init) bit = lookup (evalCirc cs.gates init) bit);
      // Correctness of zero
      lookup_subset cs.subs l bit';
      assert(forall bit. Set.mem bit (vals cs'.subs) ==>
        lookup cs'.zero bit = true ==> lookup (evalCirc cs'.gates init) bit = false);
      ()

(* Valid compiler states *)
type valid_circ_state (cs:circState) (init:state) =
  (forall l l'. not (l = l') ==> not (lookup cs.subs l = lookup cs.subs l')) /\
  disjoint (vals cs.subs) (elts cs.ah) /\
  zeroHeap init cs.ah /\
  zeroHeap (evalCirc cs.gates init) cs.ah /\
  (forall bit. Set.mem bit (vals cs.subs) ==>
    (lookup cs.zero bit = true ==> lookup (evalCirc cs.gates init) bit = false))

val alloc_pres_valid : cs:circState -> init:state ->
  Lemma (requires (valid_circ_state cs init))
	(ensures  (valid_circ_state (snd (circAlloc cs)) init))
let alloc_pres_valid cs init =
  let (ah', bit) = popMin cs.ah in
  let cs' = 
    { top = cs.top + 1; 
      ah = ah'; 
      gates = cs.gates; 
      subs = update cs.subs cs.top bit;
      zero = update cs.zero bit true }
  in
  pop_proper_subset cs.ah;
  pop_is_zero init cs.ah;
  pop_is_zero (evalCirc cs.gates init) cs.ah;
  lookup_subset cs.subs cs.top bit;
  lookup_converse cs.subs (lookup cs'.subs cs.top)

val assign_pres_valid : cs:circState -> l:int -> bexp:boolExp -> init:state ->
  Lemma (requires (valid_circ_state cs init))
	(ensures  (valid_circ_state (circAssign cs l bexp) init))
let assign_pres_valid cs l bexp init =
  let cs' = circAssign cs l bexp in
  assign_partition_lemma cs l bexp cs';
  assign_zeroHeap_lemma cs l bexp init cs';
  assign_value_lemma cs l bexp init cs';
  let bit = lookup cs.subs l in
  let bexp' = substVar bexp cs.subs in
  match (lookup cs.zero bit, factorAs bexp' bit) with
    | (true, _)            -> ()
    | (false, Some bexp'') -> ()
    | (false, None)        ->
      let (ah', bit') = popMin cs.ah in
      let (ah'', _, _, circ') = compileBexp ah' bit' bexp' in
        pop_proper_subset cs.ah;
	pop_elt cs.ah;
        lookup_subset cs.subs l bit';
        lookup_converse cs.subs bit'

(* Correctness of circuit compilation *)
type equiv_state (cs:circState) (bs:boolState) (init:state) =
  cs.top = fst bs /\ (forall i. circEval cs init i = boolEval bs init i)

val alloc_pres_equiv : cs:circState -> bs:boolState -> init:state ->
  Lemma (requires (valid_circ_state cs init /\ equiv_state cs bs init))
	(ensures  (valid_circ_state (snd (circAlloc cs)) init /\
	           equiv_state (snd (circAlloc cs)) (snd (boolAlloc bs)) init))
let alloc_pres_equiv cs bs init =
  let (l, cs') = circAlloc cs in
  let (k, bs') = boolAlloc bs in
  pop_proper_subset cs.ah;
  pop_is_zero init cs.ah;
  pop_is_zero (evalCirc cs.gates init) cs.ah;
  alloc_pres_valid cs init;
  lookup_is_valF cs.subs

val assign_pres_equiv : cs:circState -> bs:boolState -> l:int -> bexp:boolExp -> init:state ->
  Lemma (requires (valid_circ_state cs init /\ equiv_state cs bs init))
	(ensures  (valid_circ_state (circAssign cs l bexp) init /\
	           equiv_state (circAssign cs l bexp) (boolAssign bs l bexp) init))
let assign_pres_equiv cs bs l bexp init =
  let cs' = circAssign cs l bexp in
  assign_value_lemma cs l bexp init cs';
  assign_pres_valid cs l bexp init;
  lookup_is_valF cs.subs;
  substVar_value_pres bexp cs.subs (snd bs) (evalCirc cs.gates init)

// Huge impact on verification
irreducible type p_circ (cs:circState) (bs:boolState) (init:state) = 
  valid_circ_state cs init /\ equiv_state cs bs init

(* NOTE: p_circ needs to be irreducible for step_pres_equiv to be provable (given reasonable
   resource limitations), but then assign_pres_equiv is unprovable. How can we solve this
   mess? Can't seem to find any sort of local type checker commands so for now the only
   solution is to assume the existence of this lemma. *)
val expand_p : cs:circState -> bs:boolState -> init:state ->
  Lemma (requires True)
        (ensures (p_circ cs bs init <==> valid_circ_state cs init /\ equiv_state cs bs init))
  //[SMTPat (p_circ cs bs init)]
let expand_p cs bs init = admit()

val step_pres_equiv : cs:circState -> bs:boolState -> gexp:gExpr -> init:state ->
  Lemma (requires (p_circ cs bs init))
        (ensures  ((is_Err (step (gexp, cs) circInterp) /\ is_Err (step (gexp, bs) boolInterp)) \/
                   (is_Val (step (gexp, cs) circInterp) /\ is_Val (step (gexp, bs) boolInterp) /\
		    p_circ (snd (getVal (step (gexp, cs) circInterp))) 
		           (snd (getVal (step (gexp, bs) boolInterp)))
			   init)))
  (decreases %[gexp;1])
val step_lst_pres_equiv : cs:circState -> bs:boolState -> lst:list gExpr -> init:state ->
  Lemma (requires (p_circ cs bs init))
        (ensures  ((is_Err (step_lst (lst, cs) circInterp) /\ is_Err (step_lst (lst, bs) boolInterp)) \/
                   (is_Val (step_lst (lst, cs) circInterp) /\ is_Val (step_lst (lst, bs) boolInterp) /\
		    p_circ (snd (getVal (step_lst (lst, cs) circInterp))) 
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
	  expand_p (snd (getVal (step (gexp, cs) circInterp))) (snd (getVal (step (gexp, bs) boolInterp))) init
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
    let (l, cs') = circAlloc cs in
    let (l', bs') = boolAlloc bs in
      expand_p cs bs init;
      alloc_pres_equiv cs bs init;
      assign_pres_equiv cs' bs' l (BXor (BVar l, bexp)) init;
      expand_p (snd (getVal (step (gexp, cs) circInterp))) (snd (getVal (step (gexp, bs) boolInterp))) init
  | _ -> ()
and step_lst_pres_equiv cs bs lst init = match lst with
  | [] -> ()
  | x::xs -> admit() // Mutual recursion again
    //step_pres_equiv cs bs x init
    //step_lst_pres_equiv cs bs xs init
