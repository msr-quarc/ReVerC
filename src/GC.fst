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
    isanc  : Total.t int bool;
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
	  isanc  = cs.isanc;
	  cvals  = cvals'}
    | (cval, Some bexp'') -> // compile in place, substitute q.id with q.id \oplus bexp''
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
      let f bexp = substOneVar bexp bit (BXor (BVar bit, bexp'')) in
      let cvals' = update (mapVals f cs.cvals) bit (BXor (cval, bexp'')) in
        { top    = cs.top; 
	  ah     = ah'; 
	  gates  = cs.gates @ circ'; 
	  symtab = cs.symtab;
	  isanc  = cs.isanc;
	  cvals  = cvals' }
    | _                -> // Compile out of place, clean q.id
      let (ah', bit', _, circ') = compileBexp_oop cs.ah bexp' in
      let symtab' = update cs.symtab l bit' in
      let isanc' = update cs.isanc bit' true in
      let cvals' = update cs.cvals bit' bexp' in
      let cs' = 
	{ top    = cs.top; 
	  ah     = ah'; 
	  gates  = cs.gates @ circ'; 
	  symtab = symtab';
	  isanc  = isanc';
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
		isanc = update cs.isanc bit false;
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
		isanc = update cs.isanc bit false;
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
(* Passing proofs are replaced with admit() to speed up interactive verification *)

(* More precisely tuned lemmas *)
val cvals_vars_lemma : symtab:Total.t int int -> cvals:Total.t int BoolExp ->
		       bit:int -> exp:BoolExp -> s:set int ->
  Lemma (requires (disjoint (vars exp) s /\ not (Set.mem bit (vars exp)) /\
		  (forall bit'. Set.mem bit' (vals symtab) ==> 
		    disjoint (vars (lookup cvals bit')) s)))
	(ensures  (forall bit'. Set.mem bit' (vals symtab) ==> 
		    disjoint (vars (substOneVar (lookup cvals bit') bit exp)) (ins bit s)))
let rec cvals_vars_lemma symtab cvals bit exp s = admit() (*match symtab.elts with
  | [] -> substOneVar_elems (lookup cvals symtab.dval) bit exp
  | x::xs -> admit();
    let symtab' = { elts = xs; dval = symtab.dval } in
      substOneVar_elems (lookup cvals (snd x)) bit exp; 
      cvals_vars_lemma symtab' cvals bit exp s*)

val cvals_vars_lemma2 : symtab:Total.t int int -> cvals:Total.t int BoolExp ->
		       bit:int -> exp:BoolExp -> s:set int ->
  Lemma (requires (disjoint (vars exp) s /\
		  (forall bit'. Set.mem bit' (vals symtab) ==> 
		    disjoint (vars (lookup cvals bit')) s)))
	(ensures  (forall bit'. Set.mem bit' (vals symtab) ==> 
		    disjoint (vars (substOneVar (lookup cvals bit') bit exp)) s))
let rec cvals_vars_lemma2 symtab cvals bit exp s = admit() (*match symtab.elts with
  | [] -> substOneVar_elems (lookup cvals symtab.dval) bit exp
  | x::xs -> admit();
    let symtab' = { elts = xs; dval = symtab.dval } in
      substOneVar_elems (lookup cvals (snd x)) bit exp; 
      cvals_vars_lemma2 symtab' cvals bit exp s*)

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
let garbage_partition_lemma cs bit cs' = admit() (*
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
          //admitP(disjoint (vals cs'.symtab) (elts cs'.ah));
          disjoint_subset (elts ah') (elts cs.ah) (vars cval);      // disjoint ah' (vars cval)
	  cvals_vars_lemma cs.symtab cs.cvals bit cval (elts ah')
          //admitP(forall bit. Set.mem bit (vals cs'.symtab) ==> 
	  //	      disjoint (vars (lookup cs'.cvals bit)) (elts cs'.ah))
      | false -> 
        let f bexp = substOneVar bexp bit (BXor (BVar bit, cval)) in
        let cvals' = mapVals f cs.cvals in
          compile_decreases_heap cs.ah bit cval;                    // subset ah' cs.ah
          disjoint_subset (elts ah') (elts cs.ah) (vals cs.symtab); // disjoint ah' (vals cs.symtab)
          //admitP(disjoint (vals cs'.symtab) (elts cs'.ah));
	  cvals_vars_lemma2 cs.symtab cs.cvals bit (BXor (BVar bit, cval)) (elts ah')
          //admitP(forall bit. Set.mem bit (vals cs'.symtab) ==> 
		//    disjoint (vars (lookup cs'.cvals bit)) (elts cs'.ah))*)

(* TODO: the admit here is an assumption that is currently not enforced It requires 
   that all active bits have exactly one pre-image, or locations are mapped to 
   separate bits. It's true, but would require too many changes at the moment to fix *)
val assign_partition_lemma : cs:circGCState -> l:int -> bexp:BoolExp -> cs':circGCState ->
  Lemma (requires (cs' = circGCAssign cs l bexp /\ 
		   disjoint (vals cs.symtab) (elts cs.ah) /\
		   (forall bit. Set.mem bit (vals cs.symtab) ==> 
		     disjoint (vars (lookup cs.cvals bit)) (elts cs.ah))))
	(ensures  (disjoint (vals cs'.symtab) (elts cs'.ah) /\
		   (forall bit. Set.mem bit (vals cs'.symtab) ==> 
		     disjoint (vars (lookup cs'.cvals bit)) (elts cs'.ah))))
let assign_partition_lemma cs l bexp cs' = admit() (*
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
	cvals_vars_lemma2 cs.symtab cs.cvals bit bexp'' (elts cs'.ah)
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
	cvals_vars_lemma2 cs.symtab cs.cvals bit (BXor (BVar bit, bexp'')) (elts cs'.ah)
	//admitP(forall bit. Set.mem bit (vals cs'.symtab) ==> 
	//	 subset (vars (lookup cs'.cvals bit)) (vals cs'.symtab))
    | _                ->
      let (ah', bit', _, circ') = compileBexp_oop cs.ah bexp' in
      let symtab' = update cs.symtab l bit' in
      let isanc' = update cs.isanc bit' true in
      let cvals' = update cs.cvals bit' bexp' in
      let cs'' = 
	{ top    = cs.top; 
	  ah     = ah'; 
	  gates  = cs.gates @ circ'; 
	  symtab = symtab';
	  isanc  = isanc';
	  cvals  = cvals' } 
      in
	compile_decreases_heap_oop cs.ah bexp';
	disjoint_subset (elts ah') (elts cs.ah) (vals cs.symtab); // disjoint cs.ah' (vals cs.symtab)
	compile_partition_oop cs.ah bexp';
	//admitP(disjoint (vals cs''.symtab) (elts cs''.ah));
	//admitP(forall bit. Set.mem bit (vals cs''.symtab) ==> 
	//	 subset (vars (lookup cs''.cvals bit)) (vals cs''.symtab));
	admitP(b2t(not (Set.mem bit (vals cs''.symtab))));
	lookup_is_val cs.symtab l;
	garbage_partition_lemma cs'' bit cs' *)

(* These lemmas establish zero-ness of the ancilla heap *)

val garbage_zeroHeap_lemma : cs:circGCState -> bit:int -> init:state -> cs':circGCState ->
  Lemma (requires ((cs' = garbageCollect cs bit) /\ 
		   (not (Set.mem bit (elts cs.ah))) /\
		   (disjoint (vars (lookup cs.cvals bit)) (elts cs.ah)) /\
		   (zeroHeap init cs.ah) /\
		   (zeroHeap (evalCirc cs.gates init) cs.ah) /\
		   (lookup cs.isanc bit ==> lookup init bit = false) /\
		   (evalBexp (BXor (BVar bit, (lookup cs.cvals bit))) (evalCirc cs.gates init) =
		      lookup init bit)))
	(ensures  (zeroHeap init cs'.ah /\
	           zeroHeap (evalCirc cs'.gates init) cs'.ah))
let garbage_zeroHeap_lemma cs bit init cs' = admit() (*
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
	compile_bexp_zero cs.ah bit cval (evalCirc cs.gates init) *)

val assign_zeroHeap_lemma : cs:circGCState -> l:int -> bexp:BoolExp -> init:state -> cs':circGCState ->
  Lemma (requires ((cs' = circGCAssign cs l bexp) /\ 
		   (zeroHeap init cs.ah) /\
		   (zeroHeap (evalCirc cs.gates init) cs.ah) /\
		   (disjoint (vals cs.symtab) (elts cs.ah)) /\
		   (forall bit. Set.mem bit (vals cs.symtab) ==> 
		     disjoint (vars (lookup cs.cvals bit)) (elts cs.ah)) /\
		   (forall bit. Set.mem bit (vals cs.symtab) ==>
		     lookup cs.isanc bit ==> lookup init bit = false) /\
		   (forall bit. Set.mem bit (vals cs.symtab) ==>
		     evalBexp (BXor (BVar bit, (lookup cs.cvals bit))) (evalCirc cs.gates init) =
		     lookup init bit)))
	(ensures  (zeroHeap init cs'.ah /\
	           zeroHeap (evalCirc cs'.gates init) cs'.ah))
let assign_zeroHeap_lemma cs l bexp init cs' = admit() (*
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  let bexpfac = factorAs bexp' bit in
  let st  = evalCirc cs.gates init in
  lookup_is_val cs.symtab l;
  substVar_elems bexp cs.symtab;
  match (lookup cs.cvals bit, bexpfac) with
    | (BFalse, _)      ->
      let bexp'' = substOneVar bexp' bit BFalse in
      let (ah', _, _, circ) = compileBexp cs.ah bit bexp'' in
	compile_decreases_heap cs.ah bit bexp'';
	zeroHeap_subset init cs.ah ah';
	substOneVar_elems bexp' bit BFalse;
	compile_bexp_zero cs.ah bit bexp'' st
    | (_, Some bexp'') ->
      let (ah', _, _, circ') = compileBexp cs.ah bit bexp'' in
	compile_decreases_heap cs.ah bit bexp'';
	zeroHeap_subset init cs.ah ah';
	factorAs_vars bexp' bit;
	compile_bexp_zero cs.ah bit bexp'' st
    | _                -> 
      let (ah', bit', _, circ') = compileBexp_oop cs.ah bexp' in
      let cs'' = 
	{ top    = cs.top; 
	  ah     = ah'; 
	  gates  = cs.gates @ circ'; 
	  symtab = update cs.symtab l bit';
	  isanc  = update cs.isanc bit' true;
	  cvals  = update cs.cvals bit' bexp' } 
      in
      let st' = evalCirc cs''.gates init in
	compile_decreases_heap_oop cs.ah bexp';
	zeroHeap_subset init cs.ah ah';
	compile_bexp_zero_oop cs.ah bexp' st;
	compile_mods_oop cs.ah bexp';
	eval_mod st circ';
	disjoint_is_subset_compl (vars (BXor (BVar bit, lookup cs.cvals bit))) (complement (mods circ'));
	agree_on_subset st st' (complement (mods circ')) (vars (BXor (BVar bit, lookup cs.cvals bit)));
	eval_state_swap (BXor (BVar bit, lookup cs.cvals bit)) st st';
	garbage_zeroHeap_lemma cs'' bit init cs' *)

(* (internal) Correctness properties *)
val cvals_update_lemma : symtab:Total.t int int -> cvals:Total.t int BoolExp -> 
		         bit:int -> exp:BoolExp -> st:state -> st':state ->
  Lemma (requires (lookup st bit = evalBexp exp st' /\ 
                  (forall bit'. Set.mem bit' (vals symtab) ==> 
		     agree_on st st' (rem bit (vars (lookup cvals bit'))))))
	(ensures  (forall bit'. Set.mem bit' (vals symtab) ==> 
		     evalBexp (lookup cvals bit') st = 
		     evalBexp (substOneVar (lookup cvals bit') bit exp) st'))
  (decreases (symtab.elts))
let rec cvals_update_lemma symtab cvals bit exp st st' = admit() (*match symtab.elts with
  | [] -> subst_value_pres (lookup cvals symtab.dval) bit exp st st'
  | x::xs -> 
    let symtab' = { elts = xs; dval = symtab.dval } in
      subst_value_pres (lookup cvals (snd x)) bit exp st st'; 
      cvals_update_lemma symtab' cvals bit exp st st'*)

val cvals_agree_lemma : symtab:Total.t int int -> cvals:Total.t int BoolExp -> 
		         bit:int -> exp:BoolExp -> st:state -> circ:Circuit ->
  Lemma (requires (forall bit'. Set.mem bit' (vals symtab) ==> 
		     disjoint (rem bit (vars (lookup cvals bit'))) (mods circ)))
	(ensures  (forall bit'. Set.mem bit' (vals symtab) ==> 
		     agree_on st (evalCirc circ st) (rem bit (vars (lookup cvals bit')))))
  (decreases (symtab.elts))
let rec cvals_agree_lemma symtab cvals bit exp st st' = admit() (*match symtab.elts with
  | [] -> subst_value_pres (lookup cvals symtab.dval) bit exp st st'
  | x::xs -> 
    let symtab' = { elts = xs; dval = symtab.dval } in
      subst_value_pres (lookup cvals (snd x)) bit exp st st'; 
      cvals_update_lemma symtab' cvals bit exp st st'*)

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
  (lookup cs.isanc bit ==> lookup init bit = false) /\
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
let garbage_value_lemma cs bit init cs'= admit() (*
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
  //admitP(forall bit'. Set.mem bit' (vals cs.symtab) ==> 
  //  lookup st bit' = lookup st' bit');
  compile_bexp_correct cs.ah bit cval st;
  eval_state_swap cval st st';
  xor_assoc (lookup st bit) (evalBexp cval st) (evalBexp cval st);
  xor_inverse (evalBexp cval st);
  //admitP(b2t(lookup st bit = evalBexp bexp' st'));
  compile_mods cs.ah bit cval;
  cvals_agree_lemma cs.symtab cs.cvals bit bexp' st circ';
  cvals_update_lemma cs.symtab cs.cvals bit bexp' st st'
  //admitP(forall bit'. Set.mem bit' (vals cs.symtab) ==> 
  //  evalBexp (lookup cs.cvals bit') st = evalBexp (lookup cs'.cvals bit') st');*)

type precond3 (cs:circGCState) (l:int) (bexp:BoolExp) (init:state) =
  forall l'. not (l' = l) ==> not (lookup cs.symtab l = lookup cs.symtab l')
  
val assign_value_lemma : cs:circGCState -> l:int -> bexp:BoolExp -> init:state -> cs':circGCState ->
  Lemma (requires (cs' = circGCAssign cs l bexp /\
                   precond3 cs l bexp init))
	(ensures  ((lookup (evalCirc cs'.gates init) (lookup cs'.symtab l) = 
		    evalBexp (substVar bexp cs.symtab) (evalCirc cs.gates init)) /\
		   (forall bit. (not (bit = lookup cs.symtab l) /\ Set.mem bit (vals cs.symtab)) ==>
	              lookup (evalCirc cs'.gates init) bit = lookup (evalCirc cs.gates init) bit) /\
	           (forall bit. Set.mem bit (vals cs'.symtab) ==>
		     ((lookup cs'.isanc bit ==> lookup init bit = false) /\
		      evalBexp (BXor (BVar bit, lookup cs'.cvals bit)) (evalCirc cs'.gates init) = 
		       lookup init bit))))
let assign_value_lemma cs l bexp init cs' = admit()

(* Fixpoint of the above preconditions w.r.t. garbagecollection, alloc and assign *)
type valid_GC_state (cs:circGCState) (init:state) =
  (forall l l'. not (l = l') ==> not (lookup cs.symtab l = lookup cs.symtab l')) /\
  (disjoint (vals cs.symtab) (elts cs.ah)) /\
  (zeroHeap init cs.ah) /\
  (zeroHeap (evalCirc cs.gates init) cs.ah) /\
  (forall bit. Set.mem bit (vals cs.symtab) ==>
    ((disjoint (vars (lookup cs.cvals bit)) (elts cs.ah)) /\
     (lookup cs.isanc bit ==> lookup init bit = false) /\
     (evalBexp (BXor (BVar bit, (lookup cs.cvals bit))) (evalCirc cs.gates init) = lookup init bit)))

(*
  admitP(forall l l'. not (l = l') ==> not (lookup cs'.symtab l = lookup cs'.symtab l'));
  admitP(disjoint (vals cs'.symtab) (elts cs'.ah));
  admitP(zeroHeap init cs'.ah);
  admitP(zeroHeap (evalCirc cs'.gates init) cs'.ah);
  admitP(forall bit. Set.mem bit (vals cs'.symtab) ==>
    ((disjoint (vars (lookup cs'.cvals bit)) (elts cs'.ah)) /\
     (lookup cs'.isanc bit ==> lookup init bit = false) /\
     (evalBexp (BXor (BVar bit, (lookup cs'.cvals bit))) (evalCirc cs'.gates init) = lookup init bit)));
*)

val valid_implies_pre : cs:circGCState -> l:int -> init:state ->
  Lemma (requires (valid_GC_state cs init))
	(ensures  (precond1 cs (lookup cs.symtab l) init))
let valid_implies_pre cs l init = admit()

val garbageCollect_pres_valid : cs:circGCState -> bit:int -> init:state ->
  Lemma (requires ((valid_GC_state cs init) /\
                   (not (Set.mem bit (vals cs.symtab))) /\
                   (not (Set.mem bit (elts cs.ah))) /\
                   (disjoint (vars (lookup cs.cvals bit)) (elts cs.ah)) /\
                   (lookup cs.isanc bit ==> lookup init bit = false) /\
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
  let (loc, cs') = circGCAlloc cs in
  pop_proper_subset cs.ah;
  pop_is_zero init cs.ah;
  pop_is_zero (evalCirc cs.gates init) cs.ah;
  minor_lemma1 cs.symtab cs'.symtab loc

val assign_pres_valid : cs:circGCState -> l:int -> bexp:BoolExp -> init:state ->
  Lemma (requires (valid_GC_state cs init))
	(ensures  (valid_GC_state (circGCAssign cs l bexp) init))
let assign_pres_valid cs l bexp init =
  let cs' = circGCAssign cs l bexp in
  assign_partition_lemma cs l bexp cs';
  assign_zeroHeap_lemma cs l bexp init cs';
  assign_value_lemma cs l bexp init cs';
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  match (lookup cs.cvals bit, factorAs bexp' bit) with
    | (BFalse, _)      -> admit()
    | (_, Some bexp'') -> admit()
    | _ ->
      let (ah', bit', _, circ') = compileBexp_oop cs.ah bexp' in
      let cs'' = 
        { top    = cs.top; 
          ah     = ah'; 
          gates  = cs.gates @ circ'; 
	  symtab = update cs.symtab l bit'; 
	  isanc  = update cs.isanc bit' true; 
	  cvals  = update cs.cvals bit' bexp' } 
      in
        assert(not (bexp' = BVar bit));
        pop_proper_subset cs.ah;
	assert(Set.mem bit' (elts cs.ah));
	admit();
        pop_is_zero init cs.ah;
        pop_is_zero (evalCirc cs.gates init) cs.ah;
        minor_lemma1 cs.symtab cs''.symtab l;
	//admitP(forall l l'. not (l = l') ==> not (lookup cs'.symtab l = lookup cs'.symtab l'));
	admitP(forall bit. Set.mem bit (vals cs'.symtab) ==>
	  ((disjoint (vars (lookup cs'.cvals bit)) (elts cs'.ah)) /\
	   (lookup cs'.isanc bit ==> lookup init bit = false) /\
	   (evalBexp (BXor (BVar bit, (lookup cs'.cvals bit))) (evalCirc cs'.gates init) = lookup init bit)));
	()

(* (external) Correctness properties *)
type equiv_state (cs:circGCState) (bs:boolState) (init:state) =
  cs.top = fst bs /\ (forall i. circGCEval cs init i = boolEval bs init i)

val garbageCollect_pres_equiv : cs:circGCState -> bs:boolState -> bit:int -> init:state ->
  Lemma (requires (equiv_state cs bs init))
	(ensures  (equiv_state (garbageCollect cs bit) bs init))
let garbageCollect_pres_equiv cs bs bit init =
  let cs' = garbageCollect cs bit in
  admitP(precond1 cs bit init);
  garbage_value_lemma cs bit init cs';
  lookup_is_valF cs.symtab

val alloc_pres_equiv : cs:circGCState -> bs:boolState -> init:state ->
  Lemma (requires (valid_GC_state cs init /\ equiv_state cs bs init))
	(ensures  (valid_GC_state (snd (circGCAlloc cs)) init /\
	           equiv_state (snd (circGCAlloc cs)) (snd (boolAlloc bs)) init))
let alloc_pres_equiv cs bs init =
  let (l, cs') = circGCAlloc cs in
  let (k, bs') = boolAlloc bs in
  alloc_pres_valid cs init;
  alloc_value_lemma cs init cs';
  lookup_is_valF cs.symtab

val assign_pres_equiv : cs:circGCState -> bs:boolState -> l:int -> bexp:BoolExp -> init:state ->
  Lemma (requires (valid_GC_state cs init /\ equiv_state cs bs init))
	(ensures  (valid_GC_state (circGCAssign cs l bexp) init /\
	           equiv_state (circGCAssign cs l bexp) (boolAssign bs l bexp) init))
let assign_pres_equiv cs bs l bexp init =
  let cs' = circGCAssign cs l bexp in
  let bs' = boolAssign bs l bexp in
  let bit = lookup cs.symtab l in
  let bexp' = substVar bexp cs.symtab in
  valid_implies_pre cs l init;
  assign_value_lemma cs l bexp init cs';
  assign_pres_valid cs l bexp init;
  lookup_is_valF cs.symtab;
  substVar_value_pres bexp cs.symtab (snd bs) (evalCirc cs.gates init);
  match (lookup cs.cvals bit, factorAs bexp' bit) with
    | (BFalse, _)      -> ()
    | (_, Some bexp'') -> ()
    | _ ->
      let (ah', bit', _, circ') = compileBexp_oop cs.ah bexp' in
      let cs'' = 
        { top    = cs.top; 
          ah     = ah'; 
          gates  = cs.gates @ circ'; 
	  symtab = update cs.symtab l bit'; 
	  isanc  = update cs.isanc bit' true; 
	  cvals  = update cs.cvals bit' bexp' } 
      in
        garbageCollect_pres_equiv cs'' bs bit init

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
