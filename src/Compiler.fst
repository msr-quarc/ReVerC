(** Main compiler transformation *)
module Compiler

open Util
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
    subs : Total.t int int }

val circInit   : circState
val circAlloc  : circState -> Tot (int * circState)
val circAssign : circState -> int -> boolExp -> Tot circState
val circEval   : circState -> state -> int -> Tot bool

let circInit = {top = 0; ah = emptyHeap; gates = []; subs = constMap 0}
let circAlloc cs =
  let (ah', bit) = popMin cs.ah in
  let cs' = 
    { top = cs.top + 1; 
      ah = ah'; 
      gates = cs.gates; 
      subs = update cs.subs cs.top bit }
  in
    (cs.top, cs')
let circAssign cs l bexp =
  let l' = lookup cs.subs l in
  let bexp' = substVar bexp cs.subs in
  let (ah', res, ancs, circ') = match factorAs bexp' l' with
    | None -> compileBexp_oop cs.ah bexp'
    | Some bexp'' -> compileBexp cs.ah l' bexp''
  in
  {top = cs.top; ah = ah'; gates = cs.gates @ circ'; subs = update cs.subs l res}
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
                subs = update cs.subs cs.top res }
    in
      allocNcirc (((LOC cs.top)::locs), cs') (i-1)

val allocTycirc : gType -> circState -> Tot (result (gExpr * circState))
let allocTycirc ty cs = match ty with
  | GBool ->
    let (ah', res) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                subs = update cs.subs cs.top res }
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
(* Correctness of circuit compilation *)
type circ_equiv (st:boolState) (cs:circState) (init:state) =
  fst st = cs.top /\
  zeroHeap (evalCirc cs.gates init) cs.ah /\
  disjoint (vals cs.subs) (elts cs.ah) /\
  (forall i. boolEval st init i = circEval cs init i)

(* Needed for disjointness after applying substitution *)
val substVar_disjoint : bexp:boolExp -> subs:Total.t int int -> s:set int ->
  Lemma (requires (disjoint s (vals subs)))
        (ensures  (disjoint s (vars (substVar bexp subs))))
let substVar_disjoint bexp subs s =
  substVar_elems bexp subs

val eval_bexp_swap2 : st:boolState -> cs:circState -> bexp:boolExp -> bexp':boolExp -> init:state ->
  Lemma (requires (circ_equiv st cs init /\
                   bexp' = substVar bexp cs.subs /\
                   disjoint (elts cs.ah) (vars bexp')))
        (ensures  (evalBexp bexp (snd st) = evalBexp bexp' (evalCirc cs.gates init)))
let rec eval_bexp_swap2 st cs bexp bexp' init = match (bexp, bexp') with
  | (BFalse, _) -> ()
  | (BVar i, _) -> ()
  | (BNot x, BNot x') -> eval_bexp_swap2 st cs x x' init
  | (BAnd (x, y), BAnd (x', y')) | (BXor (x, y), (BXor (x', y'))) ->
    eval_bexp_swap2 st cs x x' init;
    eval_bexp_swap2 st cs y y' init

val eval_commutes_subst_circ : st:boolState -> cs:circState -> bexp:boolExp ->
  bexp':boolExp -> init:state -> targ:int -> targ':int ->
  Lemma (requires (circ_equiv st cs init /\
                   bexp' = substVar bexp cs.subs /\
                   targ' = lookup cs.subs targ /\
                   not (Set.mem targ' (vars bexp')) /\
                   not (Set.mem targ' (elts cs.ah)) /\
                   disjoint (elts cs.ah) (vars bexp')))
        (ensures  (lookup (evalCirc (last (compileBexp cs.ah targ' bexp'))
                                    (evalCirc cs.gates init)) targ' 
                   =
                   lookup (snd st) targ <> evalBexp bexp (snd st)))
let eval_commutes_subst_circ st cs bexp bexp' init targ targ' =
  let init' = evalCirc cs.gates init in
    compile_bexp_correct cs.ah targ' bexp' init';
    eval_bexp_swap2 st cs bexp bexp' init

val eval_commutes_subst_circ_oop : st:boolState -> cs:circState ->
  bexp:boolExp -> bexp':boolExp -> init:state ->
  Lemma (requires (circ_equiv st cs init /\
                   bexp' = substVar bexp cs.subs /\
                   disjoint (elts cs.ah) (vars bexp')))
        (ensures  (lookup (evalCirc (last (compileBexp_oop cs.ah bexp'))
                                    (evalCirc cs.gates init))
                          (second (compileBexp_oop cs.ah bexp')) 
                   = evalBexp bexp (snd st)))
let eval_commutes_subst_circ_oop st cs bexp bexp' init =
  let init' = evalCirc cs.gates init in
    compile_bexp_correct_oop cs.ah bexp' init';
    eval_bexp_swap2 st cs bexp bexp' init

val circ_equiv_alloc : st:boolState -> cs:circState -> init:state ->
  Lemma (requires (circ_equiv st cs init))
        (ensures  (circ_equiv (snd (boolAlloc st)) (snd (circAlloc cs)) init))
let circ_equiv_alloc st cs init =
  let (ah', bit) = popMin cs.ah in
  let cs' = snd (circAlloc cs) in
  let st' = snd (boolAlloc st) in
    pop_proper_subset cs.ah;
    zeroHeap_subset (evalCirc cs.gates init) cs.ah cs'.ah;
    lookup_is_val cs'.subs cs.top;
    lookup_subset cs.subs cs.top bit

val circ_equiv_assign : st:boolState -> cs:circState -> init:state -> l:int -> bexp:boolExp ->
  Lemma (requires (circ_equiv st cs init))
        (ensures  (circ_equiv (boolAssign st l bexp) (circAssign cs l bexp) init))
let circ_equiv_assign st cs init l bexp =
  let l' = lookup cs.subs l in
  let bexp' = substVar bexp cs.subs in
  let init' = evalCirc cs.gates init in
  let st' = boolAssign st l bexp in
  let cs' = circAssign cs l bexp in
  match factorAs bexp' l' with
    | None ->
      let (ah', res, ancs, circ') = compileBexp_oop cs.ah bexp' in
      let zeroHeap_lem = 
	substVar_disjoint bexp cs.subs (elts cs.ah);
	compile_decreases_heap_oop cs.ah bexp';
	compile_partition_oop cs.ah bexp';
	zeroHeap_subset init' cs.ah cs'.ah;
	zeroHeap_st_impl init' cs'.ah circ';
	//assert(zeroHeap (evalCirc cs'.gates init) cs'.ah);
	()
      in
      let disjoint_vals_lem =
	lookup_subset cs.subs l res;
	//assert(disjoint (vals cs'.subs) (elts cs'.ah));
	()
      in
      let preservation_lem =
	compile_mods_oop cs.ah bexp';
	eval_mod init' circ';
	admitP(forall i. not (i = l) ==> boolEval st' init i = circEval cs' init i);
	()
      in
      let correctness_lem =
	eval_commutes_subst_circ_oop st cs bexp bexp' init;
	//assert(boolEval st' init l = circEval cs' init l);
	()
      in
      ()
    | Some bexp'' -> admit() (* TODO: Fix this, doesn't pass anymore
      let (ah', res, ancs, circ') = compileBexp cs.ah l' bexp'' in
      let zeroHeap_lem =
        factorAs_correct bexp' l' init';
        factorAs_vars bexp' l';
        substVar_disjoint bexp cs.subs (elts cs.ah);
        disjoint_subset (vars bexp'') (vars bexp') (elts cs.ah);
        compile_decreases_heap cs.ah l' bexp'';
        compile_partition cs.ah l' bexp'';
        zeroHeap_subset init' cs.ah cs'.ah;
        zeroHeap_st_impl init' cs'.ah circ'
      in
      let preservation = //(forall i. not (i = l) ==> boolEval st' init i = circEval cs' init i);
        compile_mods cs.ah l' bexp'';
        eval_mod init' circ'
      in
      let correctness = //(b2t(lookup (snd st') l = lookup (evalCirc circ' init') (lookup cs'.subs l)))
        admitP(b2t(boolEval st' init l = circEval cs' init l));
        eval_commutes_subst_circ st cs bexp bexp'' init l l'
      in
        //(forall i. boolEval st' init i = circEval cs' init i);
      () *)

