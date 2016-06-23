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
    gates : list Gate;
    subs : Total.t int int }

val circInit   : circState
val circAlloc  : circState -> BoolExp -> Tot (int * circState)
val circAssign : circState -> int -> BoolExp -> Tot circState
val circEval   : circState -> state -> int -> Tot bool

let circInit = {top = 0; ah = emptyHeap; gates = []; subs = constMap 0}
let circAlloc cs bexp =
  let (ah', res, ancs, circ') = compileBexp_oop cs.ah (substVar bexp cs.subs) in
  let top' = cs.top + 1 in
  let gates' = cs.gates @ circ' in
  let subs' = update cs.subs cs.top res in
  (cs.top, {top = top'; ah = ah'; gates = gates'; subs = subs'})
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

val allocNcirc : list GExpr * circState -> i:int ->
  Tot (list GExpr * circState) (decreases i)
let rec allocNcirc (locs, cs) i =
  if i <= 0 then (List.rev locs, cs)
  else
    let (ah', res) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                subs = update cs.subs cs.top res }
    in
      allocNcirc (((LOC cs.top)::locs), cs') (i-1)

val allocTycirc : GType -> circState -> Tot (result (GExpr * circState))
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

(** Verification utilities *)
(* Correctness of circuit compilation *)
type circ_equiv (st:boolState) (cs:circState) (init:state) =
  fst st = cs.top /\
  zeroHeap (evalCirc cs.gates init) cs.ah /\
  (forall i. not (mem (lookup cs.subs i) cs.ah)) /\
  (forall i. boolEval st init i = circEval cs init i)

(* Needed for disjointness after applying substitution *)
val substVar_disjoint : bexp:BoolExp -> subs:Total.t int int -> s:set int ->
  Lemma (requires (forall i. not (Set.mem (lookup subs i) s)))
        (ensures  (disjoint s (vars (substVar bexp subs))))
let rec substVar_disjoint bexp subs s = match bexp with
  | BFalse -> ()
  | BVar i -> ()
  | BNot x -> substVar_disjoint x subs s
  | BAnd (x, y) | BXor (x, y) -> 
    substVar_disjoint x subs s; 
    substVar_disjoint y subs s

val eval_bexp_swap2 : st:boolState -> cs:circState -> bexp:BoolExp -> bexp':BoolExp -> init:state ->
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

val eval_commutes_subst_circ : st:boolState -> cs:circState -> bexp:BoolExp ->
  bexp':BoolExp -> init:state -> targ:int -> targ':int ->
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
  bexp:BoolExp -> bexp':BoolExp -> init:state ->
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

val circ_equiv_alloc : st:boolState -> cs:circState -> init:state -> bexp:BoolExp ->
  Lemma (requires (circ_equiv st cs init))
        (ensures  (circ_equiv (snd (boolAlloc st bexp)) (snd (circAlloc cs bexp)) init))
let circ_equiv_alloc st cs init bexp =
  let bexp' = substVar bexp cs.subs in
  let init' = evalCirc cs.gates init in
  let (ah', res, ancs, circ') = compileBexp_oop cs.ah bexp' in
  let st' = snd (boolAlloc st bexp) in
  let cs' = snd (circAlloc cs bexp) in
  let zeroHeap_lem =
    substVar_disjoint bexp cs.subs (elts cs.ah);
    compile_decreases_heap_oop cs.ah bexp';
    compile_partition_oop cs.ah bexp';
    zeroHeap_subset init' cs.ah cs'.ah;
    zeroHeap_st_impl init' cs'.ah circ'
  in
  let preservation =
    compile_mods_oop cs.ah bexp';
    eval_mod init' circ'
  in
  let correctness =
    eval_commutes_subst_circ_oop st cs bexp bexp' init
  in
  ()

val circ_equiv_assign : st:boolState -> cs:circState -> init:state -> l:int -> bexp:BoolExp ->
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
        zeroHeap_st_impl init' cs'.ah circ'
      in
      let preservation =
        compile_mods_oop cs.ah bexp';
        eval_mod init' circ'
      in
      let correctness =
        eval_commutes_subst_circ_oop st cs bexp bexp' init
      in
      ()
    | Some bexp'' -> (* TODO: Fix this, doesn't pass anymore *)
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
      let preservation = //admitP(forall i. not (i = l) ==> boolEval st' init i = circEval cs' init i);
        compile_mods cs.ah l' bexp'';
        eval_mod init' circ'
      in
      let correctness = //admitP(b2t(lookup (snd st') l = lookup (evalCirc circ' init') (lookup cs'.subs l)))
        admitP(b2t(boolEval st' init l = circEval cs' init l));
        eval_commutes_subst_circ st cs bexp bexp'' init l l'
      in
        //admitP(forall i. boolEval st' init i = circEval cs' init i);
      ()


(* TODO: Fix this, doesn't pass anymore *)
val circ_equiv_step : gexp:GExpr -> st:boolState -> st':circState -> init:state ->
  Lemma (requires (circ_equiv st st' init))
        (ensures
          (is_Err (step (gexp, st) boolInterp) /\ is_Err (step (gexp, st') circInterp)) \/
          (is_Val (step (gexp, st) boolInterp) /\ is_Val (step (gexp, st') circInterp) /\
          (fst (getVal (step (gexp, st) boolInterp)) =
           fst (getVal (step (gexp, st') circInterp)) /\
          circ_equiv (snd (getVal (step (gexp, st) boolInterp)))
                      (snd (getVal (step (gexp, st') circInterp)))
                      init)))
  (decreases %[gexp;1])
val circ_equiv_step_lst : lst:list GExpr -> st:boolState -> st':circState -> init:state ->
  Lemma (requires (circ_equiv st st' init))
        (ensures
          (is_Err (step_lst (lst, st) boolInterp) /\ is_Err (step_lst (lst, st') circInterp)) \/
          (is_Val (step_lst (lst, st) boolInterp) /\ is_Val (step_lst (lst, st') circInterp) /\
          (fst (getVal (step_lst (lst, st) boolInterp)) =
           fst (getVal (step_lst (lst, st') circInterp)) /\
          circ_equiv (snd (getVal (step_lst (lst, st) boolInterp)))
                      (snd (getVal (step_lst (lst, st') circInterp)))
                      init)))
  (decreases %[lst;0])
let rec circ_equiv_step gexp st st' init = match gexp with
  | LET (x, t1, t2) ->
    circ_equiv_step t1 st st' init
  | LAMBDA (x, ty, t) -> ()
  | APPLY (t1, t2) ->
    circ_equiv_step t1 st st' init;
    circ_equiv_step t2 st st' init
  | SEQUENCE (t1, t2) ->
    circ_equiv_step t1 st st' init;
    circ_equiv_step t2 st st' init
  | ASSIGN (t1, t2) ->
    circ_equiv_step t1 st st' init;
    circ_equiv_step t2 st st' init;
    if (isVal t1 && isBexp t2) then
      begin match t1 with
        | LOC l -> circ_equiv_assign st st' init l (get_bexp t2)
        | _ -> ()
      end
  | XOR (t1, t2) ->
    circ_equiv_step t1 st st' init;
    circ_equiv_step t2 st st' init
  | AND (t1, t2) ->
    circ_equiv_step t1 st st' init;
    circ_equiv_step t2 st st' init
  | BOOL b -> ()
  | APPEND (t1, t2) ->
    circ_equiv_step t1 st st' init;
    circ_equiv_step t2 st st' init
  | ROT (i, t) ->
    circ_equiv_step t st st' init
  | SLICE (t, i, j) ->
    circ_equiv_step t st st' init
  | ARRAY lst ->
    circ_equiv_step_lst lst st st' init
  | GET_ARRAY (t, i) ->
    circ_equiv_step t st st' init
  | ASSERT t ->
    circ_equiv_step t st st' init
  | BEXP bexp -> circ_equiv_alloc st st' init bexp
  | _ -> ()
and circ_equiv_step_lst lst st st' init = match lst with
  | [] -> ()
  | x::xs ->
    circ_equiv_step x st st' init;
    circ_equiv_step_lst xs st st' init
