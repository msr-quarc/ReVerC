module BoolExp

(* BoolExp - Boolean expressions over false, not, and, xor, and free variables.
             This module also defines compilation to circuits in three ways:
             No cleanup of ancillas, cleanup of ancillas after compilation,
             and intermittent cleanup during compilation. All three are proven
             correct with respect to the output and the cleanliness of ancillas.
             Boolean simplifications are also defined here and proven correct *)

open Util
open Total
open AncillaHeap
open Circuit

type BoolExp =
  | BFalse
  | BVar of int
  | BNot of BoolExp
  | BAnd of BoolExp * BoolExp
  | BXor of BoolExp * BoolExp

// Printing
val prettyPrintBexp : BoolExp -> string
let rec prettyPrintBexp bexp = match bexp with
  | BFalse -> "false"
  | BVar i -> Prims.string_of_int i
  | BNot x -> String.strcat "~" (prettyPrintBexp x)
  | BAnd (x, y) -> String.strcat "("
                (String.strcat (prettyPrintBexp x)
                (String.strcat " && "
                (String.strcat (prettyPrintBexp y) ")")))
  | BXor (x, y) -> String.strcat "("
                (String.strcat (prettyPrintBexp x)
                (String.strcat " <> "
                (String.strcat (prettyPrintBexp y) ")")))

// Membership
val occursInBexp : int -> exp:BoolExp -> Tot bool (decreases exp)
let rec occursInBexp i exp = match exp with
  | BFalse      -> false
  | BVar n      -> n = i
  | BAnd (x, y) -> occursInBexp i x || occursInBexp i y
  | BXor (x, y) -> occursInBexp i x || occursInBexp i y
  | BNot x      -> occursInBexp i x

val vars : BoolExp -> Tot (set int)
let vars exp = fun i -> occursInBexp i exp

// Use getVars for computational stuff
val getVars_acc : list int -> exp:BoolExp -> Tot (list int) (decreases exp)
let rec getVars_acc acc exp = match exp with
  | BFalse   -> []
  | BVar n   -> if FStar.List.memT n acc then acc else n::acc
  | BAnd (x, y) -> getVars_acc (getVars_acc acc x) y
  | BXor (x, y) -> getVars_acc (getVars_acc acc x) y
  | BNot exp -> getVars_acc acc exp

val getVars : BoolExp -> Tot (list int)
let getVars exp = getVars_acc [] exp

// Consistency of getVars -- finish this if needed later
(*
val getVars_acc_eq_vars : l:list int -> exp:BoolExp ->
  Lemma (forall i. vars exp i <==> FStar.List.mem i (getVars_acc l exp)) (decreases exp)
let rec getVars_acc_eq_vars l exp = match exp with
  | BVar n   -> ()
  | BAnd (x, y)
  | BXor (x, y) -> getVars_acc_eq_vars l x; getVars_acc_eq_vars (getVars_acc l x) y
  | BNot x   -> getVars_acc_eq_vars l x

val getVars_eq_vars : exp:BoolExp ->
  Lemma (forall i. vars exp i <==> FStar.List.mem i (getVars exp))
let rec getVars_eq_vars exp = getVars_acc_eq_vars [] exp
*)

// Maximums, counting -- Replace this with a version defined directly on BoolExp
val max : int -> int -> Tot int
let max x y = if x > y then x else y

val listMax : (list int) -> Tot int
let rec listMax lst = match lst with
  | [] -> 0
  | x::xs -> max x (listMax xs)

val varCount : BoolExp -> Tot int
let varCount exp = FStar.List.lengthT (getVars exp)

val varMax : BoolExp -> Tot int
let varMax exp = listMax (getVars exp)

val gtVars : int -> BoolExp -> Tot bool
let rec gtVars i bexp = match bexp with
  | BFalse -> false
  | BVar j -> i > j
  | BNot x -> gtVars i x
  | BXor (x, y) | BAnd (x, y) -> gtVars i x && gtVars i y

// Substitutions
val substBexp : BoolExp -> Total.map int BoolExp -> Tot BoolExp
let rec substBexp bexp sub = match bexp with
  | BFalse   -> BFalse
  | BVar i   -> sub i
  | BNot x   -> BNot (substBexp x sub)
  | BAnd (x, y) -> BAnd ((substBexp x sub), (substBexp y sub))
  | BXor (x, y) -> BXor ((substBexp x sub), (substBexp y sub))

val substVar : BoolExp -> Total.map int int -> Tot BoolExp
let rec substVar bexp sub = match bexp with
  | BFalse   -> BFalse
  | BVar i   -> BVar (sub i)
  | BNot x   -> BNot (substVar x sub)
  | BAnd (x, y) -> BAnd ((substVar x sub), (substVar y sub))
  | BXor (x, y) -> BXor ((substVar x sub), (substVar y sub))

// Evaluation
val evalBexp : bexp:BoolExp -> state -> Tot bool
let rec evalBexp bexp st = match bexp with
  | BFalse   -> false
  | BVar i   -> st i
  | BNot x   -> not (evalBexp x st)
  | BAnd (x, y) -> (evalBexp x st) && (evalBexp y st)
  | BXor (x, y) -> (evalBexp x st) <> (evalBexp y st)

// Optimizations
val simplify : exp:BoolExp -> Tot BoolExp
let rec simplify exp = match exp with
  | BFalse -> BFalse
  | BVar x -> exp
  | BAnd (x, y) ->
    let x' = simplify x in
    let y' = simplify y in (
      match (x', y') with
        | (BFalse, _) | (_, BFalse) -> BFalse
        | _ -> BAnd (x', y')
    )
  | BXor (x, y) ->
    let x' = simplify x in
    let y' = simplify y in (
      match (x', y') with
        | (BFalse, z) | (z, BFalse) -> z
        | _ -> BXor (x', y')
    )
  | BNot x ->
    let x' = simplify x in begin match x' with
      | BNot y -> y
      | _ -> BNot x'
    end

val factorAs : exp:BoolExp -> targ:int -> Tot (option BoolExp)
let rec factorAs exp targ = match exp with
  | BFalse -> None
  | BVar i -> if i = targ then Some BFalse else None
  | BNot x -> (
    match factorAs x targ with
      | None -> None
      | Some x' -> Some (BNot x')
    )
  | BAnd (x, y) -> None
  | BXor (x, y) ->
    if not (occursInBexp targ y) then (
      match factorAs x targ with
        | None -> None
        | Some x' -> Some (BXor (x', y))
    ) else if not (occursInBexp targ x) then (
      match factorAs y targ with
        | None -> None
        | Some y' -> Some (BXor (x, y'))
    ) else None

val distributeAnds : exp:BoolExp -> Tot BoolExp
let rec distributeAnds exp = match exp with
  | BFalse -> BFalse
  | BVar v -> BVar v
  | BNot x -> BNot (distributeAnds x)
  | BAnd (x, y) ->
    begin match (distributeAnds x, distributeAnds y) with
      | (BXor (a, b), BXor (c, d)) ->
        BXor (BXor (BAnd (a, c), BAnd (b, c)), BXor (BAnd (a, d), BAnd (b, d)))
      | (x', BXor (c, d)) -> BXor (BAnd (x', c), BAnd (x', d))
      | (BXor (a, b), y') -> BXor (BAnd (a, y'), BAnd (b, y'))
      | (x', y') -> BAnd (x', y')
    end
  | BXor (x, y) -> BXor (distributeAnds x, distributeAnds y)

val undistributeAnds : exp:BoolExp -> Tot BoolExp
let rec undistributeAnds exp = match exp with
  | BFalse -> BFalse
  | BVar v -> BVar v
  | BNot x -> BNot (undistributeAnds x)
  | BAnd (x, y) -> BAnd (undistributeAnds x, undistributeAnds y)
  | BXor (x, y) ->
    begin match (undistributeAnds x, undistributeAnds y) with
      | (BAnd (a, b), BAnd (c, d)) ->
        if a = c then BAnd (a, BXor (b, d))
        else if a = d then BAnd (a, BXor (b, c))
        else if b = c then BAnd (b, BXor (a, d))
        else if b = d then BAnd (b, BXor (a, c))
        else BXor (BAnd (a, b), BAnd (c, d))
      | (x', y') -> BXor (x', y')
    end

// Compilation stuff
type compilerResult = AncHeap * int * (list int) * (list Gate)

val compileBexp : AncHeap -> int -> exp:BoolExp -> Tot compilerResult (decreases %[exp;0])
val compileBexp_oop : AncHeap -> exp:BoolExp -> Tot compilerResult (decreases %[exp;1])
let rec compileBexp ah targ exp = match exp with
  | BFalse   -> (ah, targ, [], [])
  | BVar v   -> (ah, targ, [], [RCNOT (v, targ)])
  | BAnd (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexp_oop ah x in
    let (ah'', yres, yanc, ygate) = compileBexp_oop ah' y in
      (ah'', targ, xanc @ yanc, (xgate @ ygate) @ [RTOFF (xres, yres, targ)])
  | BXor (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexp ah targ x in
    let (ah'', yres, yanc, ygate) = compileBexp ah' targ y in
      (ah'', targ, xanc @ yanc, xgate @ ygate)
  | BNot exp  ->
    let (ah', xres, xanc, xgate) = compileBexp ah targ exp in
      (ah', targ, xanc, xgate @ [RNOT xres])
and compileBexp_oop ah exp = match exp with
  | BVar v -> (ah, v, [], [])
  | _ ->
    let (ah', targ) = popMin ah in
    let (ah'', res, anc, gate) = compileBexp ah' targ exp in
      (ah'', res, targ::anc, gate)

val compileBexpClean : AncHeap -> int -> BoolExp -> Tot compilerResult
val compileBexpClean_oop : AncHeap -> BoolExp -> Tot compilerResult
let compileBexpClean ah targ exp =
  let (ah', res, anc, circ) = compileBexp ah targ exp in
  let cleanup = uncompute circ res in
  let ah'' = FStar.List.fold_leftT insert ah' anc in
    (ah'', res, [], circ@(FStar.List.rev cleanup))
let compileBexpClean_oop ah exp = match exp with
  | BVar v -> (ah, v, [], [])
  | _ ->
    let (ah', targ) = popMin ah in
    let (ah'', res, anc, gate) = compileBexpClean ah' targ exp in
      (ah'', res, targ::anc, gate)

val compileBexpPebbled : AncHeap -> int -> exp:BoolExp -> Tot compilerResult (decreases %[exp;0])
val compileBexpPebbled_oop : AncHeap -> exp:BoolExp -> Tot compilerResult (decreases %[exp;1])
let rec compileBexpPebbled ah targ exp = match exp with
  | BFalse   -> (ah, targ, [], [])
  | BVar v   -> (ah, targ, [], [RCNOT (v, targ)])
  | BAnd (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexpPebbled_oop ah x in
    let (ah'', yres, yanc, ygate) = compileBexpPebbled_oop ah' y in
    let cleanup = uncompute (xgate @ ygate) targ in
    let ah''' = FStar.List.fold_leftT insert  ah'' (xanc@yanc) in
      (ah''', targ, [], (xgate @ ygate) @ [RTOFF (xres, yres, targ)] @ (FStar.List.rev cleanup))
  | BXor (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexpPebbled ah targ x in
    let (ah'', yres, yanc, ygate) = compileBexpPebbled ah' targ y in
      (ah'', targ, xanc @ yanc, xgate @ ygate)
  | BNot exp  ->
    let (ah', xres, xanc, xgate) = compileBexpPebbled ah targ exp in
      (ah', targ, xanc, xgate @ [RNOT xres])
and compileBexpPebbled_oop ah exp = match exp with
  | BVar v -> (ah, v, [], [])
  | _ ->
    let (ah', targ) = popMin ah in
    let (ah'', res, anc, gate) = compileBexpPebbled ah' targ exp in
      (ah'', res, targ::anc, gate)

// ---------------------------------------------------------- BoolExp properties
// Shortcuts
let first (x, _, _, _) = x
let second (_, x, _, _) = x
let third (_, _, x, _) = x
let last (_, _, _, x) = x

let compileBexpEval ah targ exp st =
  let (ah', res, anc, circ) = compileBexp ah targ exp in
    (evalCirc circ st) res
let compileBexpEval_oop ah exp st =
  let (ah', res, anc, circ) = compileBexp_oop ah exp in
    (evalCirc circ st) res
let compileBexpCleanEval ah targ exp st =
  let (ah', res, anc, circ) = compileBexpClean ah targ exp in
    (evalCirc circ st) res
let compileBexpCleanEval_oop ah exp st =
  let (ah', res, anc, circ) = compileBexpClean_oop ah exp in
    (evalCirc circ st) res
let compileBexpCleanEvalSt ah targ exp st =
  let (ah', res, anc, circ) = compileBexpClean ah targ exp in
    evalCirc circ st
let compileBexpCleanEvalSt_oop ah exp st =
  let (ah', res, anc, circ) = compileBexpClean_oop ah exp in
    evalCirc circ st

// ------------------------------ Simplify is semantics preserving: DONE
val simplify_preserves_semantics : exp:BoolExp ->
  Lemma (forall (st:state). (evalBexp exp st) = (evalBexp (simplify exp) st))
let rec simplify_preserves_semantics exp = match exp with
  | BFalse -> ()
  | BVar x -> ()
  | BAnd (x, y) | BXor (x, y) ->
    simplify_preserves_semantics x;
    simplify_preserves_semantics y
  | BNot x -> simplify_preserves_semantics x

val factorAs_correct : exp:BoolExp -> targ:int -> st:state ->
  Lemma (forall exp'. factorAs exp targ = Some exp' ==>
          not (occursInBexp targ exp') /\ evalBexp exp st = st targ <> evalBexp exp' st)
let rec factorAs_correct exp targ st = match exp with
  | BFalse -> ()
  | BVar x -> ()
  | BNot x -> factorAs_correct x targ st
  | BAnd (x, y) -> ()
  | BXor (x, y) ->
    factorAs_correct x targ st;
    factorAs_correct y targ st

val factorAs_vars : exp:BoolExp -> targ:int ->
  Lemma (forall exp'. factorAs exp targ = Some exp' ==> ins targ (vars exp') = (vars exp))
let rec factorAs_vars exp targ = match exp with
  | BFalse -> ()
  | BVar x -> ()
  | BNot x -> factorAs_vars x targ
  | BAnd (x, y) -> ()
  | BXor (x, y) ->
    factorAs_vars x targ;
    factorAs_vars y targ

val idempotentAnd : x:BoolExp ->
  Lemma (forall st. evalBexp x st = evalBexp (BAnd (x, x)) st)
val commutativityAnd : x:BoolExp -> y:BoolExp ->
  Lemma (forall st. evalBexp (BAnd (x, y)) st = evalBexp (BAnd (y, x)) st)
val commutativityXor : x:BoolExp -> y:BoolExp ->
  Lemma (forall st. evalBexp (BXor (x, y)) st = evalBexp (BXor (y, x)) st)
val distributivityAndXor : x:BoolExp -> y:BoolExp -> z:BoolExp ->
  Lemma (forall st. evalBexp (BAnd (x, BXor (y, z))) st = evalBexp (BXor (BAnd (x, y), BAnd (x, z))) st)

let idempotentAnd x = ()
let commutativityAnd x y = ()
let commutativityXor x y = ()
let distributivityAndXor x y z = ()

val distribute_preserves_semantics : exp:BoolExp ->
  Lemma (forall (st:state). (evalBexp exp st) = (evalBexp (distributeAnds exp) st))
let rec distribute_preserves_semantics exp = match exp with
  | BFalse -> ()
  | BVar x -> ()
  | BNot x -> distribute_preserves_semantics x
  | BXor (x, y) -> distribute_preserves_semantics x; distribute_preserves_semantics y
  | BAnd (x, y) ->
    distribute_preserves_semantics x;
    distribute_preserves_semantics y;
    begin match (distributeAnds x, distributeAnds y) with
      | (BXor (a, b), BXor (c, d)) ->
        distributivityAndXor (BXor (a, b)) c d;
        commutativityAnd (BXor (a, b)) c;
        commutativityAnd (BXor (a, b)) d;
        distributivityAndXor c a b;
        distributivityAndXor d a b;
        commutativityAnd c a;
        commutativityAnd c b;
        commutativityAnd d a;
        commutativityAnd d b
      | (x', BXor (c, d)) -> distributivityAndXor x' c d
      | (BXor (a, b), y') ->
        commutativityAnd (BXor (a, b)) y';
        distributivityAndXor y' a b;
        commutativityAnd y' a;
        commutativityAnd y' b
      | (x', y') -> ()
    end

val undistribute_preserves_semantics : exp:BoolExp ->
  Lemma (forall (st:state). (evalBexp exp st) = (evalBexp (undistributeAnds exp) st))
let rec undistribute_preserves_semantics exp = match exp with
  | BFalse -> ()
  | BVar x -> ()
  | BNot x -> undistribute_preserves_semantics x
  | BAnd (x, y) -> undistribute_preserves_semantics x; undistribute_preserves_semantics y
  | BXor (x, y) ->
    undistribute_preserves_semantics x;
    undistribute_preserves_semantics y;
    begin match (undistributeAnds x, undistributeAnds y) with
      | (BAnd (a, b), BAnd (c, d)) ->
        if a = c then distributivityAndXor a b d
        else if a = d then (
          distributivityAndXor a b c;
          commutativityAnd a c
        ) else if b = c then (
          distributivityAndXor b a d;
          commutativityAnd b a
        ) else if b = d then (
          distributivityAndXor b a c;
          commutativityAnd b a;
          commutativityAnd b c
        ) else ()
      | (x', y') -> ()
    end


// ------------------------------ Compile produces the right output
// What we want to say is that in any context in the larger compiler,
// the output of the subcircuit compiled for the boolean expression is
// semantically equivalent to the boolean expression. Practically speaking
// this means we need to quantify over all calling contexts -- that is, ancilla
// heaps and output bit. In the case of the output bit b, as far as I can discern
// the compiler is really supposed to compute b <> bexp, so that's what we'll
// verify. Fortunately is this is an incorrect assumption, it should show when
// we try to verify the entire compilation process.
//
// The proof will hinge on the fact that we're using the ancilla properly: i.e.
// when we grab something off the ancilla heap, it is assured to be zero. This
// is the zeroHeap property.

// It looks like the zero heap property isn't strong enough: if a circuit
// modifies a qubit that's on the heap but initially zero, executing the circuit
// can break the zero heap property. We have two choices: make states partial,
// so the qubits the state is defined on are disjoint from the heap, or prove
// that given a heap disjoint from the variables in exp, when we compile exp
// the qubits are disjoint from the resulting heap. Let's try the second idea first.

type partition = #a:Type -> s:set a -> s':set a -> s'':set a ->
  (disjoint s s' /\ disjoint s s'' /\ disjoint s' s'')

// -------------------------------------------------------------------------DONE
// Compile is strictly decreasing on the heap
// This is a nice little proof because it's a very clean, simple proposition
// with no precondition. The proof essentially boils down to transitivity of
// the subset relation, but it's enlightening to see how to apply such a basic
// proof method "by hand" in F*

val compile_decreases_heap : ah:AncHeap -> targ:int -> exp:BoolExp ->
  Lemma (subset (elts (first (compileBexp ah targ exp))) (elts ah)) (decreases %[exp;0])
val compile_decreases_heap_oop : ah:AncHeap -> exp:BoolExp ->
  Lemma (subset (elts (first (compileBexp_oop ah exp))) (elts ah)) (decreases %[exp;1])
let rec compile_decreases_heap ah targ exp = match exp with
  | BFalse -> ()
  | BVar x -> ()
  | BAnd (x, y) ->
    let (ah', _, _, _) = compileBexp_oop ah x in
    let (ah'', _, _, _) = compileBexp_oop ah' y in
      compile_decreases_heap_oop ah x;
      compile_decreases_heap_oop ah' y;
      subset_trans (elts ah'') (elts ah') (elts ah)
  | BXor (x, y) ->
    let (ah', _, _, _) = compileBexp ah targ x in
    let (ah'', _, _, _) = compileBexp ah' targ y in
      compile_decreases_heap ah targ x;
      compile_decreases_heap ah' targ y;
      subset_trans (elts ah'') (elts ah') (elts ah)
  | BNot x ->
      compile_decreases_heap ah targ x
and compile_decreases_heap_oop ah exp = match exp with
  | BVar x -> ()
  | _ ->
    let (ah', targ) = popMin ah in
    let (ah'', _, _, _) = compileBexp ah' targ exp in
      pop_subset ah;
      compile_decreases_heap ah' targ exp;
      subset_trans (elts ah'') (elts ah') (elts ah)

val compileClean_decreases_heap : ah:AncHeap -> targ:int -> exp:BoolExp ->
  Lemma (subset (elts (first (compileBexp ah targ exp))) (elts ah)) (decreases %[exp;0])
val compileClean_decreases_heap_oop : ah:AncHeap -> exp:BoolExp ->
  Lemma (subset (elts (first (compileBexp_oop ah exp))) (elts ah)) (decreases %[exp;1])
let rec compileClean_decreases_heap ah targ exp = match exp with
  | BFalse -> ()
  | BVar x -> ()
  | BAnd (x, y) ->
    let (ah', _, _, _) = compileBexp_oop ah x in
    let (ah'', _, _, _) = compileBexp_oop ah' y in
      compileClean_decreases_heap_oop ah x;
      compileClean_decreases_heap_oop ah' y;
      subset_trans (elts ah'') (elts ah') (elts ah)
  | BXor (x, y) ->
    let (ah', _, _, _) = compileBexp ah targ x in
    let (ah'', _, _, _) = compileBexp ah' targ y in
      compileClean_decreases_heap ah targ x;
      compileClean_decreases_heap ah' targ y;
      subset_trans (elts ah'') (elts ah') (elts ah)
  | BNot x ->
      compileClean_decreases_heap ah targ x
and compileClean_decreases_heap_oop ah exp = match exp with
  | BVar x -> ()
  | _ ->
    let (ah', targ) = popMin ah in
    let (ah'', _, _, _) = compileBexp ah' targ exp in
      pop_subset ah;
      compileClean_decreases_heap ah' targ exp;
      subset_trans (elts ah'') (elts ah') (elts ah)

// -------------------------------------------------------------------------DONE
// Lemma(s) about the output bit
val compile_output : ah:AncHeap -> targ:int -> x:BoolExp ->
  Lemma (second (compileBexp ah targ x) = targ)
let compile_output ah targ x = ()

val compile_output_oop : ah:AncHeap -> x:BoolExp ->
  Lemma (requires (disjoint (elts ah) (vars x)))
        (ensures  (not (mem (second (compileBexp_oop ah x))
                            (first  (compileBexp_oop ah x)))))
let compile_output_oop ah x = match x with
  | BVar x -> ()
  | _ ->
    let (ah', targ) = popMin ah in
      pop_proper_subset ah;
      compile_decreases_heap ah' targ x

// -------------------------------------------------------------------------DONE
// Compile maintains heap disjointness -- that is, if the heap is disjoint
// from the variables in the boolean expression, then the heap will be disjoint
// with the qubits used in the circuit. We need this to prove later that
// evaluating sub-circuits doesn't destroy the integrity of the heap

// If we make every potential heap allocation a member of the heap, then
// this proof will only require showing that popMin, and therefore compileBexp is
// strictly decreasing in the subset order.

// Needed since we can't have local bindings in  types
type postCond (c:compilerResult) =
  disjoint (elts (first c)) (uses (last c)) /\
  not (mem (second c) (first c))

// These proofs are getting confusing enough that they need comments
val compile_partition : ah:AncHeap -> targ:int -> x:BoolExp ->
  Lemma (requires (disjoint (elts ah) (vars x) /\ not (mem targ ah)))
        (ensures  (postCond (compileBexp ah targ x))) (decreases %[x;0])
val compile_partition_oop : ah:AncHeap -> x:BoolExp ->
  Lemma (requires (disjoint (elts ah) (vars x)))
        (ensures  (postCond (compileBexp_oop ah x))) (decreases %[x;1])
let rec compile_partition ah targ x = match x with
  | BFalse -> ()
  | BVar v -> ()
  | BNot x ->
    let (ah', xres, _, xgate) = compileBexp ah targ x in
      compile_partition ah targ x;
      uses_append xgate [RNOT xres]
  | BXor (x, y) ->
    let (ah', xres, _, xgate) = compileBexp ah targ x in
    let (ah'', yres, _, ygate) = compileBexp ah' targ y in
    // ah'' is disjoint with xgate
      compile_partition ah targ x;
      compile_decreases_heap ah' targ y;
      disjoint_subset (elts ah'') (elts ah') (uses xgate);
    // ah'' is disjoint with xsgate
      compile_decreases_heap ah targ x;
      disjoint_subset (elts ah') (elts ah) (vars y);
      compile_partition ah' targ y;
    // ah'' is disjoint with xgate@ygate
      disjoint_union (elts ah'') (uses xgate) (uses ygate);
      uses_append xgate ygate;
      compile_output ah' targ y
  | BAnd (x, y) ->
    let (ah', xres, _, xgate)  = compileBexp_oop ah x in
    let (ah'', yres, _, ygate) = compileBexp_oop ah' y in
    // ah'' is disjoint with xgate
      compile_partition_oop ah x;
      compile_decreases_heap_oop ah' y;
      disjoint_subset (elts ah'') (elts ah') (uses xgate);
    // ah'' is disjoint with ygate
      compile_decreases_heap_oop ah x;
      disjoint_subset (elts ah') (elts ah) (vars y);
      compile_partition_oop ah' y;
    // ah'' is disjoint with xgate@ygate@[RTOFF xres yres targ]
      uses_append xgate ygate;
      uses_append (xgate@ygate) [RTOFF (xres, yres, targ)]
and compile_partition_oop ah x = match x with
  | BVar v -> ()
  | _ ->
    let (ah', targ) = popMin ah in
    // ah'' is disjoint with xgate
      pop_proper_subset ah;
      disjoint_subset (elts ah') (elts ah) (vars x);
      compile_partition ah' targ x

//--------------------------------------------------------------------------DONE
// Details which bits the compiled circuit may modify. In particular, it is
// gauranteed that the resulting circuit does not modify any bit outside of the
// target bit and the ancilla heap.
val compile_mods : ah:AncHeap -> targ:int -> x:BoolExp ->
  Lemma (subset (mods (last (compileBexp ah targ x))) (ins targ (elts ah)))
  (decreases %[x;0])
val compile_mods_oop : ah:AncHeap -> x:BoolExp ->
  Lemma (subset (mods (last (compileBexp_oop ah x))) (elts ah))
  (decreases %[x;1])
let rec compile_mods ah targ exp = match exp with
  | BFalse -> ()
  | BVar _ -> ()
  | BNot x ->
    let (ah', xres, _, xgate) =  compileBexp ah targ x in
      compile_mods ah targ x;
      mods_append xgate [RNOT xres]
  | BAnd (x, y) ->
    let (ah', xres, _, xgate) = compileBexp_oop ah x in
    let (ah'', yres, _, ygate) = compileBexp_oop ah' y in
    // mods (xgate) subset (ins targ ah)
      compile_mods_oop ah x;
      subset_ins targ (elts ah);
      subset_trans (mods xgate) (elts ah) (ins targ (elts ah));
    // mods (ygate) subset (ins targ ah)
      compile_decreases_heap_oop ah x;
      subset_ins targ (elts ah);
      subset_trans (elts ah') (elts ah) (ins targ (elts ah));
      compile_mods_oop ah' y;
      subset_trans (mods ygate) (elts ah') (ins targ (elts ah));
      mods_append xgate ygate;
      mods_append (xgate@ygate) [RTOFF (xres, yres, targ)]
  | BXor (x, y) ->
    let (ah', _, _, xgate)  = compileBexp ah targ x in
    let (ah'', _, _, ygate) = compileBexp ah' targ y in
    // mods (xgate) subset ins targ ah
      compile_mods ah targ x;
    // mods (ygate) subset ins targ ah
      compile_decreases_heap ah targ x;
      ins_subset_pres targ (elts ah') (elts ah);
      compile_mods ah' targ y;
      mods_append xgate ygate
and compile_mods_oop ah x = match x with
  | BVar v -> ()
  | _ ->
    let (ah', targ) = popMin ah in
    let (ah'', _, _, circ) = compileBexp ah' targ x in
      pop_proper_subset ah;
      compile_mods ah' targ x;
      subset_trans (mods circ) (ins targ (elts ah')) (elts ah)

//--------------------------------------------------------------------------DONE
// Finally compiler correctness
val eval_state_swap : x:BoolExp -> st:state -> st':state ->
  Lemma (requires (agree_on st st' (vars x)))
        (ensures  (evalBexp x st = evalBexp x st'))
let rec eval_state_swap x st st' = match x with
  | BFalse -> ()
  | BVar x -> ()
  | BNot x -> eval_state_swap x st st'
  | BAnd (x, y) -> eval_state_swap x st st'; eval_state_swap y st st'
  | BXor (x, y) -> eval_state_swap x st st'; eval_state_swap y st st'

val zeroHeap_st_impl : st:state -> ah:AncHeap -> gates:(list Gate) ->
  Lemma (requires (zeroHeap st ah /\ disjoint (elts ah) (uses gates)))
        (ensures  (zeroHeap (evalCirc gates st) ah))
let zeroHeap_st_impl st ah gates = ref_imp_use gates; eval_mod st gates

// English-language preconditions: everything on the heap is in the 0 state, and
// the heap, expression, and target bit are all mutually disjoint -- that is,
// nothing on the heap is mentioned in either the target bit or the expression,
// and the target bit is not in the expression

val compile_bexp_correct : ah:AncHeap -> targ:int -> exp:BoolExp -> st:state ->
  Lemma (requires (zeroHeap st ah /\ disjoint (elts ah) (vars exp) /\
                   not (Util.mem targ (elts ah)) /\
                   not (Util.mem targ (vars exp))))
        (ensures  (compileBexpEval ah targ exp st = st targ <> evalBexp exp st))
 (decreases %[exp;0])
val compile_bexp_correct_oop : ah:AncHeap -> exp:BoolExp -> st:state ->
  Lemma (requires (zeroHeap st ah /\ disjoint (elts ah) (vars exp)))
        (ensures  (compileBexpEval_oop ah exp st = evalBexp exp st))
 (decreases %[exp;1])
let rec compile_bexp_correct ah targ exp st = match exp with
  | BFalse -> ()
  | BVar x -> ()
  | BNot x ->
    let (ah', xres, xanc, xgate) = compileBexp ah targ x in
    let ind_hyp_x = compile_bexp_correct ah targ x st in
      evalCirc_append xgate [RNOT xres] st
  | BXor (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexp ah targ x in
    let (ah'', yres, yanc, ygate) = compileBexp ah' targ y in
    let st' = evalCirc xgate st in
    let ind_hyp_x = compile_bexp_correct ah targ x st in
    let ind_hyp_y =
      compile_decreases_heap ah targ x;
      disjoint_subset (elts ah') (elts ah) (vars y);
      compile_partition ah targ x;
      zeroHeap_subset st ah ah';
      zeroHeap_st_impl st ah' xgate;
      compile_bexp_correct ah' targ y st'
    in
    let lem1 = // (eval (xgate@ygate)) targ = (eval ygate st') targ
      evalCirc_append xgate ygate st
    in
    let lem2 = // eval y st = eval y st'
      compile_mods ah targ x;
      eval_mod st xgate;
      eval_state_swap y st st'
    in
      ()
  | BAnd (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexp_oop ah x in
    let (ah'', yres, yanc, ygate) = compileBexp_oop ah' y in
    let st' = evalCirc xgate st in
    let ind_hyp_x = compile_bexp_correct_oop ah x st in
    let ind_hyp_y =
      compile_decreases_heap_oop ah x;
      disjoint_subset (elts ah') (elts ah) (vars y);
      compile_partition_oop ah x;
      zeroHeap_subset st ah ah';
      zeroHeap_st_impl st ah' xgate;
      compile_bexp_correct_oop ah' y st'
    in
    let lem1 = // st' xres = (evalCirc ygate st') xres
      compile_mods_oop ah' y;
      eval_mod st' ygate
    in
    let lem2 = // eval y st = eval y st'
      compile_mods_oop ah x;
      eval_mod st xgate;
      eval_state_swap y st st'
    in
    let lem3 = () // st targ = (evalCirc ygate st') targ
    in
      evalCirc_append xgate ygate st;
      evalCirc_append (xgate@ygate) [RTOFF (xres, yres, targ)] st
and compile_bexp_correct_oop ah exp st = match exp with
  | BVar v -> ()
  | _ ->
    let (ah', targ) = popMin ah in
    let (ah'', _, _, gates) = compileBexp ah' targ exp in
      pop_proper_subset ah;
      pop_elt ah;
      compile_bexp_correct ah' targ exp st

//--------------------------------------------------------------------------DONE
// Precondition for proving correctness of cleanup. CompileBexp produces a
// well-formed circuit, the ancillas all come from the initial ancilla heap,
// and the result qubit is not used as a control anywhere. These should
// possibly be separate lemmas...

val compileBexp_wf : ah:AncHeap -> targ:int -> exp:BoolExp ->
  Lemma (requires (disjoint (elts ah) (vars exp) /\
                   not (Util.mem targ (elts ah)) /\
                   not (Util.mem targ (vars exp))))
        (ensures  (wfCirc (last (compileBexp ah targ exp))))
  (decreases %[exp;0])
val compileBexp_wf_oop : ah:AncHeap -> exp:BoolExp ->
  Lemma (requires (disjoint (elts ah) (vars exp)))
        (ensures  (wfCirc (last (compileBexp_oop ah exp))))
  (decreases %[exp;1])
let rec compileBexp_wf ah targ exp = match exp with
  | BFalse   -> ()
  | BVar v   -> ()
  | BNot x   -> compileBexp_wf ah targ x
  | BXor (x, y) ->
    let (ah', xres, xanc, xcirc)  = compileBexp ah targ x in
    let (ah'', yres, yanc, ycirc) = compileBexp ah' targ y in
    let ind_hyp_x = compileBexp_wf ah targ x in
    let ind_hyp_y =
      compile_decreases_heap ah targ x;
      disjoint_subset (elts ah') (elts ah) (vars y);
      compileBexp_wf ah' targ y
    in ()
  | BAnd (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexp_oop ah x in
    let (ah'', yres, yanc, ygate) = compileBexp_oop ah' y in
    let ind_hyp_x = compileBexp_wf_oop ah x in
    let ind_hyp_y =
      compile_decreases_heap_oop ah x;
      disjoint_subset (elts ah') (elts ah) (vars y);
      compileBexp_wf_oop ah' y
    in ()
and compileBexp_wf_oop ah exp = match exp with
  | BVar v -> ()
  | _ ->
    let (ah', targ) = popMin ah in
      pop_proper_subset ah;
      compileBexp_wf ah' targ exp

val compile_anc : ah:AncHeap -> targ:int -> exp:BoolExp ->
  Lemma (subset (mems (third (compileBexp ah targ exp))) (elts ah))
  (decreases %[exp;0])
val compile_anc_oop : ah:AncHeap -> exp:BoolExp ->
  Lemma (subset (mems (third (compileBexp_oop ah exp))) (elts ah))
  (decreases %[exp;1])
let rec compile_anc ah targ exp = match exp with
  | BFalse -> ()
  | BVar v -> ()
  | BNot x -> compile_anc ah targ x
  | BXor (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexp ah targ x in
    let (ah'', yres, yanc, ygate) = compileBexp ah' targ y in
      compile_anc ah targ x;
      compile_decreases_heap ah targ x;
      compile_anc ah' targ y;
      FStar.ListProperties.append_mem_forall xanc yanc
  | BAnd (x, y) ->
    let (ah', xres, xanc, xgate) = compileBexp_oop ah x in
    let (ah'', yres, yanc, ygate) = compileBexp_oop ah' y in
      compile_anc_oop ah x;
      compile_decreases_heap_oop ah x;
      compile_anc_oop ah' y;
      FStar.ListProperties.append_mem_forall xanc yanc
and compile_anc_oop ah exp = match exp with
  | BVar v -> ()
  | _ ->
    let (ah', targ) = popMin ah in
      pop_elt ah; pop_subset ah; compile_anc ah' targ exp

val compile_ctrls : ah:AncHeap -> targ:int -> x:BoolExp ->
  Lemma (subset (ctrls (last (compileBexp ah targ x)))
                (union (elts ah) (vars x)))
  (decreases %[x;0])
val compile_ctrls_oop : ah:AncHeap -> x:BoolExp ->
  Lemma (subset (ctrls (last (compileBexp_oop ah x)))
                (union (elts ah) (vars x)))
  (decreases %[x;1])
let rec compile_ctrls ah targ x = match x with
  | BFalse -> ()
  | BVar v -> ()
  | BNot x -> compile_ctrls ah targ x
  | BXor (x, y) ->
    let (ah', _, _, _) = compileBexp ah targ x in
    let ind_hyp_x = compile_ctrls ah targ x in
    let ind_hyp_y = compile_ctrls ah' targ y in
      compile_decreases_heap ah targ x
  | BAnd (x, y) ->
    let (ah', _, _, _) = compileBexp_oop ah x in
    let ind_hyp_x = compile_ctrls_oop ah x in
    let ind_hyp_y = compile_ctrls_oop ah' y in
      compile_decreases_heap_oop ah x
and compile_ctrls_oop ah x = match x with
  | BVar v -> ()
  | _ ->
    let (ah', targ) = popMin ah in
      pop_elt ah;
      pop_subset ah;
      compile_ctrls ah' targ x

//--------------------------------------------------------------------------DONE
// Compiling with cleanup produces same result as the regular compile and
// a zero heap.


type clean_heap_cond (ah:AncHeap) (targ:int) (exp:BoolExp) (st:state) =
  zeroHeap (compileBexpCleanEvalSt ah targ exp st)
           (first (compileBexpClean ah targ exp))

type clean_corr_cond (ah:AncHeap) (targ:int) (exp:BoolExp) (st:state) =
  compileBexpCleanEval ah targ exp st = compileBexpEval ah targ exp st

val compile_with_cleanup : ah:AncHeap -> targ:int -> exp:BoolExp -> st:state ->
  Lemma (requires (zeroHeap st ah /\ disjoint (elts ah) (vars exp) /\
                   not (Util.mem targ (elts ah)) /\
                   not (Util.mem targ (vars exp))))
        (ensures  (clean_heap_cond ah targ exp st /\
                   clean_corr_cond ah targ exp st))
let compile_with_cleanup ah targ exp st =
  let (ah', res, anc, circ) = compileBexp ah targ exp in
  let cleanup = uncompute circ res in
  let ah'' = FStar.List.fold_leftT insert ah' anc in
  let st' = evalCirc circ st in
  let st'' = evalCirc (circ@(FStar.List.rev cleanup)) st in
  let heap_cond =
    let lem1 = // zeroHeap st' ah'
      compile_decreases_heap ah targ exp;
      compile_partition ah targ exp;
      zeroHeap_subset st ah ah';
      zeroHeap_st_impl st ah' circ
    in
    let lem1 = // zeroHeap st'' ah'
      compileBexp_wf ah targ exp;
      uncompute_uses_subset circ res;
      zeroHeap_st_impl st' ah' (FStar.List.rev cleanup)
    in
      compile_ctrls ah targ exp;
      uncompute_mixed_inverse circ res st;
      compile_anc ah targ exp;
      zeroHeap_insert_list st'' ah' anc
  in
  let corr_cond =
    uncompute_targ circ res;
    eval_mod st' (FStar.List.rev cleanup)
  in
    ()

val compile_with_cleanup_oop : ah:AncHeap -> exp:BoolExp -> st:state ->
  Lemma (requires (zeroHeap st ah /\ disjoint (elts ah) (vars exp)))
        (ensures  (zeroHeap (compileBexpCleanEvalSt_oop ah exp st)
                            (first (compileBexpClean_oop ah exp)) /\
                   compileBexpCleanEval_oop ah exp st =
                     compileBexpEval_oop ah exp st))
let compile_with_cleanup_oop ah exp st =
  let (ah', targ) = popMin ah in
    compile_with_cleanup ah' targ exp st
