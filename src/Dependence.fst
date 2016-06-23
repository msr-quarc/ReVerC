module Dependence

open Util
open AncillaHeap
open Circuit
open BoolExp

// Much of the semantics, optimizations, and compilation correctness will
// rely on the nodes being ordered. Let's make sure we assert orderedness

type CleanupType =
  | Bennett
  | Dependencies
  | Default

// Initial node has one outgoing and no incoming edges, terminal node
// has one incoming and no outgoing edges. A terminal node has value
// determined by the value of its incoming node. Intuitively we want the
// value of any terminal node to be false if the network is to be
// reversible.
type rID = nat
type rNode =
  | RInput
  | RInit
  | ROutput of rID
  | RTerm   of rID
  | RBexp   of BoolExp * rID

type depGraph = list rNode

// Membership, substitution utils
val occursInNode : rID -> rNode -> Tot bool
let occursInNode r node = match node with
  | RInput           -> false
  | RInit            -> false
  | ROutput r'       -> r = r'
  | RTerm r'         -> r = r'
  | RBexp (bexp, r') -> r = r' || occursInBexp r bexp

val occursInGraph : rID -> depGraph -> Tot bool
let rec occursInGraph r dg = match dg with
  | []    -> false
  | x::xs -> occursInNode r x || occursInGraph r xs

val rIDs : rNode -> Tot (set rID)
let rIDs node = fun i -> occursInNode i node

val mod : rID -> depGraph -> Tot bool
let rec mod r dg = match dg with
  | []               -> false
  | RInput::xs
  | RInit::xs        -> mod r xs
  | ROutput r'::xs
  | RTerm r'::xs
  | RBexp (_, r')::xs -> r = r' || mod r xs

val mods : depGraph -> Tot (set rID)
let mods dg = fun i -> mod i dg

// New definition of well-formedness: asserts the increasing nature of ids.
val lookupR : rid:rID -> dg:depGraph{List.length dg > rid} -> Tot rNode (decreases rid)
let rec lookupR rid dg =
  if rid <= 0
  then match dg with x::_  -> x
  else match dg with _::xs -> lookupR (rid-1) xs

val wfNode : rID -> rNode -> Tot bool
let wfNode rid node = match node with
  | RInput | RInit      -> true
  | ROutput r | RTerm r -> rid > r
  | RBexp (b, r)        -> rid > r && gtVars rid b

val wfGraphN : rID -> dg:depGraph -> Tot bool (decreases dg)
let rec wfGraphN n dg = match dg with
  | [] -> true
  | x::xs -> wfNode n x && wfGraphN (n+1) xs

type wfDG (rid:rID) (dg:depGraph) =
  forall (i:fin (List.length dg)). wfNode (i + rid) (Finite.lookup i dg)

val modPath : rid:rID -> dg:depGraph{List.length dg > rid /\ wfDG 0 dg} ->
//val modPath : rid:rID -> dg:depGraph{List.length dg > rid /\ wfGraphN 0 dg} -> *** Doesn't seem to work
  Tot (list rNode) (decreases rid)
let rec modPath rid dg = match Finite.lookup rid dg with
  | RInput    -> [RInput]
  | RInit     -> [RInit]
  | ROutput r -> (ROutput r)::(modPath r dg)
  | RTerm r   -> (RTerm r)::(modPath r dg)
  | RBexp (b, r) -> (RBexp (b, r))::(modPath r dg)

(*
val wfGraph : rid:rID -> dg:depGraph{wfGraphN} -> Tot bool
let rec wfGraph dg = match dg with
  | []                      -> true
  | (rid, RInput)::xs       -> wfGraph xs
  | (rid, RInit)::xs        -> wfGraph xs
  | (rid, ROutput r)::xs    -> not (occursInGraph rid xs) && wfGraph xs
  | (rid, RTerm r)::xs      -> not (occursInGraph rid xs) && wfGraph xs
  | (rid, RBexp (bexp, r))::xs -> not (occursInBexp r bexp) && wfGraph xs
*)
//val wfDG_tail : n:int -> x:rNode -> xs:depGraph
//type wfDepGraph = dg:depGraph{wfGraph dg}
(*
val substNode : rNode -> totMap rID int -> Tot rNode
let substNode (rid, node) sub =
  let node' = match node with
    | RInput       -> RInput
    | RInit        -> RInit
    | ROutput r    -> ROutput (sub r)
    | RTerm r      -> RTerm (sub r)
    | RBexp (bexp, r) -> RBexp (substBexp bexp sub) (sub r)
  in
    (rid, node')

val substGraph : depGraph -> totMap rID int -> Tot depGraph
let rec substGraph dg sub = match dg with
  | []              -> []
  | x::xs -> (substNode x sub)::(substGraph xs sub)
*)

// Definition of well formed graphs. Conditions needed for correctness
// 1. Boolean expressions are well formed
//    - target is not in the expression
// 2. Outputs are preserved
//    - Output is not modified in rest of computation
//    - Output us unused should work just as well/better
// 3. Terminals are false valued
//    - Path from init to terminal is palindromic
//    - Palindromes are identity
// 4. Terminals are unused
//    - Terminal does not occur in rest of computation
// (Probably not required for equivalence) 5. rIDs are strictly increasing

// This actually isn't strong enough. When we compile we map rIDs to a few
// qubits with redundancy. We need to:
//   1. Prove that two rIDs get mapped to the same bit if and only if
//      there is a mod path between them
//   2. Make well-formed graphs use mod paths rather than occursInNode
//   3. Make well-formed graphs have exactly one mod path for each node

// NOTE: this is a total version of lookups in dependence graphs. May want to
//   prove that this is OK: that is, we only generate dependence graphs with
//   self-contained rIDs

(*
val lookupRN : rid:rID -> n:rID -> dg:depGraph{wfGraphN n dg && List.length dg > rid} -> Tot rNode (decreases rid)
let rec lookupRN rid n dg =
  if rid = 0
  then match dg with x::_  -> x
  else match dg with _::xs -> lookupRN (rid-1) (n+1) xs

val lookupR : rid:rID -> dg:wfDepGraph{List.length dg > rid} -> Tot rNode
let lookupR rid dg = lookupRN rid 0 dg

// Can't prove this total. Failed attempt: make rID nat and refine the
//   depGraph type here to be decIDs
val modPath : rid:rID -> dg:depGraph{List.length dg > rid} -> Tot (list rNode) (decreases rid)
//val modPath : rID -> depGraph -> list rNode
let rec modPath rid dg = match lookupR rid dg with
  | RInput    -> [RInput]
  | RInit     -> [RInit]
  | ROutput r -> (ROutput r)::(modPath r dg)
  | RTerm r   -> (RTerm r)::(modPath r dg)
  | RBexp (b, r) -> (RBexp (b, r))::(modPath r dg)
*)

// Evaluation/semantics
val evalNode : rid:rID -> node:rNode{wfNode rid node} -> Finite.map rid bool ->
  Tot ((list rID) * (Finite.map (rid+1) bool))
let evalNode rid node st = match node with
  | RInput       -> admit () //([],    st)
  | RInit        -> ([],    upd rid false st)
  | ROutput r    -> ([rid], upd rid (find r st) st)
  | RTerm r      -> ([],    upd rid (find r st) st)
  | RBexp (bexp, r) ->
    let st_tot : state = fun i -> if i < 0 || i >= rid then false else find i st in
      ([], upd rid ((find r st) <> evalBexp bexp st_tot) st)

val evalGraph : rid:rID -> dg:depGraph{wfDG rid dg} -> Finite.map rid bool ->
  Tot ((list rID) * (Finite.map (rid+(List.length dg)) bool)) (decreases dg)
let rec evalGraph rid dg st = match dg with
  | [] -> ([], st)
  | x::xs ->
    let wfNode_x:unit -> Lemma (wfNode rid x) = admit () in
    let (outp, st')   = evalNode rid x st in
    let (outp', st'') = evalGraph (rid+1) xs st' in
      (outp@outp', st'')


// Compilation
// Version 1: Natural, defers substitution until bexp compilation
(*
type Ctx = totMap rID int
type compilerResult = AncHeap * Ctx * (list rID) * (list Gate)

val compileNode : AncHeap -> Ctx -> rNode -> Tot compilerResult
let compileNode ah ctx (rid, node) = match node with
  | RInput    -> (ah, ctx, [], [])
  | RInit     -> let (ah', a) = popMin ah in (ah', update ctx rid a, [], [])
  | ROutput r -> (ah, update ctx rid (ctx r), [rid], [])
  | RTerm r   -> (insert ah (ctx r), update ctx rid (ctx r), [], [])
  | RBexp (bexp, r) ->
    let bexp' = substBexp bexp ctx in
    let (ah', res, anc, circ) = compileBexpClean ah (ctx r) bexp' in
      (ah', update ctx rid res, [], circ)

val compileGraph : AncHeap -> Ctx -> dg:depGraph -> Tot compilerResult (decreases dg)
let rec compileGraph ah ctx dg = match dg with
  | [] -> (ah, ctx, [], [])
  | x::xs ->
    let (ah', ctx', outp, xcirc) = compileNode ah ctx x in
    let (ah'', ctx'', outp', xscirc) = compileGraph ah' ctx' xs in
      (ah'', ctx'', outp@outp', xcirc@xscirc)

// Verification
val compileAndEvalNode : AncHeap -> Ctx -> rNode -> state -> Tot bool
let compileAndEvalNode ah ctx (rid, node) st =
  let (ah', ctx', outp, circ) = compileNode ah ctx (rid, node) in
    (evalCirc circ st) (ctx' rid)

val compileAndEvalGraph : AncHeap -> Ctx -> depGraph -> state -> Tot state
let compileAndEvalGraph ah ctx dg st =
  let (ah', ctx', outp, circ) = compileGraph ah ctx dg in
    evalCirc circ st

(*
val compile_node_correct : ah:AncHeap -> ctx:Ctx -> rnode:rNode -> st:state ->
  Lemma (requires (zeroHeap st ah /\ (forall r. not (mem (ctx r) ah))))
        (ensures  ((evalNode node (fun i -> st (ctx i))) = (compileAndEvalNode ah (rid, node) ctx st)))
let compile_node_correct ah rid node ctx st = match node with
  | RInit        -> pop_is_zero st ah
  | RTerm r      -> ()
  | RBexp (bexp, r) ->
    let bexp' = subst bexp ctx in
    let (ah', res, anc, gates) = compileBexp ah (ctx r) bexp' in
      admitP(disjoint (elts ah) (vars bexp'));
      admitP(~(Util.mem (ctx r) (vars bexp')));
      compile_bexp_correct ah (ctx r) bexp' st;
      admitP(b2t (evalNode node (fun i -> st (ctx i)) = st (ctx r) <> evalBexp bexp' st))
*)
// Version 2: applies substitutions before entering compileNode
(*
val compileNode : AncHeap -> rNode -> Tot (AncHeap * int * (list int) * (list Gate))
let compileNode ah (rid, node) = match node with
  | RInput       -> (ah, rid, [], [])
  | RInit        -> let (ah', a) = popMin ah in (ah', a, [], [])
  | ROutput b    -> (ah, b, [b], [])
  | RTerm b      -> (insert ah b, b, [])
  | RBexp bexp b ->
    let (ah', res, anc, circ) = compileBexpClean ah b bexp in
      (ah', res, [], circ)

val compileGraph : AncHeap -> depGraph -> totMap rID int ->
  Tot (AncHeap * (totMap rID int) * (list int) * (list Gate))
let rec compileGraph ah dg ctx = match dg with
  | [] -> (ah, ctx, [], [])
  | (rid, node)::xs ->
    let (ah', res, xcirc) = compileNode ah (substNode node ctx) in
    let ctx' = update ctx rid res in
    let (ah'', ctx'', xscirc) = compileGraph ah xs ctx' in
      (ah'', ctx'', xcirc@xscirc)

val initCtx : list rID -> Tot ((totMap rID int) * int)
let initCtx inp =
  let emp = fun i -> -1 in
    List.fold_leftT (fun (ctx, i) rid -> (update ctx rid i, i+1)) (emp, 0) inp

val initSt : list rID -> state -> Tot (totMap rID bool)
let initSt inp st =
  let (ctx, n) = initCtx inp in
    fun r -> st (ctx r)

val compileCircuit : depGraph -> list rID -> list rID -> Tot (list Gate)
let compileCircuit dg inp outp =
  let (ctx, n) = initCtx inp in
  let (ah, ctx', circ) = compileGraph (above n) dg ctx in
    circ

// Verification

// Function composition
val pullbackSt : totMap rID int -> state -> Tot (totMap rID bool)
let pullbackSt ctx st = fun r -> st (ctx r)

val pullback_eq : ctx:totMap rID int -> st:state -> ctx':totMap rID int -> st':state ->
  Lemma (requires (ctx = ctx' /\ st = st'))
        (ensures  (pullbackSt ctx st = pullbackSt ctx' st'))
let pullback_eq ctx st ctx' st' = ()

// Functional correctness
val compileAndEvalNode : AncHeap -> rNode -> state -> Tot bool
let compileAndEvalNode ah node st =
  let (ah', res, circ) = compileNode ah node in
    (evalCirc circ st) res

val compileAndEvalGraph : AncHeap -> depGraph -> totMap rID int -> state -> Tot (totMap rID bool)
let compileAndEvalGraph ah dg ctx st =
  let (ah', ctx', circ) = compileGraph ah dg ctx in
  let st' = evalCirc circ st in
    fun r -> st' (ctx' r)

val compileAndEvalCirc : depGraph -> list rID -> list rID -> state -> Tot (totMap rID bool)
let compileAndEvalCirc dg inp outp st =
  let (ctx, n) = initCtx inp in
  let (ah, ctx', circ) = compileGraph (above n) dg ctx in
  let st' = evalCirc circ st in
    fun r -> st' (ctx' r)


val compile_node_correct : ah:AncHeap -> node:rNode -> st:state ->
  Lemma (requires (zeroHeap st ah /\ disjoint (elts ah) (ids node) /\ wfNode node))
        (ensures  (evalNode node st = compileAndEvalNode ah node st))
let compile_node_correct ah node st = match node with
  | RInit        -> pop_is_zero st ah
  | RTerm r      -> ()
  | RBexp (bexp, r) -> compile_bexp_correct ah r bexp st

val compile_graph_correct : ah:AncHeap -> dg:depGraph -> ctx:totMap rID int -> outp:list rID -> st:state ->
  Lemma (requires true) //(zeroHeap st ah /\ disjoint (elts ah) inp))
        (ensures  (agree_on (evalGraph dg (pullbackSt ctx st))
                            (compileAndEvalGraph ah dg ctx st)
                            (mems outp)))
let rec compile_graph_correct ah dg ctx outp st = match dg with
  | [] -> ()
  | (rid, node)::xs ->
    let (ah', res, xcirc) = compileNode ah node in
    let ctx' = update ctx rid res in
    let (ah'', ctx'', xscirc) = compileGraph ah' xs ctx' in
    let st' = evalCirc xcirc st in
    let ind_hyp_x =
      admitP(zeroHeap st ah /\ disjoint (elts ah) (ids node) /\ wfNode node);
      compile_node_correct ah node
    in
    let ind_hyp_xs =
      compile_graph_correct ah' xs ctx' outp st
    in
      evalCirc_append xcirc xscirc st;
      admitP(Util.mem rid (mems outp) ==> ~(Util.mem res (mods xscirc)));
      eval_mod st' xscirc

val compile_circuit_correct : dg:depGraph -> inp:list rID -> outp:list rID -> st:state ->
  Lemma (agree_on (evalGraph dg (pullbackSt (fst (initCtx inp)) st))
                  (compileAndEvalCirc dg inp outp st)
                  (mems outp))
let compile_circuit_correct dg inp outp st =
  let (ctx, n) = initCtx inp in
    compile_graph_correct (above n) dg ctx outp st

(*
val compile_graph_correct : ah:AncHeap -> dg:depGraph -> ctx:(totMap rID int) -> st:state -> inputs:set rID ->
  Lemma (requires (zeroHeap st ah))
        (ensures  (agree_on (evalGraph dg st) (compileAndEvalGraph ah dg ctx st) inputs))
let compile_graph_correct ah dg ctx st inputs = match dg with
  | [] -> ()
  | (rid, RInit)::xs -> admit ()
  | (rid, RTerm r)::xs -> compile_node_correct ah rid (RTerm r) ctx st; admit ()
  | _ -> admit ()
      //compile_bexp_correct ah (Some (Map.sel ctx r)) bexp st
*)
// Optimization passes
//let mergeBExp dg x = match x with
//  | BXor (BVar r1) (BVar r2) ->
//    match (lookup )
//let rec collectBExp_rec dg dg' = match dg' with
//  | [] -> dg
//  | (rid, RBoolexp bexp r)::xs -> collectBExp_rec (mergeBExp dg bexp r) xs
//  | x::xs -> coolectBExp_rec x::dg xs

// Transformation into Boolean expressions
//let nodeToBexp (rid, node) nodemap acc = match node with
//  | RInput i        -> update nodemap rid (BVar i)
//  | RInit           -> nodemap //update nodemap rid BFalse
//  | ROutput r i     -> update acc i (nodemap r)
//  | Rboolexp bexp r -> update nodemap rid (BXor (BVar r) bexp)

// Correctness
(*
let compileAndEvalNode ah rnode ctx st rid =
  let (ah', ctx', circ) = compileNode ah rnode ctx in
    (evalCirc circ st) (Map.sel ctx' rid)

let compileAndEvalGraph dg st =
  let (ah'', ctx'', circ) = compileGraph dg in
    (evalCirc)

val ind_hyp : ah:AncHeap -> res:(option int) -> bexp:BoolExp -> st:state ->
  Lemma (eval_bexp2 bexp st res = compile_and_eval_bexp ah res bexp st)
let ind_hyp = admit ()

val compile_node_correct : ah:AncHeap -> rnode:(rID * rNode) -> ctx:(Map.t rID int) -> st:state ->
  Lemma (requires (zeroHeap st ah /\ (forall r. not (mem (Map.sel ctx r) ah))))
        (ensures  (evalNode (snd rnode) (fun r -> st (Map.sel ctx r)) = (compileAndEvalNode ah rnode ctx st (fst rnode))))
let compile_node_correct ah (rid, node) ctx st =
  match node with
    | RInit -> pop_is_zero st ah
    | Rboolexp bexp r -> admit () //ind_hyp ah (Some (Map.sel ctx r)) bexp st

val compile_graph_correct : ah:AncHeap -> dg:depGraph -> ctx:(Map.t rID int) -> st:state ->
  Lemma (requires (zeroHeap st ah))
        (ensures  (evalGraph dg st = (compiledAndEvalGraph)))
let compile_graph_correct = admit ()
      //compile_bexp_correct ah (Some (Map.sel ctx r)) bexp st
*)

(* Dependence graph interpretation -- unfinished
type depGraphState = (int * int) * (depGraph * (Total.t address rID))

val depGraphInterp : interpretation depGraphState
let depGraphInterp fs ((atop, rtop), (nodes, dep)) = match fs with
  | Xor a1 a2 ->
    bind (lookup dep a1) (fun r1 ->
    bind (lookup dep a2) (fun r2 ->
      let nodes'  = (Rinit)::nodes in
      let nodes'' = (Rbexp (BXor (BVar r1) (BVar r2)) rtop)::nodes' in
        Val (atop, ((atop+1, rtop+2), (nodes'', update dep atop (rtop+1))))))
  | And a1 a2 ->
    bind (lookup dep a1) (fun r1 ->
    bind (lookup dep a2) (fun r2 ->
      let nodes'  = (Rinit)::nodes in
      let nodes'' = (Rbexp (BAnd (BVar r1) (BVar r2)) rtop)::nodes' in
        Val (atop, ((atop+1, rtop+2), (nodes'', update dep atop (rtop+1))))))
  | Not a ->
    bind (lookup dep a) (fun r ->
      let nodes'  = (Rinit)::nodes in
      let nodes'' = (Rbexp (BNot (BVar r)) rtop)::nodes' in
        Val (atop, ((atop+1, rtop+2), (nodes'', update dep atop (rtop+1)))))
  | Bl b ->
    let nodes' = (Rinit)::nodes in
    let (rtop', nodes'') = match b with
      | false -> (rtop, nodes')
      | true  -> (rtop+1, (Rbexp (BNot (BVar rtop)) rtop)::nodes')
    in
      Val (atop, ((atop+1, rtop'+1), (nodes'', update dep atop rtop')))
  | Asn a1 a2 -> bind (lookup dep a2) (fun r ->
    Val (atop, ((atop, rtop), (nodes, update dep a1 r))))
  | Cln a -> bind (lookup dep a) (fun r ->
    Val (atop, ((atop, rtop+1), ((Rterm r)::nodes, update dep a rtop))))

val computeGraph : GExpr -> result (valconfig depGraphState)
let computeGraph gexp = eval_rec (gexp, [], ((0, 0), ([], []))) depGraphInterp

*)
