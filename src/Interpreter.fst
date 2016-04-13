(** Program interpreter and domains *)
module Interpreter

(* The main compiler module. Defines two interpreters based on either big step
   or small step style reductions. The interpreters use an interpretation of
   the heap to handle allocation and assignment of new Boolean values.
   There are currently three main interpretations: Boolean values (i.e. program
   evaluation), Boolean expressions (classical Boolean circuits), and
   reversible circuits.
   Correctness is proven by proving that two states which are equal under the
   given semantics (eval function) remain equal after an allocation or
   assignment. *)

open Set
open Util
open BoolExp
open ExprTypes
open Total

(* A representation of program heap (which is Bool-typed) *)
type interpretation (state:Type) =
  { alloc  : state -> BoolExp -> Tot (int * state);
    assign : state -> int -> BoolExp -> Tot state;
    eval   : state -> Total.state -> int -> Tot bool }

(* Values of the language *)
val isVal : gexp:GExpr -> Tot bool (decreases %[gexp;1])
val isVal_lst : lst:list GExpr -> Tot bool (decreases %[lst;0])
let rec isVal tm = match tm with
  | UNIT          -> true
  | LAMBDA (s, ty, t) -> true
  | LOC i         -> true
  | ARRAY lst     -> isVal_lst lst
  | _             -> false
and isVal_lst lst = match lst with
  | [] -> true
  | (LOC l)::xs -> isVal_lst xs
  | _ -> false

val isBexp : GExpr -> Tot bool
let isBexp tm = match tm with
  | LOC i     -> true
  | BEXP bexp -> true
  | BOOL b    -> true
  | _         -> false

type config     (state:Type) = GExpr * state
type valconfig  (state:Type) = c:(config state){isVal (fst c)}
type listconfig (state:Type) = (list GExpr) * state

val get_bexp : gexp:GExpr{isBexp gexp} -> Tot BoolExp
let get_bexp gexp = match gexp with
  | LOC i     -> BVar i
  | BEXP bexp -> bexp
  | BOOL b    -> if b then BNot BFalse else BFalse

(* Small-step evaluator *)
val step : #state:Type -> c:config state -> interpretation state ->
  Tot (result (config state)) (decreases %[(fst c);1])
val step_lst : #state:Type -> c:listconfig state -> interpretation state ->
  Tot (result (listconfig state)) (decreases %[(fst c);0])
let rec step (tm, st) interp = match tm with
  | LET (x, t1, t2) ->
    if isVal t1
    then Val (substGExpr t2 x t1, st)
    else bindT (step (t1, st) interp) (fun (t1', st') -> Val (LET (x, t1', t2), st'))
  | APPLY (t1, t2) ->
    if not (isVal t1) then
      bindT (step (t1, st) interp) (fun (t1', st') -> Val (APPLY (t1', t2), st'))
    else if not (isVal t2) then
      bindT (step (t2, st) interp) (fun (t2', st') -> Val (APPLY (t1, t2'), st'))
    else
      begin match t1 with
        | LAMBDA (x, ty, t) -> Val (substGExpr t x t2, st)
        | _ -> Err (String.strcat "Cannot reduce application: " (show tm))
      end
  | SEQUENCE (t1, t2) ->
    if not (isVal t1) then
      bindT (step (t1, st) interp) (fun (t1', st') -> Val (SEQUENCE (t1', t2), st'))
    else
      begin match t1 with
        | UNIT -> Val (t2, st)
        | _ -> Err (String.strcat "Cannot reduce sequence: " (show tm))
      end
  | ASSIGN (t1, t2) ->
    if not (isVal t1) then
      bindT (step (t1, st) interp) (fun (t1', st') -> Val (ASSIGN (t1', t2), st'))
    else if not (isBexp t2) then
      bindT (step (t2, st) interp) (fun (t2', st') -> Val (ASSIGN (t1, t2'), st'))
    else
      begin match t1 with
        | LOC l -> Val (UNIT, interp.assign st l (get_bexp t2))
        | _ -> Err (String.strcat "Cannot reduce assignment: " (show tm))
      end
  | XOR (t1, t2) ->
    if not (isBexp t1) then
      bindT (step (t1, st) interp) (fun (t1', st') -> Val (XOR (t1', t2), st'))
    else if not (isBexp t2) then
      bindT (step (t2, st) interp) (fun (t2', st') -> Val (XOR (t1, t2'), st'))
    else
      Val (BEXP (BXor (get_bexp t1, get_bexp t2)), st)
  | AND (t1, t2) ->
    if not (isBexp t1) then
      bindT (step (t1, st) interp) (fun (t1', st') -> Val (AND (t1', t2), st'))
    else if not (isBexp t2) then
      bindT (step (t2, st) interp) (fun (t2', st') -> Val (AND (t1, t2'), st'))
    else
      Val (BEXP (BAnd (get_bexp t1, get_bexp t2)), st)
  | BOOL b ->
    let bexp = if b then BNot BFalse else BFalse in
      Val (BEXP bexp, st)
  | APPEND (t1, t2) ->
    if not (isVal t1) then
      bindT (step (t1, st) interp) (fun (t1', st') -> Val (APPLY (t1', t2), st'))
    else if not (isVal t2) then
      bindT (step (t2, st) interp) (fun (t2', st') -> Val (APPLY (t1, t2'), st'))
    else
      begin match (t1, t2) with
        | (ARRAY l, ARRAY l') -> Val (ARRAY (l@l'), st)
        | _ -> Err (String.strcat "Cannot reduce append: " (show tm))
      end
  | ROT (i, t) ->
    if not (isVal t) then
      bindT (step (t, st) interp) (fun (t', st') -> Val (ROT (i, t'), st'))
    else
      begin match t with
        | ARRAY lst ->
          if (0 <= i && i < List.lengthT lst) then
            Val (ARRAY (rotate lst i), st)
          else
            Err (String.strcat "Array out of bounds: " (show tm))
        | _ -> Err (String.strcat "Cannot reduce rotation: " (show tm))
      end
  | SLICE (t, i, j) ->
    if not (isVal t) then
      bindT (step (t, st) interp) (fun (t', st') -> Val (SLICE (t', i, j), st'))
    else
      begin match t with
        | ARRAY lst ->
          if (0 <= i && i <= j && j < List.lengthT lst) then
            Val (ARRAY (slice lst i j), st)
          else
            Err (String.strcat "Array out of bounds: " (show tm))
        | _ -> Err (String.strcat "Cannot reduce slice: " (show tm))
      end
  | ARRAY lst ->
    bindT (step_lst (lst, st) interp) (fun (lst, st') -> Val (ARRAY lst, st'))
  | GET_ARRAY (t, i) ->
    if not (isVal t) then
      bindT (step (t, st) interp) (fun (t', st') -> Val (GET_ARRAY (t', i), st'))
    else
      begin match t with
        | ARRAY lst ->
          if (0 <= i && i < List.lengthT lst) then
            Val (nthT lst i, st)
          else
            Err (String.strcat "Array out of bounds: " (show tm))
        | _ -> Err (String.strcat "Cannot reduce array index: " (show tm))
      end
  | ASSERT t ->
    if not (isVal t) then
      bindT (step (t, st) interp) (fun (t', st') -> Val (ASSERT t', st'))
    else
      begin match t with
        | LOC l -> Val (UNIT, st)
        | _ -> Err (String.strcat "Cannot reduce assertion: " (show tm))
      end
  | BEXP bexp ->
    let (l, st') = interp.alloc st bexp in Val (LOC l, st')
  | _ -> Err (String.strcat "No rule applies: " (show tm))
and step_lst (lst, st) interp = match lst with
  | [] -> Val ([], st)
  | x::xs ->
    if not (isVal x) then
      bindT (step (x, st) interp) (fun (x', st') -> Val (x'::xs, st'))
    else
      bindT (step_lst (xs, st) interp) (fun (xs', st') -> Val (x::xs', st'))

(* Big-step evaluator. More efficient but not (proven) total *)
val eval_rec : #state:Type -> config state -> interpretation state -> result (config state)
val eval_to_bexp : #state:Type -> config state -> interpretation state -> result (config state)
let rec eval_rec (tm, st) interp = match tm with
  | LET (x, t1, t2) ->
    bind (eval_rec (t1, st) interp) (fun (v1, st') ->
      eval_rec (substGExpr t2 x v1, st') interp)
  | LAMBDA (x, ty, t) -> Val (tm, st)
  | APPLY (t1, t2) ->
    bind (eval_rec (t1, st) interp)  (fun (v1, st') ->
    bind (eval_rec (t2, st') interp) (fun (v2, st'') ->
    begin match v1 with
      | LAMBDA (x, ty, t) -> eval_rec (substGExpr t x v2, st'') interp
      | _ -> Err (String.strcat "LHS is not a lambda: " (show tm))
    end))
  | SEQUENCE (t1, t2) ->
    bind (eval_rec (t1, st) interp)  (fun (v1, st') ->
      eval_rec (t2, st') interp)
  | ASSIGN (t1, t2) ->
    bind (eval_rec (t1, st) interp)  (fun (v1, st') ->
    bind (eval_rec (t2, st') interp) (fun (v2, st'') ->
    begin match (v1, v2) with
      | (LOC l, BEXP bexp) -> Val (UNIT, interp.assign st' l bexp)
      | _ -> Err (String.strcat "Invalid parameters: " (show tm))
    end))
  | XOR _ | AND _ | BOOL _ ->
    bind (eval_to_bexp (tm, st) interp) (fun c -> eval_rec c interp)
  | APPEND (t1, t2) ->
    bind (eval_rec (t1, st) interp)  (fun (v1, st') ->
    bind (eval_rec (t2, st') interp) (fun (v2, st'') ->
    begin match (v1, v2) with
      | (ARRAY l1, ARRAY l2) -> Val (ARRAY (l1@l2), st'')
      | _ -> Err (String.strcat "Append of non-array argument: " (show tm))
    end))
  | ROT (i, t) ->
    bind (eval_rec (t, st) interp) (fun (v, st') ->
    begin match v with
      | ARRAY lst ->
        if (0 <= i && i < List.length lst)
        then Val (ARRAY (rotate lst i), st')
        else Err (String.strcat "Rotation out of array bounds: " (show tm))
      | _ -> Err (String.strcat "Rotation of non-array argument: " (show tm))
    end)
  | SLICE (t, i, j) ->
    bind (eval_rec (t, st) interp) (fun (v, st') ->
    begin match v with
      | ARRAY lst ->
        if (0 <= i && i <= j && j < List.length lst)
        then Val (ARRAY (slice lst i j), st')
        else Err (String.strcat "Invalid slice bounds: " (show tm))
      | _ -> Err (String.strcat "Slice of non-array argument: " (show tm))
    end)
  | ARRAY tlst ->
    let f (acc, st) t =
      bind (eval_rec (t, st) interp) (fun (v, st') ->
      begin match v with
        | LOC l -> Val (v::acc, st')
        | _ -> Err (String.strcat "Array argument not boolean: " (show t))
      end)
    in
    bind (foldM f ([], st) tlst) (fun (llst, st') ->
      Val (ARRAY (List.rev llst), st'))
  | GET_ARRAY (t, i) ->
    bind (eval_rec (t, st) interp) (fun (v, st') ->
    begin match v with
      | ARRAY lst ->
        if (0 <= i && i < List.length lst) then
          match List.total_nth lst i with
            | Some (LOC l) -> Val (LOC l, st')
            | Some _ -> Err ("Impossible")
            | None -> Err (String.strcat "Array out of bounds: " (show tm))
        else Err (String.strcat "Array out of bounds: " (show tm))
      | _ -> Err (String.strcat "Invalid parameters: " (show tm))
    end)
  | VAR x -> Val (tm, st)
  | ASSERT t ->
    bind (eval_rec (t, st) interp) (fun (v, st') ->
    begin match v with
      | LOC l -> Val (UNIT, st')
      | _ -> Err (String.strcat "Assert of non-boolean argument: " (show tm))
    end)
  | BEXP bexp ->
    let (l, st') = interp.alloc st bexp in
      Val (LOC l, st')
  | _ -> Err (String.strcat "Unimplemented case: " (show tm))
and eval_to_bexp (tm, st) interp = match tm with
  | XOR (x, y) ->
    bind (eval_to_bexp (x, st) interp)  (fun (x', st') ->
    bind (eval_to_bexp (y, st') interp) (fun (y', st'') ->
    match (x', y') with
      | (BEXP b, BEXP b') -> Val (BEXP (BXor (b, b')), st'')
      | _ -> Err (String.strcat "Could not reduce parameters to booleans: " (show tm))))
  | AND (x, y) ->
    bind (eval_to_bexp (x, st) interp)  (fun (x', st') ->
    bind (eval_to_bexp (y, st') interp) (fun (y', st'') ->
    match (x', y') with
      | (BEXP b, BEXP b') -> Val (BEXP (BAnd (b, b')), st'')
      | _ -> Err (String.strcat "Could not reduce parameters to booleans: " (show tm))))
  | BOOL b ->
    if b then Val (BEXP (BNot BFalse), st) else  Val (BEXP BFalse, st)
  | _ ->
    bind (eval_rec (tm, st) interp) (fun (v, st') ->
    match v with
      | LOC l -> Val (BEXP (BVar l), st')
      | _ -> Err (String.strcat "Could not reduce expression to boolean: " (show tm)))

(** Interpretation domains *)

(* Boolean (standard) interpretation -- for running a Revs program *)
type boolState = int * (Total.t int bool)

val boolInit   : boolState
val boolAlloc  : boolState -> BoolExp -> Tot (int * boolState)
val boolAssign : boolState -> int -> BoolExp -> Tot boolState
val boolEval   : boolState -> state -> int -> Tot bool

let boolInit = (0, constMap false)
let boolAlloc (top, st) bexp =
  (top, (top + 1, update st top (evalBexp bexp st)))
let boolAssign (top, st) l bexp =
  (top, update st l (evalBexp bexp st))
let boolEval (top, st) ivals i = lookup st i

let boolInterp = {
  alloc = boolAlloc;
  assign = boolAssign;
  eval = boolEval
}

val substVal : v:GExpr{isVal v} -> st:boolState -> Tot GExpr
val substVal_lst : v:(list GExpr){isVal_lst v} -> st:boolState -> Tot (list GExpr)
let rec substVal v st = match v with
  | UNIT | LAMBDA _ -> v
  | LOC l -> BOOL (lookup (snd st) l)
  | ARRAY lst -> ARRAY (substVal_lst lst st)
and substVal_lst lst st = match lst with
  | [] -> []
  | (LOC l)::xs -> (BOOL (lookup (snd st) l))::(substVal_lst xs st)

let rec evalBool (gexp, st) =
  if isVal gexp then prettyPrint (substVal gexp st)
  else match step (gexp, st) boolInterp with
    | Err s -> [s]
    | Val c' -> evalBool c'

let eval gexp = evalBool (gexp, boolInit)

(* Boolean expression interpretation -- for generating the fully
   inlined classical circuit of the Revs program *)
type BExpState = int * (Total.t int BoolExp)

val bexpInit   : BExpState
val bexpAlloc  : BExpState -> BoolExp -> Tot (int * BExpState)
val bexpAssign : BExpState -> int -> BoolExp -> Tot BExpState
val bexpEval   : BExpState -> state -> int -> Tot bool

let bexpInit = (0, constMap BFalse)
let bexpAlloc (top, st) bexp =
  (top, (top + 1, update st top (substBexp bexp st)))
let bexpAssign (top, st) l bexp =
  (top, update st l (substBexp bexp st))
let bexpEval (top, st) ivals i = evalBexp (lookup st i) ivals

let bexpInterp = {
  alloc = bexpAlloc;
  assign = bexpAssign;
  eval = bexpEval
}

type CleanupStrategy =
  | Pebbled : CleanupStrategy
  | Boundaries : CleanupStrategy
  | Bennett : CleanupStrategy

val simps : BoolExp -> Tot BoolExp
let simps bexp = simplify (distributeAnds bexp)

val allocN : list GExpr * BExpState -> i:int ->
  Tot (list GExpr * BExpState) (decreases i)
let rec allocN (locs, (top, st)) i =
  if i <= 0 then (List.rev locs, (top, st))
  else allocN (((LOC top)::locs), (top+1, update st top (BVar top))) (i-1)

val allocTy : GType -> BExpState -> Tot (result (GExpr * BExpState))
let allocTy ty (top, st) = match ty with
  | GBool -> Val (LOC top, (top + 1, update st top (BVar top)))
  | GArray n ->
    let (locs, st') = allocN ([], (top, st)) n in
      Val (ARRAY locs, st')
  | _ -> Err "Invalid parameter type for circuit generation"

val lookupLst : lst:(list GExpr){isVal_lst lst} -> st:BExpState -> Tot (list BoolExp)
let rec lookupLst lst st = match lst with
  | [] -> []
  | (LOC l)::xs -> (lookup (snd st) l)::(lookupLst xs st)

open AncillaHeap
open Circuit

val foldPebble : (AncHeap * list int * list int * list Gate) ->
  BoolExp -> Tot (AncHeap * list int * list int * list Gate)
let foldPebble (ah, outs, anc, circ) bexp =
  let (ah', res, anc', circ') = compileBexpPebbled_oop ah (simps bexp) in
    (ah', res::outs, anc'@anc, circ@circ')

val foldClean : (AncHeap * list int * list int * list Gate) ->
  BoolExp -> Tot (AncHeap * list int * list int * list Gate)
let foldClean (ah, outs, anc, circ) bexp =
  let (ah', res, anc', circ') = compileBexpClean_oop ah (simps bexp) in
    (ah', res::outs, anc'@anc, circ@circ')

val foldBennett : (AncHeap * list int * list int * list Gate * list Gate) ->
  BoolExp -> Tot (AncHeap * list int * list int * list Gate * list Gate)
let foldBennett (ah, outs, anc, circ, ucirc) bexp =
  let (ah', res, anc', circ') = compileBexp_oop ah (simps bexp) in
    (ah', res::outs, anc'@anc, circ@circ', (List.rev (uncompute circ' res))@ucirc)

(* Compilation wrapper. The main point of interest is its action when the
   program is a function. In that case it allocates some new free variables
   corresponding to the inputs of the function, then evaluates the function
   body. Note also that this wrapper is not verified currently. Eventually this
   should be done. *)
val compile : config BExpState -> CleanupStrategy -> Dv (result (list int * list Gate))
let rec compile (gexp, st) strategy =
  if isVal gexp then match gexp with
    | UNIT -> Val ([], [])
    | LAMBDA (x, ty, t) ->
      begin match allocTy ty st with
        | Err s -> Err s
        | Val (v, st') -> compile (substGExpr t x v, st') strategy
      end
    | LOC l ->
      let bexp = lookup (snd st) l in
      let max = varMax bexp in
      let (ah, res, anc, circ) = match strategy with
        | Pebbled -> compileBexpPebbled_oop (above (max+1)) (simps bexp)
        | Boundaries -> compileBexpClean_oop (above (max+1)) (simps bexp)
        | Bennett -> compileBexpClean_oop (above (max+1)) (simps bexp)
      in
        Val ([res], circ)
    | ARRAY lst ->
      let blst = lookupLst lst st in
      let max = listMax (List.mapT varMax blst) in
      let (ah, outs, anc, circ) = match strategy with
        | Pebbled ->
          let (ah, outs, anc, circ) =
            List.fold_leftT foldPebble (above (max+1), [], [], []) blst
          in
            (ah, List.rev outs, List.rev anc, circ)
        | Boundaries ->
          let (ah, outs, anc, circ) =
            List.fold_leftT foldClean (above (max+1), [], [], []) blst
          in
            (ah, List.rev outs, List.rev anc, circ)
        | Bennett ->
          let (ah, outs, anc, circ, ucirc) =
            List.fold_leftT foldBennett (above (max+1), [], [], [], []) blst
          in
            (ah, List.rev outs, List.rev anc, circ@ucirc)
      in
        Val (outs, circ)
  else match (step (gexp, st) bexpInterp) with
    | Err s -> Err s
    | Val c' -> compile c' strategy

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

(* Garbage-collected reversible circuit compilation -- experimental *)
(*
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


(* Dependence graph interpretation -- unfinished *)
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

(** Verification utilities *)

val step_preservation : 
  #state:Type -> #state':Type -> 
  gexp:GExpr -> st:state -> st':state' -> init:Total.t int bool ->
  pred:(state -> state' -> Total.t int bool -> Type) ->
  h1:(forall st st' init. pred st st' init ==> 
                        
  Lemma (requires (state_equiv st st' init))
        (ensures
          (is_Err (step (gexp, st) boolInterp) /\ is_Err (step (gexp, st') bexpInterp)) \/
          (is_Val (step (gexp, st) boolInterp) /\ is_Val (step (gexp, st') bexpInterp) /\
          (fst (getVal (step (gexp, st) boolInterp)) =
           fst (getVal (step (gexp, st') bexpInterp)) /\
          state_equiv (snd (getVal (step (gexp, st) boolInterp)))
                      (snd (getVal (step (gexp, st') bexpInterp)))
                      init)))
  (decreases %[gexp;1])
val step_preservation_lst : lst:list GExpr -> st:boolState -> st':BExpState -> init:state ->
  Lemma (requires (state_equiv st st' init))
        (ensures
          (is_Err (step_lst (lst, st) boolInterp) /\ is_Err (step_lst (lst, st') bexpInterp)) \/
          (is_Val (step_lst (lst, st) boolInterp) /\ is_Val (step_lst (lst, st') bexpInterp) /\
          (fst (getVal (step_lst (lst, st) boolInterp)) =
           fst (getVal (step_lst (lst, st') bexpInterp)) /\
          state_equiv (snd (getVal (step_lst (lst, st) boolInterp)))
                      (snd (getVal (step_lst (lst, st') bexpInterp)))
                      init)))
  (decreases %[lst;0])
let rec state_equiv_step gexp st st' init = match gexp with
  | LET (x, t1, t2) ->
    state_equiv_step t1 st st' init
  | LAMBDA (x, ty, t) -> ()
  | APPLY (t1, t2) ->
    state_equiv_step t1 st st' init;
    state_equiv_step t2 st st' init
  | SEQUENCE (t1, t2) ->
    state_equiv_step t1 st st' init
  | ASSIGN (t1, t2) ->
    state_equiv_step t1 st st' init;
    state_equiv_step t2 st st' init;
    if (isVal t1 && isBexp t2) then
      begin match t1 with
        | LOC l -> state_equiv_assign st st' init l (get_bexp t2)
        | _ -> ()
      end
  | XOR (t1, t2) ->
    state_equiv_step t1 st st' init;
    state_equiv_step t2 st st' init
  | AND (t1, t2) ->
    state_equiv_step t1 st st' init;
    state_equiv_step t2 st st' init
  | BOOL b -> ()
  | APPEND (t1, t2) ->
    state_equiv_step t1 st st' init;
    state_equiv_step t2 st st' init
  | ROT (i, t) ->
    state_equiv_step t st st' init
  | SLICE (t, i, j) ->
    state_equiv_step t st st' init
  | ARRAY lst ->
    state_equiv_step_lst lst st st' init
  | GET_ARRAY (t, i) ->
    state_equiv_step t st st' init
  | ASSERT t ->
    state_equiv_step t st st' init
  | BEXP bexp -> state_equiv_alloc st st' init bexp
  | _ -> ()
and state_equiv_step_lst lst st st' init = match lst with
  | [] -> ()
  | x::xs ->
    state_equiv_step x st st' init;
    state_equiv_step_lst xs st st' init

(* Originally this was done polymorphically (using a general notion of
   equivalence of states and a proof that the interpreter preserves equivalence
   if alloc and assign do). Eventually this should be refactored that way, but
   this was faster for the time being. *)
type state_equiv (st:boolState) (st':BExpState) (init:state) =
  fst st = fst st' /\ (forall i. boolEval st init i = bexpEval st' init i)

val state_equiv_impl : st:boolState -> st':BExpState -> init:state -> i:int ->
  Lemma (requires (state_equiv st st' init))
        (ensures  (boolEval st init i = bexpEval st' init i))
let state_equiv_impl st st' init i = ()

val eval_bexp_swap : st:boolState -> st':BExpState -> bexp:BoolExp -> init:state ->
  Lemma (requires (state_equiv st st' init))
        (ensures  (evalBexp (substBexp bexp (snd st')) init =
                   evalBexp bexp (snd st)))
let rec eval_bexp_swap st st' bexp init = match bexp with
  | BFalse -> ()
  | BVar i -> ()
  | BNot x -> (); eval_bexp_swap st st' x init
  | BXor (x, y) | BAnd (x, y) -> ();
    eval_bexp_swap st st' x init;
    eval_bexp_swap st st' y init

val state_equiv_alloc : st:boolState -> st':BExpState -> init:state -> bexp:BoolExp ->
  Lemma (requires (state_equiv st st' init))
        (ensures  (state_equiv (snd (boolAlloc st bexp)) (snd (bexpAlloc st' bexp)) init))
let state_equiv_alloc st st' init bexp = eval_bexp_swap st st' bexp init

val state_equiv_assign : st:boolState -> st':BExpState -> init:state -> l:int -> bexp:BoolExp ->
  Lemma (requires (state_equiv st st' init))
        (ensures  (state_equiv (boolAssign st l bexp) (bexpAssign st' l bexp) init))
let state_equiv_assign st st' init l bexp = eval_bexp_swap st st' bexp init

val state_equiv_step : gexp:GExpr -> st:boolState -> st':BExpState -> init:state ->
  Lemma (requires (state_equiv st st' init))
        (ensures
          (is_Err (step (gexp, st) boolInterp) /\ is_Err (step (gexp, st') bexpInterp)) \/
          (is_Val (step (gexp, st) boolInterp) /\ is_Val (step (gexp, st') bexpInterp) /\
          (fst (getVal (step (gexp, st) boolInterp)) =
           fst (getVal (step (gexp, st') bexpInterp)) /\
          state_equiv (snd (getVal (step (gexp, st) boolInterp)))
                      (snd (getVal (step (gexp, st') bexpInterp)))
                      init)))
  (decreases %[gexp;1])
val state_equiv_step_lst : lst:list GExpr -> st:boolState -> st':BExpState -> init:state ->
  Lemma (requires (state_equiv st st' init))
        (ensures
          (is_Err (step_lst (lst, st) boolInterp) /\ is_Err (step_lst (lst, st') bexpInterp)) \/
          (is_Val (step_lst (lst, st) boolInterp) /\ is_Val (step_lst (lst, st') bexpInterp) /\
          (fst (getVal (step_lst (lst, st) boolInterp)) =
           fst (getVal (step_lst (lst, st') bexpInterp)) /\
          state_equiv (snd (getVal (step_lst (lst, st) boolInterp)))
                      (snd (getVal (step_lst (lst, st') bexpInterp)))
                      init)))
  (decreases %[lst;0])
let rec state_equiv_step gexp st st' init = match gexp with
  | LET (x, t1, t2) ->
    state_equiv_step t1 st st' init
  | LAMBDA (x, ty, t) -> ()
  | APPLY (t1, t2) ->
    state_equiv_step t1 st st' init;
    state_equiv_step t2 st st' init
  | SEQUENCE (t1, t2) ->
    state_equiv_step t1 st st' init
  | ASSIGN (t1, t2) ->
    state_equiv_step t1 st st' init;
    state_equiv_step t2 st st' init;
    if (isVal t1 && isBexp t2) then
      begin match t1 with
        | LOC l -> state_equiv_assign st st' init l (get_bexp t2)
        | _ -> ()
      end
  | XOR (t1, t2) ->
    state_equiv_step t1 st st' init;
    state_equiv_step t2 st st' init
  | AND (t1, t2) ->
    state_equiv_step t1 st st' init;
    state_equiv_step t2 st st' init
  | BOOL b -> ()
  | APPEND (t1, t2) ->
    state_equiv_step t1 st st' init;
    state_equiv_step t2 st st' init
  | ROT (i, t) ->
    state_equiv_step t st st' init
  | SLICE (t, i, j) ->
    state_equiv_step t st st' init
  | ARRAY lst ->
    state_equiv_step_lst lst st st' init
  | GET_ARRAY (t, i) ->
    state_equiv_step t st st' init
  | ASSERT t ->
    state_equiv_step t st st' init
  | BEXP bexp -> state_equiv_alloc st st' init bexp
  | _ -> ()
and state_equiv_step_lst lst st st' init = match lst with
  | [] -> ()
  | x::xs ->
    state_equiv_step x st st' init;
    state_equiv_step_lst xs st st' init

// Correctness of circuit compilation
type circ_equiv (st:boolState) (cs:circState) (init:state) =
  fst st = cs.top /\
  zeroHeap (evalCirc cs.gates init) cs.ah /\
  (forall i. not (mem (lookup cs.subs i) cs.ah)) /\
  (forall i. boolEval st init i = circEval cs init i)

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
    admitP(disjoint (elts cs.ah) (vars bexp')); // Implied by circ_equiv proposition 3
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
        admitP(disjoint (elts cs.ah) (vars bexp')); // Implied by circ_equiv proposition 3
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
    | Some bexp'' ->
      admit(); // Need to redo
      (*
      let (ah', res, ancs, circ') = compileBexp cs.ah l' bexp'' in
      let zeroHeap_lem =
        factorAs_correct bexp' l' init';
        factorAs_vars bexp' l';
        compile_decreases_heap cs.ah l' bexp'';
        compile_partition cs.ah l' bexp'';
        zeroHeap_subset init' cs.ah cs'.ah;
        zeroHeap_st_impl init' cs'.ah circ'
      in
      let preservation =
        compile_mods cs.ah l' bexp'';
        eval_mod init' circ'
      in
      let correctness =
        admitP(b2t(lookup (snd st') l = lookup (evalCirc circ' init') (lookup cs'.subs l)));
        factorAs_correct bexp' l' init';
        eval_commutes_subst_circ st cs bexp bexp'' init l l'
      in *)
      ()

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
(*
  | ASSIGN (t1, t2) -> admit ()
    if      not (isVal t1)  then admit() //circ_equiv_step t1 st st' init
    else if not (isBexp t2) then admit() //circ_equiv_step t2 st st' init
    else
      begin match t1 with
        | LOC l -> admit()//; circ_equiv_assign st st' init l (get_bexp t2)
        | _ -> admit ()
      end *)
(*
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
  | BEXP bexp -> circ_equiv_alloc st st' init bexp *)
  | _ -> admit ()
and circ_equiv_step_lst lst st st' init = match lst with
  | [] -> ()
  | x::xs ->
    circ_equiv_step x st st' init;
    circ_equiv_step_lst xs st st' init
