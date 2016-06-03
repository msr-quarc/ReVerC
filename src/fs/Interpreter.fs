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

open Util
open BoolExp
open ExprTypes
open Total

(* A representation of program heap (which is Bool-typed) *)
type interpretation<'state> =
  { alloc      : 'state -> BoolExp -> (int * 'state);
    assign     : 'state -> int -> BoolExp -> 'state;
    clean      : 'state -> GExpr -> int -> 'state;
    assertion  : 'state -> GExpr -> int -> 'state;
    eval       : 'state -> Total.state -> int -> bool }

(* Values of the language *)
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

let isBexp tm = match tm with
  | LOC i     -> true
  | BEXP bexp -> true
  | BOOL b    -> true
  | _         -> false

type config<'state> = GExpr * 'state
type valconfig<'state> = GExpr * 'state
type listconfig<'state> = (list<GExpr>) * 'state

let get_bexp gexp = match gexp with
  | LOC i     -> BVar i
  | BEXP bexp -> bexp
  | BOOL b    -> if b then BNot BFalse else BFalse

(* Small-step evaluator *)
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
        | _ -> Err (FStar.String.strcat "Cannot reduce application: " (show tm))
      end
  | SEQUENCE (t1, t2) ->
    if not (isVal t1) then
      bindT (step (t1, st) interp) (fun (t1', st') -> Val (SEQUENCE (t1', t2), st'))
    else
      begin match t1 with
        | UNIT -> Val (t2, st)
        | _ -> Err (FStar.String.strcat "Cannot reduce sequence: " (show tm))
      end
  | ASSIGN (t1, t2) ->
    if not (isVal t1) then
      bindT (step (t1, st) interp) (fun (t1', st') -> Val (ASSIGN (t1', t2), st'))
    else if not (isBexp t2) then
      bindT (step (t2, st) interp) (fun (t2', st') -> Val (ASSIGN (t1, t2'), st'))
    else
      begin match t1 with
        | LOC l -> Val (UNIT, interp.assign st l (get_bexp t2))
        | _ -> Err (FStar.String.strcat "Cannot reduce assignment: " (show tm))
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
      bindT (step (t1, st) interp) (fun (t1', st') -> Val (APPEND (t1', t2), st'))
    else if not (isVal t2) then
      bindT (step (t2, st) interp) (fun (t2', st') -> Val (APPEND (t1, t2'), st'))
    else
      begin match (t1, t2) with
        | (ARRAY l, ARRAY l') -> Val (ARRAY (l@l'), st)
        | _ -> Err (FStar.String.strcat "Cannot reduce append: " (show tm))
      end
  | ROT (i, t) ->
    if not (isVal t) then
      bindT (step (t, st) interp) (fun (t', st') -> Val (ROT (i, t'), st'))
    else
      begin match t with
        | ARRAY lst ->
          if (0 <= i && i < FStar.List.length lst) then
            Val (ARRAY (rotate lst i), st)
          else
            Err (FStar.String.strcat "Array out of bounds: " (show tm))
        | _ -> Err (FStar.String.strcat "Cannot reduce rotation: " (show tm))
      end
  | SLICE (t, i, j) ->
    if not (isVal t) then
      bindT (step (t, st) interp) (fun (t', st') -> Val (SLICE (t', i, j), st'))
    else
      begin match t with
        | ARRAY lst ->
          if (0 <= i && i <= j && j < FStar.List.length lst) then
            Val (ARRAY (slice lst i j), st)
          else
            Err (FStar.String.strcat "Array out of bounds: " (show tm))
        | _ -> Err (FStar.String.strcat "Cannot reduce slice: " (show tm))
      end
  | ARRAY lst ->
    bindT (step_lst (lst, st) interp) (fun (lst, st') -> Val (ARRAY lst, st'))
  | GET_ARRAY (t, i) ->
    if not (isVal t) then
      bindT (step (t, st) interp) (fun (t', st') -> Val (GET_ARRAY (t', i), st'))
    else
      begin match t with
        | ARRAY lst ->
          if (0 <= i && i < FStar.List.length lst) then
            Val (FStar.List.nth lst i, st)
          else
            Err (FStar.String.strcat "Array out of bounds: " (show tm))
        | _ -> Err (FStar.String.strcat "Cannot reduce array index: " (show tm))
      end
  | CLEAN (t, torig) ->
    if not (isVal t) then
      bindT (step (t, st) interp) (fun (t', st') -> Val (CLEAN (t', torig), st'))
    else
      begin match t with
        | LOC l -> Val (UNIT, interp.clean st torig l)
        | ARRAY lst -> Val (UNIT, List.fold (fun st l -> interp.clean st torig l) st (List.map (fun v -> match v with | LOC l -> l | _ -> 0) lst))
      end
  | ASSERT (t, torig) ->
    if not (isVal t) then
      bindT (step (t, st) interp) (fun (t', st') -> Val (ASSERT (t', torig), st'))
    else
      begin match t with
        | LOC l -> Val (UNIT, interp.assertion st torig l)
        | _ -> Err (FStar.String.strcat "Cannot reduce assertion: " (show tm))
      end
  | BEXP bexp ->
    let (l, st') = interp.alloc st bexp in Val (LOC l, st')
  | _ -> Err (FStar.String.strcat "No rule applies: " (show tm))
and step_lst (lst, st) interp = match lst with
  | [] -> Val ([], st)
  | x::xs ->
    if not (isVal x) then
      bindT (step (x, st) interp) (fun (x', st') -> Val (x'::xs, st'))
    else
      bindT (step_lst (xs, st) interp) (fun (xs', st') -> Val (x::xs', st'))

(* Big-step evaluator. More efficient but not (proven) total *)
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
      | _ -> Err ("LHS is not a lambda: " ^ (show tm))
    end))
  | SEQUENCE (t1, t2) ->
    bind (eval_rec (t1, st) interp)  (fun (v1, st') ->
      eval_rec (t2, st') interp)
  | ASSIGN (t1, t2) ->
    bind (eval_rec (t1, st) interp)  (fun (v1, st') ->
    bind (eval_rec (t2, st') interp) (fun (v2, st'') ->
    begin match (v1, v2) with
      | (LOC l, BEXP bexp) -> Val (UNIT, interp.assign st' l bexp)
      | _ -> Err ("Invalid parameters: " ^ (show tm))
    end))
  | XOR _ | AND _ | BOOL _ ->
    bind (eval_to_bexp (tm, st) interp) (fun c -> eval_rec c interp)
  | APPEND (t1, t2) ->
    bind (eval_rec (t1, st) interp)  (fun (v1, st') ->
    bind (eval_rec (t2, st') interp) (fun (v2, st'') ->
    begin match (v1, v2) with
      | (ARRAY l1, ARRAY l2) -> Val (ARRAY (l1@l2), st'')
      | _ -> Err ("Append of non-array argument: " ^ (show tm))
    end))
  | ROT (i, t) ->
    bind (eval_rec (t, st) interp) (fun (v, st') ->
    begin match v with
      | ARRAY lst ->
        if (0 <= i && i < List.length lst)
        then Val (ARRAY (rotate lst i), st')
        else Err ("Rotation out of array bounds: " ^ (show tm))
      | _ -> Err ("Rotation of non-array argument: " ^ (show tm))
    end)
  | SLICE (t, i, j) ->
    bind (eval_rec (t, st) interp) (fun (v, st') ->
    begin match v with
      | ARRAY lst ->
        if (0 <= i && i <= j && j < List.length lst)
        then Val (ARRAY (slice lst i j), st')
        else Err ("Invalid slice bounds: " ^ (show tm))
      | _ -> Err ("Slice of non-array argument: " ^ (show tm))
    end)
  | ARRAY tlst ->
    let f (acc, st) t =
      bind (eval_rec (t, st) interp) (fun (v, st') ->
      begin match v with
        | LOC l -> Val (v::acc, st')
        | _ -> Err ("Array argument not boolean: " ^ (show t))
      end)
    in
    bind (foldM f ([], st) tlst) (fun (llst, st') ->
      Val (ARRAY (List.rev llst), st'))
  | GET_ARRAY (t, i) ->
    bind (eval_rec (t, st) interp) (fun (v, st') ->
    begin match v with
      | ARRAY lst ->
        if (0 <= i && i < List.length lst) then
          match List.nth lst i with
            | LOC l -> Val (LOC l, st')
            | _ -> Err ("Impossible")
        else Err ("Array out of bounds: " ^ (show tm))
      | _ -> Err ("Invalid parameters: " ^ (show tm))
    end)
  | VAR x -> Val (tm, st)
  | CLEAN (t, t') ->
      bind (eval_rec (t, st) interp) (fun (v, st') ->
      begin match t with
        | LOC l -> Val (UNIT, interp.clean st t' l)
        | ARRAY lst -> Val (UNIT, List.fold (fun st l -> interp.clean st t' l) st (List.map (fun v -> match v with | LOC l -> l | _ -> 0) lst))
      end)
  | ASSERT (t, t') ->
    bind (eval_rec (t, st) interp) (fun (v, st') ->
    begin match v with
      | LOC l -> Val (UNIT, st')
      | _ -> Err ("Assert of non-boolean argument: " ^ (show tm))
    end)
  | BEXP bexp ->
    let (l, st') = interp.alloc st bexp in
      Val (LOC l, st')
  | _ -> Err ("Unimplemented case: " ^ (show tm))
and eval_to_bexp (tm, st) interp = match tm with
  | XOR (x, y) ->
    bind (eval_to_bexp (x, st) interp)  (fun (x', st') ->
    bind (eval_to_bexp (y, st') interp) (fun (y', st'') ->
    match (x', y') with
      | (BEXP b, BEXP b') -> Val (BEXP (BXor (b, b')), st'')
      | _ -> Err ("Could not reduce parameters to booleans: " ^ (show tm))))
  | AND (x, y) ->
    bind (eval_to_bexp (x, st) interp)  (fun (x', st') ->
    bind (eval_to_bexp (y, st') interp) (fun (y', st'') ->
    match (x', y') with
      | (BEXP b, BEXP b') -> Val (BEXP (BAnd (b, b')), st'')
      | _ -> Err ("Could not reduce parameters to booleans: " ^ (show tm))))
  | BOOL b ->
    if b then Val (BEXP (BNot BFalse), st) else  Val (BEXP BFalse, st)
  | _ ->
    bind (eval_rec (tm, st) interp) (fun (v, st') ->
    match v with
      | LOC l -> Val (BEXP (BVar l), st')
      | _ -> Err ("Could not reduce expression to boolean: " ^ (show tm)))

(** Interpretation domains *)

(* Boolean (standard) interpretation -- for running a Revs program *)
type boolState = int * (Total.t<int, bool>)

let boolInit = (0, constMap false)
let boolAlloc (top, st) bexp = (top, (top + 1, update st top (evalBexp bexp st)))
let boolAssign (top, st) l bexp = (top, update st l (evalBexp bexp st))
let boolEval (top, st) ivals i = lookup st i

let boolInterp = {
  alloc = boolAlloc;
  assign = boolAssign;
  clean = fun st t l -> st;
  assertion = fun st t l -> st;
  eval = boolEval
}

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
type BExpState = int * (Total.t<int, BoolExp>)

let bexpInit : BExpState = (0, constMap BFalse)
let bexpAlloc (top, st) bexp = (top, (top + 1, update st top (substBexp bexp (lookup st))))
let bexpAssign (top, st) l bexp = (top, update st l (substBexp bexp (lookup st)))
let bexpEval (top, st) ivals i = evalBexp (lookup st i) ivals

let bexpInterp = {
  alloc = bexpAlloc;
  assign = bexpAssign;
  clean = fun st t l -> st;
  assertion = fun st t l -> st;
  eval = bexpEval
}

type CleanupStrategy =
  | Pebbled
  | Boundaries
  | Bennett

let simps bexp = distributeAnds (simplify bexp)

let rec simploop bexp = 
  let bexp' = simps bexp
  if bexp' = bexp then bexp' else simploop bexp'

let rec allocN (locs, (top, st)) i =
  if i <= 0 then (List.rev locs, (top, st))
  else allocN (((LOC top)::locs), (top+1, update st top (BVar top))) (i-1)

let allocTy ty (top, st) = match ty with
  | GBool -> Val (LOC top, (top + 1, update st top (BVar top)))
  | GArray n ->
    let (locs, st') = allocN ([], (top, st)) n in
      Val (ARRAY locs, st')
  | _ -> Err "Invalid parameter type for circuit generation"

let rec lookupLst lst st = match lst with
  | [] -> []
  | (LOC l)::xs -> (lookup (snd st) l)::(lookupLst xs st)

open AncillaHeap
open Circuit

let foldPebble (ah, outs, anc, circ) bexp =
  let (ah', res, anc', circ') = compileBexpPebbled_oop ah (simps bexp) in
    (ah', res::outs, anc'@anc, circ@circ')

let foldClean (ah, outs, anc, circ) bexp =
  let (ah', res, anc', circ') = compileBexpClean_oop ah (simps bexp) in
    (ah', res::outs, anc'@anc, circ@circ')

let foldBennett (ah, outs, anc, circ, ucirc) bexp =
  let (ah', res, anc', circ') = compileBexp_oop ah (simps bexp) in
    (ah', res::outs, anc'@anc, circ@circ', (List.rev (uncompute circ' res))@ucirc)

(* Compilation wrapper. The main point of interest is its action when the
   program is a function. In that case it allocates some new free variables
   corresponding to the inputs of the function, then evaluates the function
   body. Note also that this wrapper is not verified currently. Eventually this
   should be done. *)
let rec compile (gexp, st) strategy =
  if isVal gexp then match gexp with
    | UNIT -> Val ([], [])
    | LAMBDA (x, ty, t) ->
      begin match allocTy ty st with
        | Err s -> Err s
        | Val (v, st') -> compile (substGExpr t x v, st') strategy
      end
    | LOC l ->
      let bexp = (simplify << distributeAnds) (lookup (snd st) l) in
      let max = varMax bexp in
      let (ah, res, anc, circ) = match strategy with
        | Pebbled -> compileBexpPebbled_oop (above (max+1)) (simps bexp)
        | Boundaries -> compileBexpClean_oop (above (max+1)) (simps bexp)
        | Bennett -> compileBexpClean_oop (above (max+1)) (simps bexp)
      in
        Val ([res], circ)
    | ARRAY lst ->
      let cmp x y = 
        let xd = andDepth x in
        let yd = andDepth y in
          if xd < yd then 1 else if xd = yd then 0 else -1
      in
      let blst' = List.map (fun x -> fromESOP (toESOP x)) (lookupLst lst st) in
      let blst = List.sortWith cmp blst' in
      let max = listMax (List.map varMax blst) in
      let (ah, outs, anc, circ) = match strategy with
        | Pebbled ->
          let (ah, outs, anc, circ) =
            List.fold foldPebble (above (max+1), [], [], []) blst
          in
            (ah, List.rev outs, List.rev anc, circ)
        | Boundaries ->
          let (ah, outs, anc, circ) =
            List.fold foldClean (above (max+1), [], [], []) blst
          in
            (ah, List.rev outs, List.rev anc, circ)
        | Bennett ->
          let (ah, outs, anc, circ, ucirc) =
            List.fold foldBennett (above (max+1), [], [], [], []) blst
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
type circState = int * AncHeap * (list<Gate>) * (Total.t<int, int>) * (Total.t<int, bool>)

let circInit : circState = (0, emptyHeap, [], constMap 0, constMap true)
let circAlloc (top, ah, circ, st, cl) bexp = match simplify (substVar bexp (lookup st)) with
    | BFalse ->
        let (ah', bit) = popMin ah in
        (top, (top+1, ah', circ, update st top bit, update cl bit true))
    | _ ->
        let (ah', res, ancs, circ') = compileBexpPebbled_oop ah (simplify (substVar bexp (lookup st))) in
        (top, (top+1, ah', circ@circ', update st top res, update cl res false))
let circAssign (top, ah, circ, st, cl) l bexp =
  let l' = lookup st l in
  let bexp' = simplify (substVar bexp (lookup st)) in
  match factorAs bexp' l' with
    | Some bexp'' ->
      let (ah', res, ancs, circ') = compileBexpPebbled ah l' (simplify bexp'') in
      (top, ah', circ@circ', update st l res, update cl l' false)
    | None ->
      if (lookup cl l' = true) then
        let (ah', res, ancs, circ') = compileBexpPebbled ah l' bexp' in
        (top, ah', circ@circ', update st l res, update cl l' false)
      else 
        let (ah', res, ancs, circ') = compileBexpPebbled_oop ah bexp' in
        (top, ah', circ@circ', update st l res, update cl res false)
let circClean (top, ah, circ, st, cl) _ l = 
    let bit = lookup st l in
    (top, insert ah bit, circ, st, update cl bit true)
let circEval (top, ah, circ, st, cl) ivals i = lookup (evalCirc circ ivals) (lookup st i)

let circInterp = {
  alloc = circAlloc;
  assign = circAssign;
  clean = circClean;
  assertion = fun st t l -> st;
  eval = circEval
}

let rec allocNcirc (locs, (top, ah, circ, st, cl)) i =
  if i <= 0 then (List.rev locs, (top, ah, circ, st, cl))
  else
    let (ah', res) = popMin ah in
      allocNcirc (((LOC top)::locs), (top+1, ah', circ, update st top res, update cl res false)) (i-1)

let allocTycirc ty (top, ah, circ, st, cl) = match ty with
  | GBool ->
    let (ah', res) = popMin ah in
      Val (LOC top, (top + 1, ah', circ, update st top res, update cl res false))
  | GArray n ->
    let (locs, st') = allocNcirc ([], (top, ah, circ, st, cl)) n in
      Val (ARRAY locs, st')
  | _ -> Err "Invalid parameter type for circuit generation"

let rec lookup_Lst st lst = match lst with
  | [] -> []
  | (LOC l)::xs -> (lookup st l)::(lookup_Lst st xs)

let rec compileCirc (gexp, (top, ah, circ, st, cl)) =
  if isVal gexp then match gexp with
    | UNIT -> Val ([], [])
    | LAMBDA (x, ty, t) ->
      begin match allocTycirc ty (top, ah, circ, st, cl) with
        | Err s -> Err s
        | Val (v, st') -> compileCirc (substGExpr t x v, st')
      end
    | LOC l ->
      let res = lookup st l in
        Val ([res], circ)
    | ARRAY lst ->
      let res = lookup_Lst st lst in
        Val (res, circ)
  else match (step (gexp, (top, ah, circ, st, cl)) circInterp) with
    | Err s -> Err s
    | Val c' -> compileCirc c'

(* Garbage-collected reversible circuit compilation -- experimental *)
type qubit =
  { id   : int;
    ival : BoolExp;
    cval : BoolExp;
    modi : bool }

let nullq = { id = 0; ival = BFalse; cval = BFalse; modi = false }
let get_subst m = fun i -> (Partial.find_def m i nullq).id
let data_q i = { id = i; ival = BVar i; cval = BFalse; modi = false }
let anc_q i  = { id = i; ival = BFalse; cval = BFalse; modi = false }

type circGCState =
  { top    : int;
    ah     : AncHeap;
    gates  : list<Gate>;
    symtab : Partial.t<int,qubit> }

// The garbage collector needs to:
//  -compile the current value in place (i.e. ival + cval + cval = ival),
//  -if the qubit is an ancilla, push it back onto the heap, and
//  -update the current value of all other bits by substituting q.id with ival + cval
let garbageCollect cs q =
  if q.modi = true then cs else
  let (ah', res, ancs, circ) = compileBexp cs.ah q.id q.cval in
  let ah'' = if q.ival = BFalse then insert ah' q.id else ah' in
  let f q' = 
    let subq = fun v -> if v = q.id then BXor (q.ival, q.cval) else BVar v in
    { id = q'.id; 
      ival = q'.ival; 
      cval = q'.cval; //simplify (substBexp q'.cval subq); 
      modi = q'.modi || occursInBexp q.id q'.cval }
  in
  let symtab' = Partial.mapVals f cs.symtab in
  { top = cs.top; 
    ah = ah''; 
    gates = cs.gates @ circ; 
    symtab = symtab' }

let circGCInit = { top = 0; ah = emptyHeap; gates = []; symtab = Partial.empty }
let circGCAlloc cs bexp = 
  let bexp' = simplify (substVar bexp (get_subst cs.symtab)) in
  let (ah', bit) = popMin cs.ah in
  let (ah'', res, ancs, circ') = compileBexp ah' bit bexp' in
  let q = { id = bit; ival = BFalse; cval = bexp'; modi = false } in
  let top' = cs.top + 1 in
  let gates' = cs.gates @ circ' in
  let symtab' = Partial.update cs.symtab cs.top q in
  (cs.top, {top = top'; ah = ah''; gates = gates'; symtab = symtab'})
let circGCAssign cs l bexp =
  let q = Partial.find_def cs.symtab l nullq in
  let bexp' = simplify (substVar bexp (get_subst cs.symtab)) in
  let bexpfac = factorAs bexp' q.id in
  match (q.cval, bexpfac) with
    | (BFalse, _)      -> // substitute q.id with BFalse, compile in place
      let bexp'' = substBexp bexp' (fun v -> if v = q.id then BFalse else BVar v) in
      let (ah', res, ancs, circ) = compileBexp cs.ah q.id bexp'' in
      let q' = { id = q.id; ival = q.ival; cval = bexp''; modi = false } in
      let f b = 
        let subq = fun v -> if v = q.id then bexp'' else BVar v in
        { id = b.id; 
          ival = b.ival; 
          cval = b.cval; //simplify (substBexp b.cval subq); 
          modi = b.modi || occursInBexp q.id b.cval }
      in
      let symtab' = Partial.update (Partial.mapVals f cs.symtab) l q' in
        {top = cs.top; ah = ah'; gates = cs.gates @ circ; symtab = symtab' }
    | (_, Some bexp'') -> // compile in place, substitute q.id with q.id \oplus bexp''
      let (ah', res, ancs, circ') = compileBexp cs.ah q.id bexp'' in
      let q' = { id = q.id; ival = q.ival; cval = simplify (BXor (q.cval, bexp'')); modi = false } in
      let f b = 
        let subq = fun v -> if v = q.id then BXor (BVar q.id, bexp'') else BVar v in
        { id = b.id; 
          ival = b.ival; 
          cval = b.cval; //simplify (substBexp b.cval subq); 
          modi = b.modi || occursInBexp q.id b.cval }
      in
      let symtab' = Partial.update (Partial.mapVals f cs.symtab) l q' in
        {top = cs.top; ah = ah'; gates = cs.gates @ circ'; symtab = symtab' }
    | _                -> // Compile out of place, clean q.id
      let (ah', res, ancs, circ') = compileBexp_oop cs.ah bexp' in
      let q' = { id = res; ival = BFalse; cval = bexp'; modi = false } in
      let cs' = { top = cs.top; ah = ah'; gates = cs.gates @ circ'; symtab = Partial.update cs.symtab l q' } in
        garbageCollect cs' q
let circGCClean cs _ l = 
    let bit = Partial.find_def cs.symtab l nullq in
    let q' = { id = bit.id; ival = BFalse; cval = BFalse; modi = false } in
    { top = cs.top; ah = insert cs.ah bit.id; gates = cs.gates; symtab = Partial.update cs.symtab l q' }
let circGCEval cs st i = false

let circGCInterp = {
  alloc = circGCAlloc;
  assign = circGCAssign;
  clean = circGCClean;
  assertion = fun st t l -> st;
  eval = circGCEval
}

let rec allocNcircGC (locs, cs) i =
  if i <= 0 then (List.rev locs, cs)
  else
    let (ah', res) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                symtab = Partial.update cs.symtab cs.top (data_q res) }
    in
      allocNcircGC (((LOC cs.top)::locs), cs') (i-1)

let allocTycircGC ty cs = match ty with
  | GBool ->
    let (ah', res) = popMin cs.ah in
    let cs' = { top = cs.top + 1;
                ah = ah';
                gates = cs.gates;
                symtab = Partial.update cs.symtab cs.top (data_q res) }
    in
      Val (LOC cs.top, cs')
  | GArray n ->
    let (locs, st') = allocNcircGC ([], cs) n in
      Val (ARRAY locs, st')
  | _ -> Err "Invalid parameter type for circuit generation"

let rec lookup_Lst_gc symtab lst = match lst with
  | [] -> []
  | (LOC l)::xs -> ((Partial.find_def symtab l nullq).id)::(lookup_Lst_gc symtab xs)

let findGarbage gexp cs = Set.diff (Partial.keys cs.symtab) (locs gexp)

let garbageCollector gexp cs = 
  let garbage = findGarbage gexp cs in
  let f cs l = 
    let q = Partial.find_def cs.symtab l nullq in
    let cs' = garbageCollect cs q in
    { top = cs'.top; ah = cs'.ah; gates = cs'.gates; symtab = Partial.remove cs'.symtab l }
  Set.fold f cs garbage

let rec compileGCCirc (gexp, cs) =
  let cs = garbageCollector gexp cs in
  if isVal gexp then match gexp with
    | UNIT -> Val ([], [])
    | LAMBDA (x, ty, t) ->
      begin match allocTycircGC ty cs with
        | Err s -> Err s
        | Val (v, cs') -> compileGCCirc (substGExpr t x v, cs')
      end
    | LOC l ->
      let res = Partial.find_def cs.symtab l nullq in
        Val ([res.id], cs.gates)
    | ARRAY lst ->
      let res = lookup_Lst_gc cs.symtab lst in
        Val (res, cs.gates)
  else match (step (gexp, cs) circGCInterp) with
    | Err s -> Err s
    | Val c' -> compileGCCirc c'
