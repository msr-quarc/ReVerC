module Equiv

open System
open RCircuit
open ExprTypes

open AncillaHeap
open GenOp

// File name prefixes for BDD printing
let cfname = "circuitBDD"
let pfname = "programBDD"

//module bdd = mlbdd
module bdd = Buddy

// Circuit evaluator
let circuitBDDs man gates n outputs =
    let bdds : bdd.t array = Array.init n (fun i -> if i >= List.head outputs then bdd.dfalse man else bdd.ithvar man i)
    let f gate = match gate with
        | RCNOT (x, y) -> bdds.[y] <- bdd.xor bdds.[x] bdds.[y]
        | RTOFF (x, y, z) -> bdds.[z] <- bdd.xor (bdd.dand bdds.[x] bdds.[y]) bdds.[z]
        | RHADAMARD _ -> failwith "Illegal Hadamard gate"
        | RNOT x -> bdds.[x] <- bdd.dnot bdds.[x]
    List.iter f gates;
    Array.toList bdds

// Monad stuff
type MaybeBuilder() =
    member this.Bind(x, f) = match x with
        | None -> None
        | Some a -> f a
    member this.Return(x) = 
        Some x
    member this.Zero() = None
   
let maybe = new MaybeBuilder()

let rec seq lst = match lst with
    | [] -> Some []
    | x::xs -> maybe {
        let! x' = x
        let! xs' = seq xs
        return x'::xs'
    }
let mapM f = seq << List.map f
let rec foldM f i lst = match lst with
    | [] -> Some i
    | x::xs -> maybe.Bind (f i x, fun m -> foldM f m xs)

(* Version 1
// BDD Interpreter internals

type id = string // Type of identifiers

// Values
type value =
    | Unit
    | Loc of int * int
    | Bool of bdd.t
    | Lam of id * GExpr

type heap = (int * bdd.t) list // Type of heaps
type env  = (id * value) list  // Type of environments

// Environment/heap accessors
let rec lookup lst v = match lst with
    | [] -> None
    | (x,y)::xs when x = v -> Some y
    | x::xs -> lookup xs v

let rec revLookup lst v = match lst with
    | [] -> None
    | (x,y)::xs when y = v -> Some x
    | x::xs -> revLookup xs v

let push lst x y = (x,y)::lst
let pop lst = match lst with
    | [] -> []
    | _::xs -> xs

let rec update lst v w = match lst with
    | [] -> []
    | (x,_)::xs when x = v -> (x,w)::xs
    | x::xs -> x::(update xs v w)

// A configuration is a program, store, and heap
type config    = GExpr * env * heap
type valconfig = value * env * heap

// Interpreter based on a big step semantics. It is deterministic, always
// either reducing to a value configuration (i.e. configuration with a program
// value for a term) or nothing. It uses a stack model for the environment to
// (hopefully) accurately model F# mutable variables, and a heap for the arrays
// in order to provide a streamlined semantics. Array values are explicitly
// allocated on the heap.
let eval man gexp =
    // Heap allocator
    let heapTop = ref 0
    let alloc n = let tmp = !heapTop in heapTop := tmp + n; tmp
    // BDD variable dispatch
    let var = ref -1
    let newVar () = var := !var + 1; !var
    // BDD variable mapping
    let varMap    = new System.Collections.Generic.Dictionary<int * (int option), int>()
    let invVarMap = new System.Collections.Generic.Dictionary<int, int * (int option)>()
    let getVar x = varMap.[x]
    let setVar x v = varMap.[x] <- v
                     invVarMap.[v] <- x
    // Check an assertion and pretty print its result
    let checkAssertion e b env =
        let rec printCE valLst = match valLst with
            | [] -> ignore <| printf "\n"
            | (b, v)::xs ->
                let (loc, io) = try invVarMap.[v] with _ -> failwith <| sprintf "Variable #%d not in inverse lookup" v
                let var = revLookup env loc
                match (var, io) with
                    | (None, _) -> ignore <| printf "Warning: variable \#%d not found in environment" v
                    | (Some x, None) -> ignore <| printf "%s = %A, " x b
                    | (Some x, Some i) -> ignore <| printf "%s.[%d] = %A, " x i b
                printCE xs
        let printCELst = List.iter (fun ce -> ignore <| printf "    "; printCE ce)
        let counterexamples = bdd.allsat (bdd.dnot b)
        match counterexamples with
            | [] -> ()
            | _ -> ignore <| printf "Assertion failed: \n"
                   show e
                   ignore <| printf "Counterexamples: \n"
                   printCELst counterexamples
                   ignore <| printf "\n"

    let rec eval_rec (tm, env, st) = 
        match tm with
            //
            // <t1, env, st> ==> <v1, env', st'>
            // <t2, push env' x v1, st'> ==> <v2, env'', st''>
            // -----------------------------------------------------
            // <let x = t1 in t2, env, st> ==> <v2, pop env'', st''>
            | LET (x, t1, t2) -> maybe {
                let! (v1, env', st') = eval_rec (t1, env, st)
                let! (v2, env'', st'') = eval_rec (t2, push env' x v1, st')
                return (v2, pop env'', st'')
                }
            //
            // ----------------------------------------------------------
            // <\x1 ... xn . t, env, st> ==> <Lam x1 ... xn . t, env, st>
            | LAMBDA (x, t) -> Some (Lam (x,t), env, st)
            //
            // <t1, env, st> ==> <Lam x. t', env', st'>
            // <t2, env', st'> ==> <v2, env'', st''>
            // <t', push x v2 env'', st''> ==> <v, env''', st'''>
            // -------------------------------------------------------------
            // <t1 t2, env, st> ==> <v, pop env''', st'''>
            | APPLY (t1, t2) -> maybe {
                let! (v1, env', st') = eval_rec (t1, env, st)
                let! (v2, env'', st'') = eval_rec (t2, env', st')
                match v1 with 
                    | Lam (x, t) ->
                        let! (v, env''', st''') = eval_rec (t, push env'' x v2, st'')
                        return (v, pop env''', st''')
                    | _ -> ignore <| printf "Apply: LHS is not a lambda: \n"; show tm
                }
            //
            // <t1, env, st> ==> <Array b1 ... bi, _, st'>
            // <t2, env, st'> ==> <Array bi+1 ... bn, _, st''>
            // --------------------------------------------------------------
            // <Append t1 t2, env, st> ==> <Array b1 ... bn, env, st''>
            //
            | APPEND (t1, t2) -> maybe {
                let! (v1, env', st') = eval_rec (t1, env, st)
                let! (v2, env'', st'') = eval_rec (t2, env', st')
                match (v1, v2) with
                    | (Loc (l1, b1), Loc (l2, b2)) -> 
                        let l = alloc b1 + b2
                        let f st i =
                            let va = if i < b1 then lookup st (l1 + i) else lookup st (l2 - b1 + i)
                            match va with
                                | None -> failwith "Append: could not dereference array \n"
                                | Some b -> (l + i, b)::st
                        return (Loc (l,b1+b2), env'', List.fold f st'' [0..b1+b2-1])
                    | _ -> ignore <| printf "Append: at least one argument is not an Array: \n"; show tm
                }
            // <t1, env, st> ==> <Bool b1, env', st'>
            // <t2, env', st'> ==> <Bool b2, env'', st''>
            // --------------------------------------------------------------
            // <Xor t1 t2, env, st> ==> <b1 \oplus b2, env'', st''>
            //
            | XOR (t1, t2) -> maybe {
                let! (v1, env', st') = eval_rec (t1, env, st)
                let! (v2, env'', st'') = eval_rec (t2, env', st')
                match (v1, v2) with
                    | (Bool b1, Bool b2) -> return (Bool <| bdd.xor b1 b2, env'', st'')
                    | _ -> ignore <| printf "Xor: at least one argument is not Boolean: \n"; show tm
                }
            // <t1, env, st> ==> <Bool b1, env', st'>
            // <t2, env', st'> ==> <Bool b2, env'', st''>
            // --------------------------------------------------------------
            // <And t1 t2, env, st> ==> <b1 /\ b2, env'', st''>
            //
            | AND (t1, t2) -> maybe {
                let! (v1, env', st') = eval_rec (t1, env, st)
                let! (v2, env'', st'') = eval_rec (t2, env', st')
                match (v1, v2) with
                    | (Bool b1, Bool b2) -> return (Bool <| bdd.dand b1 b2, env'', st'')
                    | _ -> ignore <| printf "And: at least one argument is not Boolean: \n"; show tm
                }
            // <t1, env, st> ==> <Bool b1, env', st'>
            // <t2, env', st'> ==> <Bool b2, env'', st''>
            // --------------------------------------------------------------
            // <Eq t1 t2, env, st> ==> <b1 = b2, env'', st''>
            //
            | EQ (t1, t2) -> maybe {
                let! (v1, env', st') = eval_rec (t1, env, st)
                let! (v2, env'', st'') = eval_rec (t2, env', st')
                match (v1, v2) with
                    | (Bool b1, Bool b2) -> return (Bool <| bdd.eq b1 b2, env'', st'')
                    | _ -> ignore <| printf "Eq: at least one argument is not Boolean: \n"; show tm
                }
            // <t, env, st> ==> <Bool b, env', st'>
            // --------------------------------------------------------------
            // <Not t, env, st> ==> <not b, env', st'>
            | NOT t -> maybe {
                let! (v, env', st') = eval_rec (t, env, st)
                match v with
                    | Bool b -> return (Bool <| bdd.dnot b, env', st')
                    | _ -> ignore <| printf "Not: argument is not Boolean: \n"; show tm 
                }
            // <t1, env, st> ==> <Loc l, env', st'>
            // <t2, env', st'> ==> <Bool b, env'', st''>
            // --------------------------------------------------------------
            // <t1.[i] <- t2, env, st> ==> <unit, env'', st''[l + i -> b]>
            | SET_ARRAY (t1, i, t2) -> maybe {
                let! (v1, env', st') = eval_rec (t1, env, st)
                let! (v2, env'', st'') = eval_rec (t2, env', st')
                match (v1, v2) with
                    | (Loc (l, bnd), Bool b) when bnd > i ->
                        return (Unit, env'', update st'' (l + i) b)
                    | _ -> ignore <| printf "Set array: LHS not a valid location: %A\n" v1
                }
            // <t1, env, st> ==> <Loc l, env', st'>
            // --------------------------------------------------------------
            // <t1.[i], env, st> ==> <st'(l + i), env', st'>
            | GET_ARRAY (t, i) -> maybe {
                let! (v, env', st') = eval_rec (t, env, st)
                match v with
                    | Loc (l, bnd) when bnd > i ->
                        let! b = lookup st' l
                        return (Bool b, env', st')
                    | _ -> ignore <| printf "Get array: LHS is not a location: \n"; show tm
                }
            // <t, env, st> ==> <v, env', st'>
            // --------------------------------------------------------------
            // <x <- t, env, st> ==> <unit, env'[x -> v], st'>
            | SET_VAR (x, t) -> maybe {
                let! (v, env', st') = eval_rec (t, env, st)
                return (Unit, update env' x v, st')
                }
            // <t1, env, st> ==> <_, env', st'>
            // <t2, env', st'> ==> <v2, env'', st''>
            // -------------------------------------------------------------
            // <t1; t2, env, st> ==> <v2, env'', st''>
            //
            | SEQUENCE (t1, t2) -> maybe {
                let! (_, env', st') = eval_rec (t1, env, st)
                let! (v2, env'', st'') = eval_rec (t2, env', st')
                return (v2, env'', st'')
                }
            // --------------------------------------------------------------
            // <Var x, env, st> ==> <Loc env(x), env, st>
            //
            | VAR x -> maybe {
                let! v = lookup env x
                return (v, env, st)
                }
            // st0 = st
            // <ti, env, st(i-1)> ==> <bi, env, sti>
            // --------------------------------------------------------------
            // <Array t1 ... tn, env, st> ==> <Array b1 ... bn, env, sti>
            //
            | ARRAY tlst -> maybe {
                let f (acc, env, st) t = match eval_rec (t, env, st) with
                    | None -> None
                    | Some (v, env', st') -> Some (v::acc, env', st')
                let! (vlst, env', st') = foldM f ([], env, st) tlst
                let getBool v = match v with | Bool b -> Some b | _ -> None
                let! blst = mapM getBool vlst
                let l = alloc (List.length blst)
                let st'' = List.fold (fun st (b, i) -> update st (l + i) b) st' (List.zip blst [0..List.length blst - 1])
                return (Loc (l, List.length blst), env', st'')
                }
            | CONST_INT x -> maybe {
                let l = alloc 32
                let f st i = update st (l + i) (if (x >>> i) % 2 = 1 then bdd.dtrue man else bdd.dfalse man)
                let st' = List.fold f st [0..31]
                return (Loc (l, 32), env, st')
                }
            | CONST_BOOL false -> Some (Bool <| bdd.dfalse man, env, st)
            | CONST_BOOL true  -> Some (Bool <| bdd.dtrue man, env, st)
            // <t, env, st> ==> <Array b1 ... bn, env, st'>
            // -------------------------------------------------------------
            // <t[i..j], env, st> ==> <Array bi ... bj, env, st'>
            //
            | SLICE (t, i, j) -> maybe {
                let! (v, env', st') = eval_rec (t, env, st)
                match v with
                    | Loc (l, bnd) when i >= 0 && j < bnd && i <= j
                        -> return (Loc (l + i, j - i), env', st')
                    | _ -> ignore <| printf "Slice: argument is not an array: \n"; show tm
                }
            // <t, env, st> ==> <Loc l, _, st'>
            // -------------------------------------------------------------
            // <Clean t, env, st> ==> <unit, env, st'[l -> xv]>
            | CLEAN t -> maybe {
                let! (v, env', st') = eval_rec (t, env, st)
                return (v, env', st')
            //    match v with
             //       | Loc (l, bnd) -> 
              //          let! hv = lookup st' l
               //         match hv with
                //            | Bit b -> return (Unit, env, update st' l (Bit <| bdd.ithvar man (getVar (l, None))))
                 //           | Arr barr -> List.iter (fun i -> barr.[i] <- bdd.ithvar man (getVar (l, Some i))) [0..Array.length barr-1]
                  //                        return (Unit, env, st')
                   //         | _ -> ignore <| printf "Clean: stored value is a function: \n"; show tm
                    //| _ -> ignore <| printf "Clean: argument is not a location: \n"; show tm
                }
            | ASSERT e -> maybe {
                let! (v, env', st') = eval_rec (e, env, st)
                match v with
                    | Bool b ->
                        //let _ = checkAssertion e b env'
                        return (v, env, st')
                    | _ -> ignore <| printf "Assert: argument is not Boolean: \n"; show tm
                }
            | _ -> ignore <| printf "Unimplemented case: \n"; show tm; None
    eval_rec (gexp, [], [])
*)

(* Version 2, closer to Revs *)
// BDD Interpreter internals

type id = string // Type of identifiers
type loc = int

// Values
type value =
    | Unit
    | Bit of loc
    | Array of loc array
    | Fun of id * GExpr

type store = (loc * bdd.t) list // Type of stores
type env   = (id * value) list  // Type of environments

// Environment/heap accessors
let rec lookup lst v = match lst with
    | [] -> None
    | (x,y)::xs when x = v -> Some y
    | x::xs -> lookup xs v

let rec revLookup lst v = match lst with
    | [] -> None
    | (x,y)::xs when y = v -> Some x
    | x::xs -> revLookup xs v

let rec update lst v w = match lst with
    | [] -> []
    | (x,_)::xs when x = v -> (x,w)::xs
    | x::xs -> x::(update xs v w)

// A configuration is a program, environment, and store
type config    = GExpr * env * store
type valconfig = value * env * store

// Interpreter based on a big step semantics. It is deterministic, always
// either reducing to a value configuration (i.e. configuration with a program
// value for a term) or nothing. All values are allocated on the heap, and
// variables are references to heap locations (or sets of heap locations).
let eval man gexp =
    // Heap allocator
    let heapTop = ref 0
    let alloc n = let tmp = !heapTop in heapTop := tmp + n; tmp
    // BDD variable dispatch
    let var = ref -1
    let newVar () = var := !var + 1; !var
    // BDD variable mapping
    let varMap    = new System.Collections.Generic.Dictionary<int * (int option), int>()
    let invVarMap = new System.Collections.Generic.Dictionary<int, int * (int option)>()
    let getVar x = varMap.[x]
    let setVar x v = varMap.[x] <- v
                     invVarMap.[v] <- x
    // Check an assertion and pretty print its result
    let checkAssertion e b env =
        let rec printCE valLst = match valLst with
            | [] -> ignore <| printf "\n"
            | (b, v)::xs ->
                let (loc, io) = try invVarMap.[v] with _ -> failwith <| sprintf "Variable #%d not in inverse lookup" v
                let var = revLookup env loc
                match (var, io) with
                    | (None, _) -> ignore <| printf "Warning: variable \#%d not found in environment" v
                    | (Some x, None) -> ignore <| printf "%s = %A, " x b
                    | (Some x, Some i) -> ignore <| printf "%s.[%d] = %A, " x i b
                printCE xs
        let printCELst = List.iter (fun ce -> ignore <| printf "    "; printCE ce)
        let counterexamples = bdd.allsat (bdd.dnot b)
        match counterexamples with
            | [] -> ()
            | _ -> ignore <| printf "Assertion failed: \n"
                   show e
                   ignore <| printf "Counterexamples: \n"
                   printCELst counterexamples
                   ignore <| printf "\n"

    let rec eval_rec (tm, env, st) = 
        match tm with
            | LET (x, t1, t2) -> maybe {
                let! (v1, _, st') = eval_rec (t1, env, st) in
                let! res = eval_rec (t2, (x, v1)::env, st') in
                    return res
                }
            | LAMBDA (x, t) -> Some (Fun (x,t), env, st)
            | APPLY (t1, t2) -> maybe {
                let! (v1, _, st')  = eval_rec (t1, env, st)
                let! (v2, _, st'') = eval_rec (t2, env, st')
                match v1 with 
                    | Fun (x, t) ->
                        let! (v, _, st''') = eval_rec (t, (x, v2)::env, st'')
                        return (v, env, st''')
                    | _ -> ignore <| printf "Apply: LHS is not a lambda: \n"; show tm
                }
            | APPEND (t1, t2) -> maybe {
                let! (v1, _, st')  = eval_rec (t1, env, st)
                let! (v2, _, st'') = eval_rec (t2, env, st')
                match (v1, v2) with
                    | (Array arr1, Array arr2) -> 
                        return (Array (Array.append arr1 arr2), env, st'')
                    | _ -> ignore <| printf "Append: at least one argument is not an Array: \n"; show tm
                }
            | XOR (t1, t2) -> maybe {
                let! (v1, _, st')  = eval_rec (t1, env, st)
                let! (v2, _, st'') = eval_rec (t2, env, st')
                match (v1, v2) with
                    | (Bit l1, Bit l2) -> 
                        let! b1 = lookup st'' l1 in
                        let! b2 = lookup st'' l2 in
                        let l = alloc 1 in
                            return (Bit l, env, (l, bdd.xor b1 b2)::st'')
                    | _ -> ignore <| printf "Xor: at least one argument is not Boolean: \n"; show tm
                }
            | AND (t1, t2) -> maybe {
                let! (v1, _, st')  = eval_rec (t1, env, st)
                let! (v2, _, st'') = eval_rec (t2, env, st')
                match (v1, v2) with
                    | (Bit l1, Bit l2) -> 
                        let! b1 = lookup st'' l1 in
                        let! b2 = lookup st'' l2 in
                        let l = alloc 1 in 
                            return (Bit l, env, (l, bdd.dand b1 b2)::st'')
                    | _ -> ignore <| printf "And: at least one argument is not Boolean: \n"; show tm
                }
            | EQ (t1, t2) -> maybe {
                let! (v1, _, st')  = eval_rec (t1, env, st)
                let! (v2, _, st'') = eval_rec (t2, env, st')
                match (v1, v2) with
                    | (Bit l1, Bit l2) -> 
                        let! b1 = lookup st'' l1 in
                        let! b2 = lookup st'' l2 in
                        let l = alloc 1 in
                            return (Bit l, env, (l, bdd.eq b1 b2)::st'')
                    | _ -> ignore <| printf "Eq: at least one argument is not Boolean: \n"; show tm
                }
            | NOT t -> maybe {
                let! (v, _, st') = eval_rec (t, env, st)
                match v with
                    | Bit l -> 
                        let! b = lookup st' l in 
                            return (Bit l, env, (l, bdd.dnot b)::st')
                    | _ -> ignore <| printf "Not: argument is not Boolean: \n"; show tm 
                }
            | SET_ARRAY (t1, i, t2) -> maybe {
                let! (v1, _, st')  = eval_rec (t1, env, st)
                let! (v2, _, st'') = eval_rec (t2, env, st')
                match (v1, v2) with
                    | (Array arr, Bit l) when i < Array.length arr -> 
                        let! _ = lookup st'' arr.[i] in
                        let! b = lookup st'' l in
                            return (Unit, env, update st'' arr.[i] b)
                    | _ -> ignore <| printf "Set array: LHS not a valid location: \n"; show tm
                }
            | GET_ARRAY (t, i) -> maybe {
                let! (v, _, st') = eval_rec (t, env, st)
                match v with
                    | Array arr when i < Array.length arr ->
                        return (Bit arr.[i], env, st')
                    | _ -> ignore <| printf "Get array: LHS is not a location: \n"; show tm
                }
            | SET_VAR (x, t) -> maybe {
                let! (v, _, st') = eval_rec (t, env, st)
                return (Unit, env, update st' x 
                match (lookup env x, v) with
                    | (Some (Bit l1), Bit l2) ->
                        let! _ = lookup st' l1 in
                        let! b = lookup st' l2 in
                            return (Unit, env, update st' l1 b)
                    | _ -> ignore <| printf "Set var: LHs not a valid location: \n"; show tm
                }
            | SEQUENCE (t1, t2) -> maybe {
                let! (_, _, st') = eval_rec (t1, env, st)
                let! (v2, _, st'') = eval_rec (t2, env, st')
                return (v2, env, st'')
                }
            | VAR x -> maybe {
                let! v = lookup env x
                return (v, env, st)
                }
            | ARRAY tlst -> maybe {
                let f (acc, env, st) t = match eval_rec (t, env, st) with
                    | None -> None
                    | Some (v, env', st') -> Some (v::acc, env', st')
                let! (vlst, env', st') = foldM f ([], env, st) tlst
                let getBool v = match v with 
                    | Bit l -> maybe {
                        let! b = lookup st' l in return b
                        }
                    | _ -> None
                let! blst = mapM getBool vlst
                let l = alloc (List.length blst)
                let st'' = List.fold (fun st (b, i) -> (l + i, b)::st) st' (List.zip blst [0..List.length blst - 1])
                return (Array [|l+0..l+(List.length blst - 1)|], env, st'')
                }
            | CONST_INT x -> maybe {
                let l = alloc 32
                let f st i = 
                    let b = if (x >>> i) % 2 = 1 then bdd.dtrue man else bdd.dfalse man in
                        (l + i, b)::st
                let st' = List.fold f st [0..31]
                return (Array [|l+0..l+31|], env, st')
                }
            | CONST_BOOL b -> maybe {
                let l = alloc 1
                return (Bit l, env, (l, if b then bdd.dtrue man else bdd.dfalse man)::st)
                }
            | SLICE (t, i, j) -> maybe {
                let! (v, _, st') = eval_rec (t, env, st)
                match v with
                    | Array arr when i >= 0 && j < (Array.length arr) && i <= j
                        -> return (Array arr.[i..j], env, st')
                    | _ -> ignore <| printf "Slice: argument is not an array: \n"; show tm
                }
            | CLEAN t -> maybe {
                let! (v, _, st') = eval_rec (t, env, st)
                match v with
                    | Bit l -> return (Unit, env, update st' l (bdd.dfalse man))
                    | Array arr -> return (Unit, env, Array.fold (fun st l -> update st l (bdd.dfalse man)) st' arr)
                    | _ -> ignore <| printf "Clean: argument is not a location or array: \n"; show tm
                }
            | ASSERT e -> maybe {
                let! (v, _, st') = eval_rec (e, env, st)
                match v with
                    | Bit l ->
                        let! b = lookup st' l in
                        //let _ = checkAssertion e b st'
                        return (v, env, st')
                    | _ -> ignore <| printf "Assert: argument is not Boolean: \n"; show tm
                }
            | _ -> ignore <| printf "Unimplemented case: \n"; show tm; None
    eval_rec (gexp, [], [])


// Testing and printing functions

let printBDDs = List.iter bdd.print
let printBDDsDot prefix lst = 
    List.iter (fun (i, b) -> bdd.print_dot (prefix + i.ToString() + ".gv") b) (List.zip [0..List.length lst - 1] lst)

let rec dumpHeap st = 
    List.iter bdd.print st

let progBDDs man gexp = 
    let result = eval man gexp
    let resultHeap st l = 
        let hv = lookup st l
        match hv with
            | None -> ignore <| printf "Resulting location is not on the heap\n"; None
            | Some b -> Some b
    match result with 
        | None -> ignore <| printf "Evaluator failed to produce a result\n"; None
        | Some (Unit, env, st) -> ignore <| printf "Program produced Unit\n"; None
        | Some (Bit l, env, st) -> mapM (resultHeap st) [l]
        | Some (Array arr, env, st) -> mapM (resultHeap st) (Array.toList arr)
        | Some (Fun _, env, st) -> ignore <| printf "Returned value is a function\n"; None

let verify program cleanupStrategy = 
    let man = bdd.init None
    let gexp = gExpr program
    let rexp = generateGraph gexp cleanupStrategy
    let appArray = List.toArray rexp.apps
    let {apps = opApps ; definitionMap = opDefMap} = rexp
    let gates , (outBits, ah) =  toGates (List.toArray opApps) opDefMap  (new AncHeap()) cleanupStrategy

    let progBDDs = progBDDs man gexp 
    match progBDDs with
        | None -> Console.WriteLine "Can't verify, evaluator failed"
        | Some bdds ->
            let circBDDs = circuitBDDs man gates ah.maxUsed outBits
            let circOuts = List.map (List.nth circBDDs) outBits
            printBDDsDot pfname bdds
            printBDDsDot cfname circOuts
            if List.forall (fun (x, y) -> bdd.equal x y) (List.zip bdds circOuts)
            then Console.WriteLine "Program and circuit match"
            else Console.WriteLine "Program and circuit differ: "
                 Console.WriteLine "Program BDDs"
                 printBDDs bdds
                 Console.WriteLine ""
                 Console.WriteLine "Circuit BDDs"
                 printBDDs circOuts

let check program cleanupStrategy = 
    let man = bdd.init None
    let gexp = gExpr program
    ignore <| progBDDs man gexp

(*
let verify gates n outputs = 
    let man = bdd.init None
    printBDDs <| circuitBDDs man gates n outputs

let verify' gexp =
    let man = bdd.init None
    let BDDs = progBDDs man gexp
    match BDDs with
        | None -> ()
        | Some bddlst -> printBDDs bddlst 
*)
