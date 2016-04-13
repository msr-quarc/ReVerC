module Equiv

open Util
open AncillaHeap
open Circuit
open BoolExp
open ExprTypes
open Total
open Interpreter

open GenOp

(* File name prefixes for BDD printing *)
let cfname = "circuitBDD"
let pfname = "programBDD"

//module bdd = mlbdd
module bdd = Buddy

let man = bdd.init None

(* Circuit evaluator *)
let circuitBDDs gates st = 
  let f st gate = match gate with
    | RCNOT (x, y)    -> update st y (bdd.xor (lookup st x) (lookup st y))
    | RTOFF (x, y, z) -> update st z (bdd.xor (bdd.dand (lookup st x) (lookup st y)) (lookup st z))
    | RNOT x          -> update st x (bdd.dnot (lookup st x))
  in
    List.fold f st gates
  
(* Boolean expression evaluator *)
let rec bexpToBDD bexp st = match bexp with
  | BFalse      -> bdd.dfalse man
  | BVar i      -> lookup st i
  | BNot x      -> bdd.dnot (bexpToBDD x st)
  | BAnd (x, y) -> bdd.dand (bexpToBDD x st) (bexpToBDD y st)
  | BXor (x, y) -> bdd.xor  (bexpToBDD x st) (bexpToBDD y st)

let rec printCE valLst env = match valLst with
  | [] -> ignore <| printf "\n"
  | (b, v)::xs ->
    let (name, io) = lookup env v in
    begin match (io) with
      | None   -> printf "%s = %A, " name b
      | Some i -> printf "%s.[%d] = %A, " name i b
    end;
    printCE xs env
let printCELst celst env = List.iter (fun ce -> printf "    "; printCE ce env) celst

(* Interpretation for generating the BDDs of a program *)
type bddState = int * (Total.t<int, bdd.BDD>) * (Total.t<int, string * option<int> >)

let bddInit : bddState              = (0, constMap (bdd.dfalse man), constMap ("", None))
let bddAlloc (top, st, env) bexp    = (top, (top + 1, update st top (bexpToBDD bexp st), env))
let bddAssign (top, st, env) l bexp = (top, update st l (bexpToBDD bexp st), env)
let bddClean (top, st, env) gexp l  = 
  begin match bdd.allsat (lookup st l) with
    | [] -> ()
    | celst -> 
        printf "WARNING: value %s not clean\n" (show gexp);
        printf "Counterexamples: \n";
        printCELst celst env;
        printf "\n"
  end;
  (top, st, env)
let bddAssert (top, st, env) gexp l = 
  begin match bdd.allsat (bdd.dnot (lookup st l)) with
    | [] -> ()
    | celst -> 
        printf "Assertion failed: \n";
        printf "%s\n" (show gexp);
        printf "Counterexamples: \n";
        printCELst celst env;
        printf "\n"
  end;
  (top, st, env)
let bddEval (top, st, env) ivals i  = false //lookup st i

let bddInterp = {
  alloc      = bddAlloc;
  assign     = bddAssign;
  clean      = bddClean;
  assertion  = bddAssert;
  eval       = bddEval
}

let rec allocNBDD x (locs, (top, st, env)) n i =
  if i = n then (List.rev locs, (top, st, env))
  else allocNBDD x (((LOC top)::locs), 
                    (top+1, update st top (bdd.ithvar man top), 
                            update env top (x, Some i))) 
                   n (i+1)

let allocTyBDD x ty (top, st, env) = match ty with
  | GBool -> Val (LOC top, (top + 1, update st top (bdd.ithvar man top), update env top (x, None)))
  | GArray n -> 
    let (locs, st) = allocNBDD x ([], (top, st, env)) n 0 in
      Val (ARRAY locs, st)
  | _ -> Err "Invalid parameter type for circuit generation"

let rec lookup_bdds st lst = match lst with
  | [] -> []
  | (LOC l)::xs -> (lookup st l)::(lookup_bdds st xs)

let rec compileBDD (gexp, (top, st, env)) =
  if isVal gexp then match gexp with
    | LAMBDA (x, ty, t) ->
      begin match allocTyBDD x ty (top, st, env) with
        | Err s -> Err s
        | Val (v, st) -> compileBDD (substGExpr t x v, st)
      end
    | UNIT      -> Val []
    | LOC l     -> Val [lookup st l]
    | ARRAY lst -> Val (lookup_bdds st lst)
  else match (step (gexp, (top, st, env)) bddInterp) with
    | Err s -> Err s
    | Val c' -> compileBDD c'

