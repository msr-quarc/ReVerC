module GenOp

open Util
open AncillaHeap
open BoolExp
open ExprTypes
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.DerivedPatterns
open Microsoft.FSharp.Quotations.ExprShape
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Reflection
open Circuit
open TypeCheck
open Interpreter
open GC
open System

let rot n (x:bool array) = List.toArray <| rotate (List.ofArray x) n
let clean x = ()
let allege x = if x then () else failwith "Assertion failed"
let not x = if x then false else true

type constArray<'T> = 
  { data : array<'T> }
  member this.Item with get i = this.data.[i]
                    and set i v = this.data.[i] <- v
  member this.GetSlice(i : int option, j : int option) : constArray<'T> = match (i, j) with
    | (Some i, Some j) -> { data = this.data.[i..j] }
    | (Some i, None) -> { data = this.data.[i..] }
    | (None, Some j) -> { data = this.data.[..j] }
    | (None, None) -> { data = this.data.[*] }

let unfreeze (x:constArray<'T>) = x.data

/// <summary>
/// Substitutes a varible in some expressions with an integer
/// Used for loop unrolling
/// </summary>
/// <param name="expression">Expression that is being subsituted into</param>
/// <param name="name">Name of the variable to substitute</param>
/// <param name="value">Interger to set it to</param>
let substituteVar expression name (value : int32) = 
    let rec subVar = 
        function 
        | ShapeVar var when var.Name = name -> Expr.Value value
        | ShapeVar var -> Expr.Var var
        | ShapeLambda(var, expr) -> Expr.Lambda(var, subVar expr)
        | ShapeCombination(shapeComboObject, exprList) -> RebuildShapeCombination(shapeComboObject, List.map subVar exprList)
    subVar expression

/// <summary>
/// Evaluates some expression.  
/// Used for evaluating loop indices and array bounds to intergers
/// </summary>
/// <param name="args"></param>
let rec eval = 
    function 
    | Value(v, _) -> v
    | Coerce(e, _) -> eval e
    | NewObject(ci, args) -> ci.Invoke(evalAll args)
    | NewArray(t, args) -> 
        let array = Array.CreateInstance(t, args.Length)
        args |> List.iteri (fun i arg -> array.SetValue(eval arg, i))
        box array
    | NewUnionCase(case, args) -> FSharpValue.MakeUnion(case, evalAll args)
    | NewRecord(t, args) -> FSharpValue.MakeRecord(t, evalAll args)
    | NewTuple(args) -> 
        let t = 
            FSharpType.MakeTupleType [| for arg in args -> arg.Type |]
        FSharpValue.MakeTuple(evalAll args, t)
    | FieldGet(Some(Value(v, _)), fi) -> fi.GetValue(v)
    | PropertyGet(None, pi, args) -> pi.GetValue(null, evalAll args)
    | PropertyGet(Some(x), pi, args) -> pi.GetValue(eval x, evalAll args)
    | SpecificCall <@@ (-) @@> (_, _, exprList) -> 
        let lhs = eval exprList.Head :?> int32
        let rhs = eval exprList.Tail.Head :?> int32
        upcast (lhs - rhs)
    | SpecificCall <@@ (%) @@> (_, _, exprList) -> 
        let lhs = eval exprList.Head :?> int32
        let rhs = eval exprList.Tail.Head :?> int32
        upcast (lhs % rhs)
    | Call(None, mi, args) -> mi.Invoke(null, evalAll args)
    | Call(Some(x), mi, args) -> mi.Invoke(eval x, evalAll args)
    | arg -> raise <| NotSupportedException(arg.ToString())

and evalAll args = 
    [| for arg in args -> eval arg |]

/// <summary>
///  Used to handle constants that should be calculated at compile time
/// Such as array indices and loop bounds
/// </summary>
/// <param name="exp"></param>
let evalConstExp (exp : Expr) = 
    eval exp :?> int32

/// <summary>
/// Takes a quotation and transforms it into an intermediate representation for graph constuction
/// All loops are unrolled in this form 
/// </summary>
/// <param name="expr">An F# quotations expression</param>
let parseAST expr = 
  let varMax = ref 0 in
  let inc () = 
    varMax := !varMax + 1;
    !varMax
  let rec gExpr expr = match expr with
    | Let(var, expr1, expr2) -> LET(var.Name, gExpr expr1, gExpr expr2)
    | Lambda(var, lexpr) -> 
        let getTy (ty:Type) =
          if ty.Name = "constArray`1" 
          then GConst (GVar (inc ()))
          else GVar (inc ())
        LAMBDA (var.Name, getTy var.Type, gExpr lexpr)
    | Application(f, exp) -> APPLY (gExpr f, gExpr exp)
    | SpecificCall <@@ (<>) @@> (_, _, exprList) -> 
        let lhs = gExpr exprList.Head
        let rhs = gExpr exprList.Tail.Head
        XOR(lhs, rhs)
    | AndAlso(l, r) -> //Call to &&
        let lhs = gExpr l
        let rhs = gExpr r
        AND(lhs, rhs)
    | OrElse(l, r) -> //Call to || 
        let lhs = gExpr l
        let rhs = gExpr r
        XOR(AND(lhs, rhs), XOR(lhs, rhs))
    | IfThenElse (c,t,e) -> //Not implemented yet
        let condition = gExpr c 
        let thenExpr = gExpr t
        let elseExpr = gExpr e
        IFTHENELSE (condition , thenExpr , elseExpr )
    | Call(op, methodInfo, exps) -> 
        match methodInfo.Name with
            | "SetArray" -> 
                let var = gExpr exps.Head
                let index = evalConstExp exps.Tail.Head
                let value = gExpr exps.Tail.Tail.Head
                ASSIGN(GET_ARRAY(var, index), value)
            | "GetArray" -> 
                let var = gExpr exps.Head
                let index = evalConstExp exps.Tail.Head
                GET_ARRAY(var, index)
            | "ZeroCreate" -> 
                let size = evalConstExp exps.Head
                ARRAY(List.init size (fun _ -> BOOL false))
            | "Append" ->
                APPEND (gExpr exps.Head, gExpr exps.Tail.Head)
            | "Concat" -> 
                let exp = 
                    match exps.Head with
                        | Coerce (x,_) -> x
                        | x -> failwith <| sprintf "Issue with concat: %A" x
                let rec doAppends =
                    function
                    | NewUnionCase (_,[b; NewUnionCase (_,[]) ]) ->
                        gExpr b
                    | NewUnionCase (_,[a; exprs]) -> 
                        APPEND (gExpr a, doAppends exprs)
                    | x -> failwith <| sprintf "Issue with concat: %A" x
                doAppends exp
            | "GetArraySlice" ->       
                let getVal =
                    function
                    | NewUnionCase (_,n) -> evalConstExp n.Head
                    | x -> failwith <| sprintf "Issue with GetArraySlice: %A" x
                let var = gExpr exps.Head
                let start =  getVal exps.Tail.Head
                let finish =  getVal exps.Tail.Tail.Head
                SLICE(var,start,finish)
            | "GetSlice" ->       
                let getVal =
                    function
                    | NewUnionCase (_,n) -> evalConstExp n.Head
                    | x -> failwith <| sprintf "Issue with GetArraySlice: %A" x
                let var = match op with
                  | Some v -> gExpr v
                  | None -> failwith <| sprintf "No root for get slice: %A" expr
                let start =  getVal exps.Head
                let finish =  getVal exps.Tail.Head
                SLICE(var,start,finish)
            | "rot" -> 
                let dist = evalConstExp exps.Head
                let exp = gExpr exps.Tail.Head
                ROT(dist, exp)
            | "clean" ->
                let exp = gExpr exps.Head
                CLEAN (exp, exp)
            | "allege" ->
                let exp = gExpr exps.Head
                ASSERT (exp, exp)
            | "op_Equality" ->
                let exp1 = gExpr exps.Head
                let exp2 = gExpr exps.Tail.Head
                XOR(BOOL true, XOR(exp1, exp2))
            | "not" ->
                let exp = gExpr exps.Head
                XOR(BOOL true, exp)
            | "Ignore" -> gExpr exps.Head
            | x -> failwith <| sprintf "Unsupported Call to %A in %A" x expr
    | VarSet(var, exp) -> ASSIGN(VAR var.Name, gExpr exp)
    | Var x -> VAR x.Name
    | Int32 x -> ARRAY (List.map (fun b -> BOOL b) (Util.ofInt x 32))
    //This is not implemented yet.  Want to make my own types for everything so I can do operator overloading
    | NewObject(RBit, Bool x :: _) -> BOOL x  
    | Bool x -> BOOL x
    | NewArray(_, x) -> ARRAY(List.map gExpr x)
    | ForIntegerRangeLoop(var, start, finish, fexp) -> 
        let start' = evalConstExp start // tries to evaluate constant
        let finish' = evalConstExp finish
        let mutable seq = gExpr <| substituteVar fexp var.Name finish'
        for i in finish'-1..-1..start' do
            seq <- SEQUENCE(gExpr (substituteVar fexp var.Name i), seq) // build up the sequence
        seq
    | Sequential(first, second) -> SEQUENCE(gExpr first, gExpr second)
    | Sequential(first, unit)   -> gExpr first
    | Value (value, typ) -> failwith <| sprintf "Unsupported value %s : %A" (value.ToString()) typ
    | PropertyGet (Some x, _, exps) ->
        let index = evalConstExp exps.Head
        GET_ARRAY (gExpr x, index)
    | PropertySet (Some x, _, exps, v) ->
        let index = evalConstExp exps.Head
        ASSIGN (GET_ARRAY (gExpr x, index), gExpr v)
    | x -> failwith <| sprintf "Unsupported: %A" x
  let res = gExpr expr
  (inc (), res)
