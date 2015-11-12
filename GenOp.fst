module GenOp

open AncillaHeap
//open BoolExp
open ExprTypes
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.DerivedPatterns
open Microsoft.FSharp.Quotations.ExprShape
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Reflection
open RCircuit
open System

module Op   = Microsoft.Research.Liquid.Operations
module Util = Microsoft.Research.Liquid.Util
type Qubits = Microsoft.Research.Liquid.Qubits

let rot n x : bool array = x
let clean x = ()
let allege x = if x then () else failwith "Assertion failed"

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
let rec gExpr = 
    function 
    | Let(var, expr1, expr2) -> LET(var.Name, gExpr expr1, gExpr expr2)
    | Lambdas(vars, lexpr) -> 
        let vars' = List.map (fun (x : Var list) -> (List.head x).Name) vars
        LAMBDA(vars', (gExpr lexpr))
    | Applications(f, xs) -> 
        let exprs = List.map (fun (x : Expr list) -> gExpr <| List.head x) xs
        APPLY(gExpr f, exprs)
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
    | Call(_, methodInfo, exps) -> 
        match methodInfo.Name with
            | "SetArray" -> 
                let var = gExpr exps.Head
                let index = evalConstExp exps.Tail.Head
                let value = gExpr exps.Tail.Tail.Head
                SET_ARRAY(var, index, value)
            | "GetArray" -> 
                let var = gExpr exps.Head
                let index = evalConstExp exps.Tail.Head
                GET_ARRAY(var, index)
            | "ZeroCreate" -> 
                let size = evalConstExp exps.Head
                ARRAY(List.init size (fun _ -> CONST_BOOL false))
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
            | "rot" -> 
                let dist = evalConstExp exps.Head
                let exp = gExpr exps.Tail.Head
                ROT(dist, exp)
            | "clean" -> 
                let exp = gExpr exps.Head
                CLEAN exp 
            | "allege" ->
                let exp = gExpr exps.Head
                ASSERT exp
            | "op_Equality" ->
                let exp1 = gExpr exps.Head
                let exp2 = gExpr exps.Tail.Head
                EQ (exp1, exp2)
            | x -> failwith <| sprintf "Unsupported Call to: %A" x
    | VarSet(var, exp) -> SET_VAR(var.Name, gExpr exp)
    | Var x -> VAR x.Name
    | Int32 x -> CONST_INT x
    //This is not implemented yet.  Want to make my own types for everything so I can do operator overloading
    | NewObject(RBit, Bool x :: _) -> CONST_BOOL x  
    | Bool x -> CONST_BOOL x
    | NewArray(_, x) -> ARRAY(List.map gExpr x)
    | ForIntegerRangeLoop(var, start, finish, fexp) -> 
        let start' = evalConstExp start // tries to evaluate constant
        let finish' = evalConstExp finish
        let mutable seq = gExpr <| substituteVar fexp var.Name finish'
        for i in finish' - 1..-1..start' do
            seq <- SEQUENCE(gExpr (substituteVar fexp var.Name i), seq) // build up the sequence
        seq
    | Sequential(first, second) -> SEQUENCE(gExpr first, gExpr second)
    | Sequential(first, Unit ) -> gExpr first
    | x -> failwith <| sprintf "Unsupported: %A" x

/// <summary>
/// Insert nodes into a graph at some index updating indices as required
/// </summary>
/// <param name="newNodes">Nodes to be inserted</param>
/// <param name="n">Index to insert after</param>
/// <param name="nodes">Nodes that are being insetered into</param>
let insertNodesAfter (newNodes : rNode array) n (nodes : rNode array) = 
    let incIndices greaterThen amount nodes = 
        let incInt = 
            function 
            | n when n > greaterThen -> n + amount
            | n -> n
        
        let incInp = 
            function 
            | Some x -> Some(incInt x)
            | None -> None
        
        let rec incBExp expr = 
            match expr with
            | BXor xs -> BXor <| List.map incBExp xs
            | BAnd xs -> BAnd <| List.map incBExp xs
            | BNot x -> BNot <| incBExp x
            | BVar n -> BVar <| incInt n
        
        let incNode = 
            function 
            | RGENOP op -> 
                RGENOP { op with controls = List.map incInt op.controls
                                 input = incInp op.input }
            | RBOOLEXP(expr, inp) -> RBOOLEXP (incBExp expr, incInt inp)
            | RROT(n, inp) -> RROT (n, incInt inp)
            | RINDEX(var, n) -> RINDEX (incInt var, n)
            | RARRAY vals -> RARRAY <| List.map incInt vals
            | OUTPUT n -> OUTPUT <| incInt n
            | RAPPEND (a,b) -> RAPPEND (incInt a, incInt b)
            | RSLICE (v,a,b) -> RSLICE (incInt v, a , b )
            | RIFTHENELSE (a,b,c) -> RIFTHENELSE (incInt a, incInt b, incInt c)
            | RCLEAN n -> RCLEAN <| incInt n
            | RINIT -> RINIT
            | RBOOL x -> RBOOL x
            | x -> failwith <| sprintf "Error: %A unsupported for increment node" x
        
        Array.map incNode nodes
    
    let resultStart = nodes.[0..n]
    let resultEnd = incIndices n newNodes.Length nodes.[n + 1..]
    Array.concat [ resultStart; newNodes; resultEnd ]

/// <summary>
/// Preform cleanup on a graph
/// </summary>
/// <param name="_nodes"></param>
let applyCleanup (_nodes : rNode list) = 
    let nodes = List.toArray _nodes
    
    //The set of variables initalized in this circuit
    let inits =        
        let mutable initNodes = []
        for i in 0..nodes.Length - 1 do
            match nodes.[i] with
            | RGENOP op when op.input = None -> initNodes <- i :: initNodes
            | RINIT | RBOOL _ -> initNodes <- i :: initNodes
            | _ -> ()
        initNodes
    
    //Gets the modification path of a node n
    let getPath nodes (init : int) = 
        let isIndexOf n = 
            function
            | RINDEX (x,_) when x = n -> true
            | RSLICE (x,_,_) when x = n -> true
            | _ -> false                             
        let rec getPath (nodeAddress : int) = 
            let isOutput = 
                function 
                | RGENOP op -> 
                    match op.input with
                    | Some inp -> inp = nodeAddress
                    | None -> false
                | RBOOLEXP(_, inp) -> inp = nodeAddress
                | OUTPUT a when a = nodeAddress -> true
                | RAPPEND (x1,x2) when x1 = nodeAddress || x2 = nodeAddress -> true
                | RCLEAN a when a = nodeAddress -> true
                | _ -> false
            match Array.tryFindIndex isOutput nodes with
            | Some n -> nodeAddress :: getPath n
            | None -> nodeAddress :: []
        let indices = List.filter (fun x-> (isIndexOf init) nodes.[x]) [0 .. nodes.Length - 1]
        List.concat <| (List.map getPath indices) @ [getPath init]
    
    let getCtrls = 
        function 
        | RGENOP op -> op.controls
        | RBOOLEXP(exp, _) -> getVars exp
        | RIFTHENELSE(a,b,c) -> [a;b;c]
        | OUTPUT a -> [ a ]
        | _ -> []

    //The set of things that depend on a path    
    let rec dependencies (nodes : rNode array) = 
        function
        | n :: ns -> 
            let isCtrl nodeAddress n = List.exists ((=) nodeAddress) <| getCtrls n
            let mutable deps = []
            for i in 0..nodes.Length - 1 do
                if isCtrl n nodes.[i] then deps <- i :: deps
            deps @ dependencies nodes ns
        | [] -> []
    
    let setInput inp = 
        function 
        | RGENOP op -> RGENOP { op with input = Some inp }
        | RBOOLEXP(exp, _) -> RBOOLEXP(exp, inp)
        | RCLEAN n -> RCLEAN inp
        | x -> x
    
    let rec setInputChain start = 
        function 
        | n :: ns -> setInput start n :: setInputChain (start + 1) ns
        | [] -> []
    
    let isGenOp = 
        function 
        | RGENOP _ -> true
        | _ -> false
    
    let checkIfAvailNodes nodes n = 
        let isOutput n = 
            function 
            | RGENOP op -> 
                match op.input with
                | Some inp -> inp = n
                | None -> false
            | RBOOLEXP(_, inp) -> inp = n
            | _ -> false
        Array.forall (fun x -> not (isOutput n x)) nodes
    
    let revNode = 
        function 
        | RGENOP op -> RGENOP { op with reverse = not op.reverse }
        | x -> x

    let isFuncOutputOrCLeaned (nodes: rNode array) path =
        match nodes.[List.head <| List.rev path] with
        | OUTPUT _ | RCLEAN _ -> true
        | _ -> false
    
    let applyCleanup (currNodes : rNode array) init = 
        let initPath = getPath currNodes init
        let controls = List.concat <| List.map getCtrls (List.map (fun x -> currNodes.[x]) initPath)
        let deps = dependencies currNodes initPath
        let maxDep = List.max (deps @ initPath)
        let inputsAvail = List.forall (fun x -> x) <| List.map (fun x -> checkIfAvailNodes currNodes.[0..maxDep] x) controls
        if initPath.Length > 0
           && inputsAvail 
           && (initPath.Length > 1 || isGenOp currNodes.[initPath.[0]]) 
           && not (isFuncOutputOrCLeaned currNodes initPath) then 
                let ops' = List.map (fun x -> revNode currNodes.[x]) initPath
                let cleanedOps = 
                    if isGenOp (List.head ops') then List.rev <| (RCLEAN initPath.Head) :: ops'
                    else List.rev <| (RCLEAN initPath.Tail.Head) :: List.tail ops'
                let finalOps = setInput (List.head <| List.rev initPath) cleanedOps.Head :: setInputChain (maxDep + 1) cleanedOps.Tail
                insertNodesAfter (List.toArray finalOps) maxDep currNodes
        else currNodes
    
    let nodes' = List.fold applyCleanup nodes inits
    Array.toList nodes'

/// <summary>
/// Takes the intermediate representation and constucts a graph
/// </summary>
/// <param name="gexp">The intermediate representation</param>
let generateGraph gexp (cleanup : CleanupType) = 
    let rec rScope gexp (varMap : Map<string * int option, int>) defMap appList = 
        let setVar (targ : string) (value : string) (m : Map<string * int option, int>) = 
            let (values, _) = Map.partition (fun (name, _) _ -> name = value) m
            let m' = Map.filter (fun (name, _) _ -> name <> targ) m //Remove old values of targ from the map
            List.fold (fun map ((_, index), address) -> Map.add (targ, index) address map) m' (Map.toList values)
        
        let mapCtrl input appList =
            let _, _, (appList' : rNode list) = rScope input varMap defMap appList
            match List.head appList' with
            | OUTPUT n -> (n , appList'.Tail)
            | RVAR name -> (varMap.[name, None] , appList'.Tail)
            | _ -> (appList'.Length - 1 , appList')

        let mapCtrls inputs appList = 
            let expFold (inputs, applist) exp = 
                let input , applist' =  mapCtrl exp applist
                (input :: inputs, applist')
            List.fold expFold ([], appList) inputs
        
        let doBoolExp expr appList = 
            let rec getBExp appList = 
                function 
                | XOR(lhs, rhs) -> 
                    let lhs', appList' = getBExp appList lhs
                    let rhs', appList'' = getBExp appList' rhs
                    bXor lhs' rhs', appList''
                | AND(lhs, rhs) -> 
                    let lhs', appList' = getBExp appList lhs
                    let rhs', appList'' = getBExp appList' rhs
                    bAnd lhs' rhs', appList''
                | x -> 
                    let (inp, appList') = mapCtrl x  appList
                    (BVar inp, appList')
            
            let bExpr, appList' = getBExp appList expr
            RBOOLEXP(bExpr, appList'.Length) :: RINIT :: appList'
        let isBool =
            function
            |RBOOL _ -> true
            | _ -> false
        let setInput nodes inp =       
            function
            | RGENOP gop -> RGENOP { gop with input = Some inp } :: nodes
            //For a bool expression being the output corresponds to being xored with the expression.
            //In the case where the top level expression is an xor expression and the value exists in the expression
            //we check to see if it still exists after removing it from the top level
            //If not we can simply set it as the input after removing it
            //If it does still exist we have to initalize a new varible to hold the value and relabel it
            | RBOOLEXP(BXor exprs as expr, _) when List.exists ((=) inp)  (getVars expr) ->
                let expr' = BXor <| List.filter ((<>) (BVar inp)) exprs
                if List.exists ((=) (BVar inp)) exprs 
                    && not (List.exists ((=) inp) << getVars <| expr') then
                    RBOOLEXP(expr', inp) :: nodes
                else
                    RBOOLEXP(expr, List.length nodes) :: RINIT :: nodes  
            | RBOOLEXP (BAnd _ as expr, _) when List.exists ((=) inp)  (getVars expr) -> 
                RBOOLEXP(expr, List.length nodes) :: RINIT :: nodes  
            //If the input varible was just initalized and doesn't exist on the RHS it is set to zero so it is ok to use it as the target since: 0 xor a = a 
            | RBOOLEXP(expr, _) when isBool (List.nth (List.rev nodes) inp) ->
                RBOOLEXP(expr,inp) :: nodes  
            | RBOOLEXP(expr, _) -> 
                RBOOLEXP(expr, List.length nodes) :: RINIT :: nodes
            | RAPPEND (x,y) -> RAPPEND (x,y) :: nodes //XXX not sure about this
            | RINDEX (x,y) -> RINDEX (x,y) :: nodes //XXX not sure about this
            | RROT (x,y) -> RROT(x,y) :: nodes //XXX not sure about this
            | x -> failwith <| sprintf "setInput invalid for %A" x
        
        match gexp with
        // LET( .. , LAMBDA( .. , .. ), .. ) 
        // expressions of the form:
        // let f a = .. 
        // This is a function definition.
        // We evaluate the call graph for the function passing in our current context of defined functions and varibles.
        // We then add it to the map of function definitions and pass that along to the evaluation of the next expression.
        | LET(name, LAMBDA(vars, exp), next) -> 
            let vMap' = Map.ofList << (List.zip <| List.map (fun x -> x, None) (List.rev vars)) <| (List.rev [ 0..vars.Length - 1 ])
            let _, defMap', appList' = rScope exp vMap' defMap <| List.map RVAR (List.rev vars)
            rScope next varMap (Map.add name { apps = appList'
                                               definitionMap = defMap' } defMap) appList
        // LET ( .. , Var .. , ..)
        // Expressions of the form:
        // let a = b
        // This is a variable labeling
        // Simply remove all referances to the varible on the LHS from the map then add a new referance for it pointing to the location of the varible on the RHS.
        // TODO: This is perhaps confusing since it is not a referance.  
        //       Maybe change the meaning to copy the value on the RHS to a new set of ancilla and assign the label on the LHS to those values
        | LET(name, VAR a, next) -> 
            let varMap' = setVar name a varMap
            rScope next varMap' defMap appList
        // Let ( .. , .. , ..)
        // Catches all other let expressions
        // Assumes the expression will evaluate to a value at some address on the RHS.
        // It then adds a varible with the label on the LHS pointing to that address.
        | LET(name, exp, next) -> 
            let (_, appList') = mapCtrl exp appList
            let varMap' = Map.add (name, None) (List.length appList' - 1) varMap
            rScope next varMap' defMap appList'
        // APPLY ( VAR .. , .. )
        // Expressions of the form 
        // f a b
        | APPLY(VAR s, inputs) -> 
            let (ctrls, appList') = mapCtrls inputs appList
            
            let newOp = 
                RGENOP { defaultGenOp with name = s
                                           controls = ctrls
                                           input = None }
            varMap, defMap, newOp :: appList'
        // Expressions of the form 
        // a <> b and a && b
        // Note that athough || is supported it is converted into these operations during the intial reading of the AST
        | XOR _ | AND _ -> 
            let appList' = doBoolExp gexp appList
            varMap, defMap, appList'
        //TODO: Not yet implemented
        | IFTHENELSE ( cond , thenExpr, elseExpr) ->
            let (condLoc, appList') = mapCtrl cond appList
            let (thenLoc, appList'') = mapCtrl thenExpr appList'
            let (elseLoc, appList''') = mapCtrl elseExpr appList''
            varMap, defMap, RIFTHENELSE (condLoc, thenLoc, elseLoc) :: appList'''
        // Expressions of the form:
        // rot 4 a 
        | ROT(n, value) -> 
            let (rVal, appList') = mapCtrl value appList
            varMap, defMap, RROT(n, rVal) :: appList'
            //
        | CLEAN (VAR v) ->
            varMap, defMap, RCLEAN varMap.[v, None] :: appList
        // SEQUENCE(SEQUENCE .. , .. )
        // A Sequence of Sequences can be flattened into
        // a single sequence by appending one sequence to another
        | SEQUENCE(SEQUENCE(x1, x2), y) -> 
            let combineSeq seq1 seq2 = 
                let rec comb = 
                    function 
                    | SEQUENCE(x, y) -> SEQUENCE(x, comb y)
                    | x -> SEQUENCE(x, seq2)
                comb seq1
            
            let combinedSequences = combineSeq (SEQUENCE(x1, x2)) y
            rScope combinedSequences varMap defMap appList
        // SEQUENCE (..)
        // Sequences operations by evaluating the first expression then passing the updated varible map and application list to the second one
        | SEQUENCE(curr, next) -> 
            let varMap', _, appList' = rScope curr varMap defMap appList
            rScope next varMap' defMap appList'
        // GET_ARRAY :
        // Expressions of the form:
        // a.[i]
        // Access to a var at some position is translated at that position if an address exists in the variable map
        // If the varibles were not declared in the local scope (if they were returned by a function for example) and index operation is added and the access will be resolved at circuit generation time.
        | GET_ARRAY(VAR v, n) -> 
            let index = Map.tryFind (v, Some n) varMap
            match index with
            | Some ind -> varMap, defMap, OUTPUT ind :: appList
            | None -> varMap, defMap, RINDEX(varMap.[v, None], n) :: appList
        // SET_ARRAY :
        // Expressions of the form:
        // a.[i] <- x 
        // Setting an array corresponds to storing the output of the operation on the RHS to the varible on the LHS.
        // Note that after this operation is preformed we know that the original value of 'a.[i]' will not be used in the future so further optimizations may be applied
        | SET_ARRAY(VAR v, n, value) -> 
            let _, apps = mapCtrl value appList
            let op = List.head apps          
            let apps' = 
                    match op with
                    | RBOOLEXP _ -> (List.tail << List.tail) apps //why
                    | _ -> List.tail apps   
            let index = Map.tryFind (v, Some n) varMap        
            let appList' = 
                match index with
                | Some ind -> setInput apps' ind op
                | None -> op :: RINDEX(varMap.[v, None], n) :: apps'
            let varMap' = Map.add (v, Some n) (List.length appList' - 1) varMap
            varMap', defMap, appList'
        // SET_VAR:
        // For expressions of the form:
        // 'a <- b' or 'a <- f g'
        // In the case of a function application the function is evaluated
        // And the result is stored in a.  In the case of a single varible
        // 'a' is relabled to point to that varible.
        | SET_VAR(v, _value) -> 
            match _value with
            | VAR a -> 
                let varMap' = setVar v a varMap
                varMap', defMap, appList
            | value -> 
                let _, apps = mapCtrl value appList
                let op = List.head apps
                let apps' = 
                    match op with
                    | RBOOLEXP _ -> (List.tail << List.tail) apps //XXX ?
                    | _ -> List.tail apps
                let appList' = setInput apps' varMap.[v, None] op
                let varMap' = Map.add (v, None) (List.length appList' - 1) varMap
                varMap', defMap, appList'
        //Create an array with the indicies set to to the result of the contained expressions
        | ARRAY exps -> 
            let (ctrls, appList') = mapCtrls exps appList
            varMap, defMap, RARRAY(List.rev ctrls) :: appList'
        | APPEND (a, b) -> 
            let (aCtrl, appList') = mapCtrl a appList
            let (bCtrl, appList'') = mapCtrl b appList'
            varMap, defMap, RAPPEND(aCtrl,bCtrl) :: appList''
        | SLICE (var,start,finish) ->
            let (var', appList') = mapCtrl var appList
            varMap, defMap, RSLICE(var',start,finish) :: appList'
        | VAR(name) -> 
            varMap, defMap, OUTPUT varMap.[name, None] :: appList
        | CONST_BOOL n -> varMap, defMap, RBOOL n :: appList  
        | ASSERT _ -> varMap, defMap, appList
        | x -> 
            printfn "Unsupported1: %A" x
            varMap, defMap, appList
    
    let _, defs, nodes = rScope gexp Map.empty Map.empty []
    
    let addOutput apply = 
        match List.head apply with
        | OUTPUT _ -> apply
        | _ -> OUTPUT(List.length apply - 1) :: apply
    
    let doCLeanUp (nodes : rNode list) = 
        match cleanup with
        | DEFAULT -> applyCleanup nodes
        | BENNETT | NONE -> nodes
    let rec revDefAndClean { apps = nodes; definitionMap = defs } = 
        { apps = doCLeanUp << List.rev << addOutput <| nodes
          definitionMap = Map.map (fun _ def -> revDefAndClean def) defs }
    
    revDefAndClean { apps = nodes
                     definitionMap = defs }

/// <summary>
/// Converts the graph into a circuit
/// </summary>
/// <param name="_apps">The graph</param>
/// <param name="_defMap">A map which defines operations on the graph</param>
/// <param name="_ancHeap">An acncilla heap for ancilla tracking</param>
let toGates _apps (_defMap : Map<string, rDefinition>) (_ancHeap : AncHeap) (cleanup : CleanupType) = 
    let getAdd = 
        function 
        | RADDRESS x -> x
        | x -> failwith <| sprintf "Error: %A is not an address" x
    
    let getBit node = 
        match getAdd node with
        | A_ADDR n -> n
        | x -> failwith <| sprintf "Error: %A is not a bit" x
    
    let getArray node = 
        match getAdd node with
        | A_ARRAY n -> n
        | x -> failwith <| sprintf "Error: %A is not an array" x
    
    let rec _toGates apps (defMap : Map<string, rDefinition>) vars (ancHeap : AncHeap) = 
        let mutable anc = ancHeap
        let mutable gates = []
        let mutable output = None
        for i in 0..Array.length apps - 1 do
            match apps.[i] with
            | RGENOP { name = opName; controls = ctrls; reverse = isRev; input = inp } -> 
                let ctrls' = List.rev ctrls
                let { apps = opApps; definitionMap = opDefMap } = defMap.[opName]
                // Sets the output inside the function to the input
                // Idea for a statment a <- f a is to convert the function from f <> 0 to f <> a
                // This is somewhat confusing and could be changed in the future 
                let setOutput (nodes : rNode array) address = 
                    let rec setOutputRoot i = 
                        match nodes.[i] with
                        | OUTPUT n -> setOutputRoot n
                        | RGENOP gop -> 
                            match gop.input with
                            | Some n -> setOutputRoot n
                            | None -> () //printfn "Warning: cant set outputRoot!"
                        | RBOOLEXP(_, n) | RROT(_, n) -> setOutputRoot n
                        | RINIT | RVAR _ -> nodes.[i] <- RADDRESS(getAdd apps.[address])
                        | RARRAY ns -> 
                            nodes.[i] <- RADDRESS(getAdd apps.[address])
                            List.iter (fun i -> nodes.[i] <- NOP) ns
                        | x -> printfn "Cant set root of %A" x
                    setOutputRoot (nodes.Length - 1)
                    Array.toList nodes
                
                let opApps' = 
                    match inp with
                    | Some n -> setOutput (List.toArray opApps) n
                    | None -> opApps
                
                let vars' = Array.zeroCreate (List.length ctrls')
                for i in 0..List.length ctrls' - 1 do
                    vars'.[i] <- getAdd apps.[ctrls'.[i]]
                let (_gates, _anc, out) = _toGates (List.toArray opApps') opDefMap vars' anc
                if isRev then gates <- (List.rev _gates) @ gates
                else gates <- _gates @ gates
                anc <- _anc
                match inp with
                | Some n -> apps.[i] <- apps.[n]
                | None -> apps.[i] <- out
            | RBOOLEXP(expr, inp) -> 
                let rec addressExpr = 
                    function 
                    | BAnd xs -> BAnd <| List.map addressExpr xs
                    | BXor xs -> BXor <| List.map addressExpr xs
                    | BNot x -> BNot <| addressExpr x
                    | BVar n -> BVar(getBit apps.[n])
                
                //Address and check for "a <- a <> b" like notation               
                let addressedExpr = 
                    let inputBit = getBit apps.[inp]
                    let addrExpr = addressExpr expr
                    if List.exists ((=) inputBit) (getVars addrExpr) then 
                        match addrExpr with
                        | BXor xs when List.exists ((=) (BVar inputBit)) xs -> BXor <| List.filter ((<>) (BVar inputBit)) xs
                        | _ -> 
                            //MR printfn "ERROR: Assignment with bool expression cannot contain var unless it is XORed at the top level.  %A In %A"  inputBit addrExpr
                            addrExpr
                    else addrExpr 
                let _gates, _anc = genExp addressedExpr anc (Some <| getBit apps.[inp])
                anc <- _anc
                gates <- (List.rev _gates) @ gates
                apps.[i] <- apps.[inp]
            | RROT(n, inp) -> 
                let rotAddress offset node = 
                    let adds = getArray node
                    let newAdds = Array.copy adds
                    let size = Array.length adds
                    for i in 0..size - 1 do
                        newAdds.[(i + offset) % size] <- adds.[i]
                    RADDRESS(A_ARRAY newAdds)
                apps.[i] <- rotAddress n apps.[inp]
            | RINDEX(v, ind) -> 
                let getIndex node n = (getArray node).[n]
                apps.[i] <- RADDRESS <| getIndex apps.[v] ind
            | RVAR _ -> 
                assert (i < Array.length vars)
                apps.[i] <- RADDRESS vars.[i]
            | RINIT -> 
                let n = anc.popMin
                apps.[i] <- RADDRESS(A_ADDR n)
            | RBOOL _ -> 
                let n = anc.popMin
                apps.[i] <- RADDRESS(A_ADDR n)
            | RARRAY xs -> apps.[i] <- RADDRESS(A_ARRAY(List.toArray <| List.map (fun x -> getAdd apps.[x]) xs))
            | RAPPEND (a,b) ->
                let getArrayAdds n = 
                    match (getAdd apps.[n]) with
                    | A_ARRAY xs -> xs
                    | x -> failwith <| sprintf "Error: %A is not an array" x
                apps.[i] <-  RADDRESS(A_ARRAY(Array.append (getArrayAdds a) (getArrayAdds b)))
            | RSLICE (var,start,finish) ->
                //printfn "Slice from %A to %A with length %A\n" start finish ((getArray apps.[var]).Length)
                apps.[i] <- RADDRESS(A_ARRAY (getArray apps.[var]).[start..finish])
            | OUTPUT x ->
                output <- Some(getAdd apps.[x])
            | RCLEAN x -> 
                let rec cleanNode (anc : AncHeap) = 
                    function 
                    | A_ADDR n -> 
                        anc.insert n
                        anc
                    | A_ARRAY ns -> Array.fold cleanNode anc ns
                anc <- cleanNode anc (getAdd apps.[x])
            | RIFTHENELSE (ctrl, a, b) -> //Not supporting array arrays here for now to make this simplier 
                let checkLength x = 
                    match getAdd apps.[x] with
                    | A_ADDR _ -> 1
                    | A_ARRAY xs -> xs.Length
                let ctrlCopyGates ctrl bits (outBits: int array) =
                    match bits with
                        | A_ADDR n -> [RTOFF (ctrl, n, outBits.[0])]
                        | A_ARRAY ns ->
                            let mutable gates = []
                            for i in 0..ns.Length-1 do
                                gates <- RTOFF (ctrl,getBit (RADDRESS ns.[i]),outBits.[i]) :: gates 
                            List.rev gates
                let outSize = max (checkLength a) (checkLength b)
                let outBits = List.toArray (anc.getn outSize)
                let ctrlBit = getBit apps.[ctrl]
                let gatesA = ctrlCopyGates ctrlBit (getAdd apps.[a]) outBits
                let gatesB = ctrlCopyGates ctrlBit (getAdd apps.[b]) outBits
                gates <- List.rev ( gatesA @ [RNOT ctrlBit] @  gatesB @ [RNOT ctrlBit]) @ gates
                apps.[i] <- RADDRESS (A_ARRAY (Array.map A_ADDR outBits))
            | RADDRESS _ -> ()
            | NOP -> ()
        match output with
        | Some out -> gates, anc, RADDRESS out
        | None -> gates, anc, apps.[Array.length apps - 1]
    
    let gates, anc, out = _toGates _apps _defMap Array.empty _ancHeap
    match cleanup with
    | DEFAULT | NONE -> 
        let outBits = 
            let addr = getAdd out      
            let rec getAddrBits = 
                function 
                | A_ADDR n -> [ n ]
                | A_ARRAY ns -> List.concat << (List.map getAddrBits) <| Array.toList ns
            addr |> getAddrBits
        List.rev gates, (outBits , anc)
    | BENNETT -> 
        let outSize = 
            let addr = getAdd out
            
            let rec getAddrSize = 
                function 
                | A_ADDR _ -> 1
                | A_ARRAY ns -> List.fold (+) 0 (List.map getAddrSize <| Array.toList ns)
            getAddrSize addr
        
        let outBits = 
            let addr = getAdd out      
            let rec getAddrBits = 
                function 
                | A_ADDR n -> [ n ]
                | A_ARRAY ns -> List.concat << (List.map getAddrBits) <| Array.toList ns
            addr |> getAddrBits
        let cpyGates = List.fold (fun gates (x, y) -> RCNOT(x, y) :: gates) [] (List.zip outBits (anc.getn outSize))
        List.rev gates @ cpyGates @ gates, (outBits , anc)

/// <summary>
/// Creates Dot file for graphviz
/// </summary>
/// <param name="nodes">Graph nodes</param>
let nodesToDot (nodes : rNode array) = 
    let ctrlArrow var b = sprintf "%d -> %d[style=dashed];\n" var b
    let inpArrow var b = sprintf "%d -> %d [color=grey19];\n" var b
    let indexCtrlArrow var b ind = sprintf "%d -> %d [style=dashed,label=%d];\n" var b ind
    let sliceCtrlArrow var b s f = sprintf "%d -> %d [style=dashed,label=\"%d..%d\"];\n" var b s f
    let indexInpArrow var b ind = sprintf "%d -> %d [color=grey19,label=%d];\n" var b ind
    let sliceInpArrow var b s f = sprintf "%d -> %d [style=grey19,label=\"%d..%d\"];\n" var b s f
    let getName = 
        function 
        | RGENOP gop -> Some gop.name
        | RBOOLEXP (expr,_) -> 
            let rec writeExpr = 
                function
                | BVar v -> sprintf " %d " v
                | BAnd exprs -> " (" + writeBinOP "&&" exprs + ") "
                | BXor exprs -> writeBinOP "<>" exprs 
                | BNot expr -> "Not" + writeExpr expr
            and writeBinOP name =
                function
                | [x] -> writeExpr x
                | (x::xs) -> writeExpr x + name + writeBinOP name xs
                | [] -> ""
            Some <| writeExpr expr 
        | RROT(n, _) -> Some <| sprintf "ROT(%d)" n
        | RVAR name -> Some <| sprintf "var %s" name
        | RINDEX _ -> None
        | RAPPEND _ -> Some <| sprintf "append"
        | RSLICE (a,b,c) -> None 
        | RBOOL _ -> None
        | RIFTHENELSE _ -> Some <| sprintf "ifThenElse"
        | RARRAY xs -> Some(sprintf "array(%d)" <| List.length xs)
        | RINIT -> Some <| sprintf "init"
        | RCLEAN _ -> Some <| sprintf "clean"
        | OUTPUT _ -> Some <| sprintf "Out"
        | x -> failwith <| sprintf "UNHANDLED %A" x
    
    let getInpsCrtls = 
        function 
        | RGENOP gop -> 
            match gop.input with
            | Some n -> [ n ], gop.controls
            | None -> [], gop.controls
        | RIFTHENELSE (a,b,c) -> [],[a;b;c]
        | RAPPEND (a,b) -> [a;b] , []
        | RBOOLEXP(expr, input) -> [ input ], getVars expr
        | RROT(_, ctrl) -> [], [ ctrl ]
        | RARRAY _ -> [], []
        | OUTPUT x -> [ x ], []
        | RCLEAN x -> [ x ], []
        | _ -> [], []
    
    let writeInpCrtlArrows n node = 
        let (inputs, controls) = getInpsCrtls node
        
        let ctrlIndArrow (x : int) = 
            match nodes.[x] with
            | RINDEX(v, ind) -> indexCtrlArrow v n ind
            | RSLICE(v,s,f) -> sliceCtrlArrow v n s f 
            | _ -> ctrlArrow x n
        
        let inpIndArrow (x : int) = 
            match nodes.[x] with
            | RINDEX(v, ind) -> indexInpArrow v n ind
            | RSLICE(v,s,f) -> sliceInpArrow v n s f 
            | _ -> inpArrow x n
        
        let arrowApplications = List.map ctrlIndArrow controls @ List.map inpIndArrow inputs
        List.fold (+) "" arrowApplications
    
    let mutable nodesStr = ""
    let mutable arrowsStr = ""
    for i in 0..Array.length nodes - 1 do
        let name = getName nodes.[i]
        match name with
        | Some n -> 
            nodesStr <- nodesStr + sprintf "%d [label=\"%s\"];\n" i n
            arrowsStr <- arrowsStr + writeInpCrtlArrows i nodes.[i]
        | None -> ()
    "digraph  {\nedge [color=grey41,arrowhead=vee];\nnode [fontcolor=grey19,color=grey41];\n" + nodesStr + arrowsStr + "}"

/// <summary>
/// Takes a list of gates and a circuit size and outputs a .qc representation.
/// </summary>
/// <param name="gs">Gates</param>
/// <param name="n">The size of the circuit</param>
let printQCV gs n = 
    let printPrim = 
        function 
        | RCNOT(x, y) -> sprintf "tof %d %d\n" x y
        | RTOFF(x, y, z) -> sprintf "tof %d %d %d\n" x y z
        | RNOT x-> sprintf "not %d\n" x
    
    let varlist = List.fold (+) "" (List.map (sprintf " %d ") [ 0..n ])
    let header = ".v " + varlist + "\n.i" + varlist + "\n.o" + varlist
    let gsStrs = List.map printPrim gs
    let mutable gateStr = String.concat "" gsStrs
    header + "\nBEGIN\n" + gateStr + "\nEND"


let genLiquid gs n (qs:Qubits) = 
    let revToLiq = 
        function 
        | RCNOT(x, y) -> Op.CNOT (List.map (List.nth qs) [x; y])
        | RTOFF(x, y, z) -> Op.CCNOT (List.map (List.nth qs) [x; y; z])
        | RNOT x-> Op.X [List.nth qs x]
    List.iter revToLiq gs

/// <summary>
/// Produces a tuple containing a list of gates and the number of gates in the circuit 
/// </summary>
/// <param name="cleanUp">The strategy that should be used for cleanup</param>
/// <param name="expr">The code quotation to generate a circuit from</param>
let exprToCircWithCleanup cleanUp expr = 
    let gexp = gExpr expr
    let rexp = generateGraph gexp cleanUp
    let { apps = opApps; definitionMap = opDefMap } = rexp
    let ah = new AncHeap()
    let gates, (outbits,_) = toGates (List.toArray opApps) opDefMap ah cleanUp
    gates, (ah.maxUsed - 1,outbits)

let exprToCirc : Expr -> (Primative list * (int*int list)) = (exprToCircWithCleanup DEFAULT)