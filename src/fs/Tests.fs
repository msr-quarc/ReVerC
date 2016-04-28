module Tests
open System
open GenOp
open Circuit
open System.IO

let constTest = 
    let b = [|1|]
    <@@
        let a = Array.zeroCreate 3
        a.[0] <- a.[0] <> a.[b.[0]]
        a
    @@>
        

let slice = 
    <@@
        let xor3 (a :bool array) (b:bool array)  =
            let c = Array.zeroCreate 3
            for i in 0 .. 2 do
                    c.[i] <- a.[i] <> b.[i] 
            c 
        let mutable a = Array.zeroCreate 4
        let mutable b = Array.zeroCreate 3
        let mutable t = a.[0..2]
        t <- xor3 t b
        t
    @@>

let array2 =
    <@@
        let xor2 (a :bool array) (b:bool array)  =
                    let c = Array.zeroCreate 2
                    for i in 0 .. 1 do
                            c.[i] <- a.[i] <> b.[i] 
                    c 
        let a = Array.zeroCreate 2
        let b = Array.zeroCreate 2
        let c = Array.zeroCreate 2
        c.[0] <- a
        //c.[1] <- b
        xor2 a b
    @@>

let appendTest = 
    <@@
        let f (a : bool array) (b : bool array) =
            let x = Array.zeroCreate 2
            for i in 0..1 do
                x.[i] <- a.[i] <> b.[i]
            x
        let a = Array.zeroCreate 3
        let b = Array.zeroCreate 3
        let c = Array.zeroCreate 3
        let d = Array.zeroCreate 2
        let mutable res = Array.zeroCreate 0
        res <- Array.append res (f a.[0..1] b.[0..1])
        res <- Array.append res (f a.[1..2] c.[0..1])
        f res.[0..1] d
    @@>

let tests _ =
    let simple = 
        <@@   
            let a = false
            let b = false
            let c = a <> b
            c
        @@> 
    let array = 
        <@@  
            let xor4 (a :bool array) (b:bool array)  =
                let c = Array.zeroCreate 4
                for i in 0 .. 3 do
                        c.[i] <- a.[i] <> b.[i] 
                c
            let mutable a =  Array.zeroCreate 4
            let b =  Array.zeroCreate 4
            a <- xor4 a b
            a
        @@> 
    let functionExpr = 
        <@@ 
            let f (a : bool) b = a && b
            f false false
        @@> 
    let varDecOrder =
        <@@ 
            let a = false
            let f (a : bool) b  = a && b
            let b = false
            f a b
        @@> 
    
    let setVar = 
        <@@
            let a = false
            let mutable b = false
            let mutable c = (a&&b)
            b <- b <> c
            b
        @@>
    let relabelVar = 
        <@@
            let mutable a = false
            let mutable b = false
            b <- b <> a
            let t = a 
            a <- b
            b <- t
            b <- b <> a
            b
        @@>
    let booleanExpression = 
       <@@
            let h a b c d = (a || b) <> (c && d)        
            h false false false false
        @@>
    let OrOperator = 
       <@@
            let f a b = 
                a || b
            let g a b = 
                a && b  
            let h a b c d = f a b <> g c d        
            h false false false false
        @@>
    let clean = 
        <@@ 
            let a = false
            let b = false
            let c = a <> b
            clean c
            let e = a && b
            e
        @@>
    let concat = 
        <@@ 
            let xor4 (a :bool array) (b:bool array)  =
                    let c = Array.zeroCreate 4
                    for i in 0 .. 3 do
                            c.[i] <- a.[i] <> b.[i] 
                    c
            let xor2 (a :bool array) (b:bool array)  =
                    let c = Array.zeroCreate 4
                    for i in 0 .. 1 do
                            c.[i] <- a.[i] <> b.[i] 
                    c 
            let mutable a = Array.zeroCreate 2
            let b = Array.zeroCreate 2
            let mutable d = Array.zeroCreate 4
            a <- xor2 a b
            d <- xor4 d (Array.concat[a;b])  
        @@>
    let ifelse =
        <@@
            let a = false
            let b = false
            let c = false
            let d = false
            let res = 
                if a then
                    c <> d
                else
                    c <> b 
            b
        @@>        
    let bug1 = //Caused the program to loop forever
        <@@
        let f (a : bool) b = a <> b
        let g (a : bool) b = f a b
        let mutable a = false
        let b = false
        a <- g a b
        @@>
    let bug2 = //Cleaned up output due setting c incorrectly
        <@@
        let a = false
        let b = false
        let mutable c = false
        c <- a && b && c
        c
        @@>
    let append = 
        <@@
            let f (a : bool array) (b : bool array) =
                let x = Array.zeroCreate 1
                x.[0] <- a.[0] <> b.[0]
                x
            let a = Array.zeroCreate 1
            let b = Array.zeroCreate 1
            let c = Array.zeroCreate 1
            let mutable res = Array.zeroCreate 0
            res <- Array.append res (f a b)
            res <- Array.append res (f a c)
        @@>
    let tests =
        [
            "simple" , simple, [RCNOT (0,2); RCNOT (1,2)]
            "array" , array, [RCNOT (4,0); RCNOT (5,1); RCNOT (6,2); RCNOT (7,3)]
            "function" , functionExpr, [RTOFF (0,1,2)]
            "Variable Declaration order" , varDecOrder, [RTOFF (0,1,2)]
            "setVar" , setVar, [RTOFF (0,1,2); RCNOT (2,1)]
            "relabelVar" , relabelVar, [RCNOT (0,1); RCNOT (1,0)]
            "booleanExpression", booleanExpression , [RTOFF (0,1,4); RCNOT (0,4); RCNOT (1,4); RTOFF (2,3,4)]
            "OrOperator", OrOperator, [RTOFF (0,1,4); RCNOT (0,4); RCNOT (1,4); RTOFF (2,3,5); RCNOT (4,6); RCNOT (5,6); RCNOT (1,4); RCNOT (0,4); RTOFF (0,1,4); RTOFF (2,3,5)]
            "clean" , clean, [RCNOT (0,2); RCNOT (1,2); RTOFF (0,1,2)]
            "concat", concat, [RCNOT (2,0); RCNOT (3,1); RCNOT (0,4); RCNOT (1,5); RCNOT (2,6); RCNOT (3,7)]
            "ifelse", ifelse, [RCNOT (2,4); RCNOT (3,4); RCNOT (2,5); RCNOT (1,5); RTOFF (0,4,6); RNOT 0; RTOFF (0,5,6); RNOT 0; RCNOT (2,4); RCNOT (3,4); RCNOT (2,5); RCNOT (1,5)]
            "bug1" , bug1, [RCNOT (0,2); RCNOT (1,2)]
            "bug2" , bug2,  [RTOFF (0,1,4); RTOFF (2,4,3); RTOFF (0,1,4)]
            "append" , append,  [RCNOT (0,3); RCNOT (1,3); RCNOT (0,4); RCNOT(2,4)]
        ] 
    printfn "Tests done!"
