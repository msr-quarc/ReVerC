module Examples

open GenOp

let counterEx = 
    <@@
        let x = Array.zeroCreate 2
        (not x.[0]) && (x.[1])
    @@>

/// <summary>
/// Generate a ripple adder
/// </summary>
/// <param name="n">Number of bits for each input</param>
let carryRippleAdder n =
    <@@
        fun (a : bool array) (b : bool array) ->
        let result =  Array.zeroCreate (n)
        result.[0] <- a.[0] <> b.[0]
        let mutable carry = false
        carry <- a.[0] <> b.[0]
        result.[1] <- a.[1] <> b.[1] <> carry
        for i in 2 .. n-1 do
            carry <- (a.[i-1] && (b.[i-1] <> carry)) <> (carry && b.[i-1])
            result.[i]  <-  a.[i] <> b.[i] <> carry
        result           
    @@>
(*
let carryRippleAdder n =
    <@@
        let compute_carry (a : bool) (b : bool) (c : bool) =
            (a && (b <> c)) <> (b && c)
        in
        fun (a : bool array) (b : bool array) (result : bool array) ->
        result.[0] <- a.[0] <> b.[0]
        let mutable carry = false
        carry <- compute_carry a.[0] b.[0] carry
        allege (carry = (a.[0] && b.[0]))
        result.[1] <- a.[1] <> b.[1] <> carry
        for i in 2 .. n-1 do
            carry <- compute_carry a.[0] b.[0] carry
            result.[i]  <-  a.[i] <> b.[i] <> carry
            allege (result.[i] = (a.[i] <> b.[i] <> carry))
        result           
    @@>
*)

let mult22 n = 
    <@@
    let ctrlAddModn ctrl (a :bool array) (b :bool array) =
        let mutable c = false
        b.[0] <- b.[0] <> (a.[0]&&ctrl)
        c <- c <> a.[0]
        a.[0] <- a.[0] <> (c && b.[0])
        b.[n-1] <- b.[n-1] <> (a.[n-1] && ctrl)
        b.[n-1] <- b.[n-1] <> (a.[n-2] && ctrl)
        a.[0] <- a.[0] <> (c && b.[0])
        c <- c <> a.[0]
        b.[0] <- b.[0] <> (c&&ctrl)
        clean c
    //let a =  Array.zeroCreate n
    //let b =  Array.zeroCreate n
    fun (a:bool array) (b:bool array) ->
    let result = Array.zeroCreate (2*n)
    for i in 0..n-1 do
        ctrlAddModn a.[i] b result.[i..i+n-1]
    result 
    @@>

let mult n = 
    <@@
    let ctrlAddModn ctrl (a :bool array) (b :bool array) =
        let mutable c = false
        b.[0] <- b.[0] <> (a.[0]&&ctrl)
        c <- c <> a.[0]
        a.[0] <- a.[0] <> (c && b.[0])
        for i in 1 .. n - 2 do
            b.[i] <- b.[i] <> (a.[i] && ctrl)
            a.[i-1] <- a.[i-1] <> a.[i]
            a.[i] <- a.[i] <> (a.[i-1] && b.[i])
        b.[n-1] <- b.[n-1] <> (a.[n-1] && ctrl)
        b.[n-1] <- b.[n-1] <> (a.[n-2] && ctrl)
        for i in 2 .. n - 1 do
            a.[n-i] <- a.[n-i] <> (a.[n-i-1] && b.[n-i])
            a.[n-i-1] <- a.[n-i-1] <> a.[n-i]
            b.[n-i] <- b.[n-i] <> (a.[n-i-1]&& ctrl)
        a.[0] <- a.[0] <> (c && b.[0])
        c <- c <> a.[0]
        b.[0] <- b.[0] <> (c&&ctrl)
        clean c
    //let a =  Array.zeroCreate n
    //let b =  Array.zeroCreate n
    fun (a:bool array) (b:bool array) ->
    let result = Array.zeroCreate (2*n)
    for i in 0..n-1 do
        ctrlAddModn a.[i] b result.[i..i+n-1]
    result 
    @@>

let mult2 n = 
    <@@
    let addModn (a :bool array) (b :bool array) =
        let mutable c = false
        b.[0] <- b.[0] <> a.[0]
        c <- c <> a.[0]
        a.[0] <- a.[0] <> (c && b.[0])
        for i in 1 .. n - 2 do
            b.[i] <- b.[i] <> a.[i] 
            a.[i-1] <- a.[i-1] <> a.[i]
            a.[i] <- a.[i] <> (a.[i-1] && b.[i])
        b.[n-1] <- b.[n-1] <> a.[n-1]
        b.[n-1] <- b.[n-1] <> a.[n-2]
        for i in 2 .. n - 1 do
            a.[n-i] <- a.[n-i] <> (a.[n-i-1] && b.[n-i])
            a.[n-i-1] <- a.[n-i-1] <> a.[n-i]
            b.[n-i] <- b.[n-i] <> a.[n-i-1]
        a.[0] <- a.[0] <> (c && b.[0])
        c <- c <> a.[0]
        b.[0] <- b.[0] <> c
        clean c  
    //let a =  Array.zeroCreate n
    //let b =  Array.zeroCreate n
    //let result = Array.zeroCreate (2*n)
    fun (a:bool array) (b:bool array) ->
    let result = Array.zeroCreate (2*n)
    for i in 0..n-1 do
        let addVal = 
            if a.[i] then
                b
            else
                Array.zeroCreate n
        addModn addVal result.[i..i+n-1]
    result 
    @@>

    (*
let carryLookaheadAdder n = 
    let adderSize = int (sqrt (float n))
    let imSpacing = 2*(adderSize+1)
    <@@
        fun (a:bool array) (b:bool array) ->
        let carryRipple (a:bool array) (b:bool array) (c:bool) (result: bool array) =
            let mutable carry = c
            result.[0] <- a.[0] <> b.[0] <> carry
            for i in 1 .. adderSize - 1 do
                carry <- (a.[i-1] && (carry <> b.[i-1])) <> (carry && b.[i-1])
                result.[i]  <-  a.[i] <> b.[i] <> carry
        let carryRippleC (a:bool array) (b:bool array) (c:bool) (result: bool array) =
            let mutable carry = c
            result.[0] <- a.[0] <> b.[0] <> carry
            for i in 1 .. adderSize - 1 do
                carry <- (a.[i-1] && (carry <> b.[i-1])) <> (carry && b.[i-1])
                result.[i]  <-  a.[i] <> b.[i] <> carry
            result.[adderSize] <- carry
        let result = Array.zeroCreate (adderSize*adderSize)
        let a0b0 = Array.zeroCreate (adderSize+1)
        carryRipple a.[0..adderSize-1] b.[0..adderSize-1] false a0b0
        carryRipple a.[0..adderSize-1] b.[0..adderSize-1] result.[0..adderSize-1] // a0b0
        let a' = a.[adderSize .. adderSize*adderSize-1]
        let b' = b.[adderSize .. adderSize*adderSize-1]
        let intermediateResults = Array.zeroCreate (2*imSpacing*adderSize)
        for i in 0 .. adderSize - 2 do
            carryRippleFalse a'.[i*adderSize .. i*adderSize + adderSize-1] b'.[i*adderSize .. i*adderSize + adderSize-1] intermediateResults.[2*i*imSpacing..(2*i+1)*imSpacing - 1]
            carryRippleTrue a'.[i*adderSize .. i*adderSize + adderSize-1] b'.[i*adderSize .. i*adderSize + adderSize-1] intermediateResults.[(2*i+1)*imSpacing..2*(i+1)*imSpacing]
        let mutable carry = result.[adderSize]
        for i in 0 .. adderSize - 2 do
            for j in 0 .. adderSize - 1 do
              result.[(i+1)*adderSize + j] <- (carry && intermediateResults.[i*imSpacing + j]) <> ((true <> carry) && intermediateResults.[i*imSpacing + adderSize + 1 + j])
            carry <- (carry && intermediateResults.[i*imSpacing+adderSize]) <> ((true <> carry) && intermediateResults.[i*imSpacing+2*adderSize+1])
        result
      @@>*)

let carryLookaheadAdder n = 
    let adderSize = int (sqrt (float n))
    let imSpacing = 2*(adderSize+1)
    <@@
        fun (a:bool array) (b:bool array) ->
        let carryRipple (a:bool array) (b:bool array) (c:bool) (result: bool array) =
            let mutable carry = c
            result.[0] <- a.[0] <> b.[0] <> carry
            for i in 1 .. adderSize - 1 do
                carry <- (a.[i-1] && (carry <> b.[i-1])) <> (carry && b.[i-1])
                result.[i]  <-  a.[i] <> b.[i] <> carry
            result.[adderSize] <- carry
        let result = Array.zeroCreate (adderSize*(adderSize-1))
        let a0b0 = Array.zeroCreate (adderSize+1)
        carryRipple a.[0..adderSize-1] b.[0..adderSize-1] false a0b0
        let a' = a.[adderSize .. adderSize*adderSize-1]
        let b' = b.[adderSize .. adderSize*adderSize-1]
        let intermediateResults = Array.zeroCreate (2*adderSize*adderSize-2)
        for i in 0 .. adderSize - 2 do
            carryRipple a'.[i*adderSize .. i*adderSize + adderSize-1] b'.[i*adderSize .. i*adderSize + adderSize-1] false intermediateResults.[2*i*(adderSize+1)..(2*i+1)*(adderSize+1) - 1]
            carryRipple a'.[i*adderSize .. i*adderSize + adderSize-1] b'.[i*adderSize .. i*adderSize + adderSize-1] true intermediateResults.[(2*i+1)*(adderSize+1)..2*(i+1)*(adderSize+1) - 1]
        let mutable carry = a0b0.[adderSize]
        for i in 0 .. adderSize - 2 do
            for j in 0 .. adderSize - 1 do
              result.[i*adderSize + j] <- (carry && intermediateResults.[i*imSpacing + j]) <> ((true <> carry) && intermediateResults.[i*imSpacing + adderSize + 1 + j])
            carry <- (carry && intermediateResults.[i*imSpacing+adderSize]) <> ((true <> carry) && intermediateResults.[i*imSpacing+2*adderSize+1])
        Array.concat [a0b0.[0..adderSize-1]; result]
      @@>
//
//        //<- c.[i] || (for j in 0..i do ttt <- ttt && c.[j])
////        for i in 1..n do 
////            temp.[0] <- a.[i-1] && b.[i-1] 
////            for j in 1..i-1 do 
////                temp.[j] <- temp.[j] && (a.[]) // fix this 
////            for j in 0..n-1 do 
////                c.[i] <- c.[i] || temp.[j]
////        
////        for i in 0.. 
//               
//    @>

/// <summary>
/// Cuccaro adder 
/// </summary>
/// <param name="n">>Number of bits for each input</param>
let addMod2 n =
    <@
        fun (a:bool array) (b:bool array) ->
        let mutable c = false
        b.[0] <- b.[0] <> a.[0]
        c <- c <> a.[0]
        a.[0] <- a.[0] <> (c && b.[0])
        a.[0] <- a.[0] <> (c && b.[0])
        c <- c <> a.[0]
        b.[0] <- b.[0] <> c
        clean c
        b          
    @>

let addMod n =
    <@
        fun (a:bool array) (b:bool array) ->
        let mutable c = false
        b.[0] <- b.[0] <> a.[0]
        c <- c <> a.[0]
        a.[0] <- a.[0] <> (c && b.[0])
        for i in 1 .. n - 2 do
            b.[i] <- b.[i] <> a.[i]
            a.[i-1] <- a.[i-1] <> a.[i]
            a.[i] <- a.[i] <> (a.[i-1] && b.[i])
        b.[n-1] <- b.[n-1] <> a.[n-1]
        b.[n-1] <- b.[n-1] <> a.[n-2]
        for i in 2 .. n - 1 do
            a.[n-i] <- a.[n-i] <> (a.[n-i-1] && b.[n-i])
            a.[n-i-1] <- a.[n-i-1] <> a.[n-i]
            b.[n-i] <- b.[n-i] <> a.[n-i-1]
        a.[0] <- a.[0] <> (c && b.[0])
        c <- c <> a.[0]
        b.[0] <- b.[0] <> c
        clean c
        b          
    @>

let cucarro2 n =
    <@@ 
        fun (a:bool array) (b:bool array) ->
        let mutable c = false
        b.[0] <- b.[0] <> a.[0]
        c <- c <> a.[0]
        a.[0] <- a.[0] <> (c && b.[0])
        b.[n-1] <- b.[n-1] <> a.[n-1]
        b.[n-1] <- b.[n-1] <> a.[n-2]
        a.[0] <- a.[0] <> (c && b.[0])
        c <- c <> a.[0]
        b.[0] <- b.[0] <> c
        clean c
        b
    @@>

let cucarro n =
    <@@ 
        fun (a:bool array) (b:bool array) ->
        let mutable c = false
        b.[0] <- b.[0] <> a.[0]
        c <- c <> a.[0]
        a.[0] <- a.[0] <> (c && b.[0])
        for i in 1 .. n - 2 do
            b.[i] <- b.[i] <> a.[i]
            a.[i-1] <- a.[i-1] <> a.[i]
            a.[i] <- a.[i] <> (a.[i-1] && b.[i])
        b.[n-1] <- b.[n-1] <> a.[n-1]
        b.[n-1] <- b.[n-1] <> a.[n-2]
        a.[0] <- a.[0] <> (c && b.[0])
        c <- c <> a.[0]
        b.[0] <- b.[0] <> c
        clean c
        b
    @@>

let ma4 =
    <@@
        fun (a:bool array) (b:bool array) (c:bool array) ->
        let ma4 (a :bool array)  (b :bool array)  (c :bool array) = 
            let t =  Array.zeroCreate 4
            for i in 0 .. 3 do
                t.[i] <- (a.[i] && (b.[i] <> c.[i])) <> (b.[i] && c.[i])
            t
        ma4 a b c
    @@>
/// <summary>
/// Runs a number of rounds of SHA-2
/// </summary>
/// <param name="n">number of rounds</param>
let exprSha n = 
    <@
    fun (k :bool array) (w :bool array) (x :bool array) ->
    let addMod2_32 (a :bool array) (b :bool array) =
        let mutable c = false
        b.[0] <- b.[0] <> a.[0]
        c <- c <> a.[0]
        a.[0] <- a.[0] <> (c && b.[0])
        for i in 1 .. 30 do
            b.[i] <- b.[i] <> a.[i]
            a.[i-1] <- a.[i-1] <> a.[i]
            a.[i] <- a.[i] <> (a.[i-1] && b.[i])
        b.[31] <- b.[31] <> a.[31]
        b.[31] <- b.[31] <> a.[30]
        for i in 2 .. 32 - 1 do
            a.[32-i] <- a.[32-i] <> (a.[31-i] && b.[32-i])
            a.[31-i] <- a.[31-i] <> a.[32-i]
            b.[32-i] <- b.[32-i] <> a.[31-i]
        a.[0] <- a.[0] <> (c && b.[0])
        c <- c <> a.[0]
        b.[0] <- b.[0] <> c
        clean c
    let ch (e :bool array)  (f :bool array)  (g :bool array) = 
        let t =  Array.zeroCreate 32
        for i in 0 .. 31 do
            t.[i] <- e.[i] && f.[i] && g.[i]
        t
    let ma (a :bool array)  (b :bool array)  (c :bool array) = 
        let t =  Array.zeroCreate 32
        for i in 0 .. 31 do
            t.[i] <- (a.[i] && (b.[i] <> c.[i])) <> (b.[i] && c.[i])
        t
    let s0 a =
        let a2 = rot 2 a  
        let a13 = rot 13 a
        let a22 = rot 22 a
        let t =  Array.zeroCreate 32
        for i in 0 .. 31 do
            t.[i] <- a2.[i] <> a13.[i] <> a22.[i]
        t
    let s1 a =
        let a6 = rot 6 a 
        let a11 = rot 11 a
        let a25 = rot 25 a 
        let mutable t =  Array.zeroCreate 32
        for i in 0 .. 31 do
            t.[i] <- a6.[i] <> a11.[i] <> a25.[i]
        t
    let hsh (x :bool array) =
        let a = x.[0..31]
        let b = x.[32..63]
        let c = x.[64..95]
        let d = x.[96..127]
        let e = x.[128..159]
        let f = x.[160..191]
        let g = x.[192..223]
        let h = x.[224..255]
        addMod2_32 (ch e f g) h
        addMod2_32 (s0 a) h
        addMod2_32 w h
        addMod2_32 k h
        addMod2_32 h d
        addMod2_32 (ma a b c) h
        addMod2_32 (s1 e) h
    for i in 0 .. n - 1 do
        hsh (rot (32*i % 256) x)
    x
    @>

let exprShaEfficient = 
  <@
    fun (k :bool array) (w :bool array) (x :bool array) ->
    let addMod2_32 (a :bool array) (b :bool array) =
        let mutable c = false
        b.[0] <- b.[0] <> a.[0]
        c <- c <> a.[0]
        a.[0] <- a.[0] <> (c && b.[0])
        for i in 1 .. 30 do
            b.[i] <- b.[i] <> a.[i]
            a.[i-1] <- a.[i-1] <> a.[i]
            a.[i] <- a.[i] <> (a.[i-1] && b.[i])
        b.[31] <- b.[31] <> a.[31]
        b.[31] <- b.[31] <> a.[30]
        for i in 2 .. 31 do
            a.[32-i] <- a.[32-i] <> (a.[32-i-1] && b.[32-i])
            a.[32-i-1] <- a.[32-i-1] <> a.[32-i]
            b.[32-i] <- b.[32-i] <> a.[32-i-1]
        a.[0] <- a.[0] <> (c && b.[0])
        c <- c <> a.[0]
        b.[0] <- b.[0] <> c
        clean c
    let ch (e :bool array)  (f :bool array)  (g :bool array) (t :bool array) = 
        for i in 0 .. 31 do
          t.[i] <- t.[i] <> (e.[i] && f.[i] && g.[i])
    let ma (a :bool array)  (b :bool array)  (c :bool array) (t: bool array) = 
        for i in 0 .. 31 do
          t.[i] <- t.[i] <> ((a.[i] && (b.[i] <> c.[i])) <> (b.[i] && c.[i]))
    let s0 a (t :bool array) =
        let a2 = rot 2 a  
        let a13 = rot 13 a
        let a22 = rot 22 a
        for i in 0 .. 31 do
          t.[i] <- t.[i] <> (a2.[i] <> a13.[i] <> a22.[i])
    let s1 a (t :bool array) =
        let a6 = rot 6 a 
        let a11 = rot 11 a
        let a25 = rot 25 a 
        for i in 0 .. 31 do
          t.[i] <- t.[i] <> (a6.[i] <> a11.[i] <> a25.[i])
    let a = x.[0..31]
    let b = x.[32..63]
    let c = x.[64..95]
    let d = x.[96..127]
    let e = x.[128..159]
    let f = x.[160..191]
    let g = x.[192..223]
    let h = x.[224..255]
//    let k = [| false; false; false; true; true; false; false; true; true; true; true; true; false;
//               true; false; false ;false; true; false; true; false; false; false; true; false; true;
//               false; false; false; false; true; false |]
    let mutable anc = Array.zeroCreate 32
    s1 e anc
    addMod2_32 anc h
    s1 e anc

    ch e f g anc
    addMod2_32 anc h
    ch e f g anc

    addMod2_32 k h
    addMod2_32 w h
    addMod2_32 h d

    ma a b c anc
    addMod2_32 anc h
    ma a b c anc

    s0 a anc
    addMod2_32 anc h
    s0 a anc

    x
  @>


/// <summary>
/// Runs a number of rounds of MD5
/// </summary>
/// <param name="n">number of rounds</param>
let exprMD5 n = 
    let s = [| 7; 12; 17; 22;  7; 12; 17; 22;  7; 12; 17; 22;  7; 12; 17; 22; 
               5;  9; 14; 20;  5;  9; 14; 20;  5;  9; 14; 20;  5;  9; 14; 20; 
               4; 11; 16; 23;  4; 11; 16; 23;  4; 11; 16; 23;  4; 11; 16; 23;
               6; 10; 15; 21;  6; 10; 15; 21;  6; 10; 15; 21;  6; 10; 15; 21 |] 
    <@
    fun (M :bool array) (K :bool array) (A :bool array) (B :bool array) 
        (C :bool array) (D :bool array) ->

    let addMod2_32 (a :bool array) (b :bool array) =
        let mutable c = false
        b.[0] <- b.[0] <> a.[0]
        c <- c <> a.[0]
        a.[0] <- a.[0] <> (c && b.[0])
        for i in 1 .. 30 do
            b.[i] <- b.[i] <> a.[i]
            a.[i-1] <- a.[i-1] <> a.[i]
            a.[i] <- a.[i] <> (a.[i-1] && b.[i])
        b.[31] <- b.[31] <> a.[31]
        b.[31] <- b.[31] <> a.[30]
        for i in 2 .. n - 1 do
            a.[32-i] <- a.[32-i] <> (a.[31-i] && b.[32-i])
            a.[31-i] <- a.[31-i] <> a.[32-i]
            b.[32-i] <- b.[32-i] <> a.[31-i]
        a.[0] <- a.[0] <> (c && b.[0])
        c <- c <> a.[0]
        b.[0] <- b.[0] <> c
        clean c

    let F (B : bool array)  (C : bool array)  (D : bool array) = 
        let t =  Array.zeroCreate 32
        for i in 0 .. 31 do
            t.[i] <- (B.[i] && C.[i]) || ((B.[i] <> false) && D.[i]) 
        t
    
    let G (B : bool array)  (C : bool array)  (D : bool array) = 
        let t =  Array.zeroCreate 32
        for i in 0 .. 31 do
            t.[i] <- (D.[i] && B.[i]) || ((D.[i] <> false) && C.[i]) 
        t
    
    let H (B : bool array)  (C : bool array)  (D : bool array) = 
        let t =  Array.zeroCreate 32
        for i in 0 .. 31 do
            t.[i] <- (B.[i] <> C.[i] <> D.[i])
        t
    
    let I (B : bool array)  (C : bool array)  (D : bool array) = 
        let t =  Array.zeroCreate 32
        for i in 0 .. 31 do
            t.[i] <- (C.[i] <> (B.[i] || (D.[i] <> false)))
        t

    for i in 0 .. 15 do
        let mutable t = Array.zeroCreate 32
        addMod2_32 A t
        addMod2_32 (F B C D) t
        addMod2_32 K t
        addMod2_32 M.[32*i..32*i+31] t
        addMod2_32 (rot s.[i] t) B
        //let temp = D
        //D <- C; C <- B; A <- temp        
    for i in 16 .. 31 do
        let mutable t = Array.zeroCreate 32
        addMod2_32 A t
        addMod2_32 (G B C D) t
        addMod2_32 K t
        addMod2_32 M.[32*((5*i+1)%16)..32*((5*i+1)%16)+31] t
        addMod2_32 (rot s.[i] t) B
        //let temp = D
        //D <- C; C <- B; A <- temp        
    for i in 32 .. 47 do        
        let mutable t = Array.zeroCreate 32
        addMod2_32 A t
        addMod2_32 (H B C D) t
        addMod2_32 K t
        addMod2_32 M.[32*((3*i+5)%16)..32*((3*i+5)%16)+31] t
        addMod2_32 (rot s.[i] t) B
        //let temp = D
        //D <- C; C <- B; A <- temp        
    for i in 48 .. 63 do      
        let mutable t = Array.zeroCreate 32
        addMod2_32 A t
        addMod2_32 (I B C D) t
        addMod2_32 K t
        addMod2_32 M.[32*((7*i)%16)..32*((7*i)%16)+31] t
        addMod2_32 (rot s.[i] t) B
        //let temp = D
        //D <- C; C <- B; A <- temp        
    Array.concat [A; B; C; D]
    @>

let keccakf l =
  let w = 1<<<l
  let b = 25*w
  let n = 12+2*l
  let r = [| 0; 36; 3; 41; 18; 1; 44; 10; 45; 2; 62; 6; 43;
             15; 61; 28; 55; 25; 21; 56; 27; 20; 39; 8; 14 |]
  let ind x y z = 5*w*(x % 5) + w*(y % 5) + z
  <@
    fun (A :bool array) (RC :bool array) ->

    let bxor (a: bool array) (b: bool array) =
      for i in 0..w-1 do
        a.[i] <- a.[i] <> b.[i]

    let theta (a: bool array) =
      let A = a
      let C = Array.zeroCreate (5*w)   // temporary storage
      let D = Array.zeroCreate (5*w)   // temporary storage
      for x in 0..4 do          // C stage
        for y in 0..4 do
          bxor C.[w*x..w*x + w-1] A.[5*w*x + w*y..5*w*x + w*y + w-1]
      for x in 0..4 do          // D stage
        bxor D.[w*x..w*x + w-1] C.[w*((((x-1) % 5) + 5) % 5)..w*((((x-1) % 5) + 5) % 5) + w-1]
        bxor D.[w*x..w*x + w-1] (rot (1 % w) C.[w*((x+1) % 5)..w*((x+1) % 5) + w-1])
      for x in 0..4 do          // A stage
        for y in 0..4 do
          bxor A.[5*w*x + w*y..5*w*x + w*y + w-1] D.[w*x..w*x + w-1]
      A

    let rhopi (A: bool array) =
      let B = Array.zeroCreate (5*5*w) // temporary storage
      for x in 0..4 do          // Shuffle indices
        for y in 0..4 do
          bxor B.[5*w*y + w*((2*x + 3*y) % 5)..5*w*y + w*((2*x + 3*y) % 5) + w-1] 
               (rot (r.[w*x + y] % w) A.[5*w*x + w*y..5*w*x + w*y + w-1])
      B

    let chi (A: bool array) =
      let C = Array.zeroCreate (5*w)   // temporary storage
      for y in 0..4 do
        for x in 0..4 do
          for z in 0..w-1 do
            C.[w*x + z] <- C.[w*x + z] <> A.[5*w*x + w*y + z] <> A.[5*w*((x+2) % 5) + w*y + z]
                                <> (A.[5*w*((x+1) % 5) + w*y + z] && A.[5*w*((x+2) % 5) + w*y + z])
        for x in 0..4 do
          for z in 0..w-1 do
            A.[5*w*x + w*y + z] <- C.[w*x + z]
        for x in 0..4 do     // uncompute C
          for z in 0..w-1 do
            C.[w*x + z] <- C.[w*x + z] <> A.[5*w*x + w*y + z] <> A.[5*w*((x+2) % 5) + w*y + z]
                                <> (A.[5*w*((x+1) % 5) + w*y + z] && A.[5*w*((x+2) % 5) + w*y + z])
      A

    let iota (A: bool array) = 
      bxor A.[0..w-1] RC
      A

    iota (chi (rhopi (theta A)))
  @>

let keccakfInPlace l =
  let w = 1<<<l
  let b = 25*w
  let n = 12+2*l
  let r = [| 0; 36; 3; 41; 18; 1; 44; 10; 45; 2; 62; 6; 43;
             15; 61; 28; 55; 25; 21; 56; 27; 20; 39; 8; 14 |]
  let inversePositions64 = [| 
    0xDE26BC4D789AF134UL;
    0x09AF135E26BC4D78UL;
    0xEBC4D789AF135E26UL;
    0x7135E26BC4D789AFUL;
    0xCD789AF135E26BC4UL |]
  let inversePositions = Array.zeroCreate 5
  let inverseBits : bool array = Array.zeroCreate (5*64)

  for z in 0..w..63 do
    for x in 0..4 do
      inversePositions.[x] <- inversePositions.[x] ^^^ (inversePositions64.[x] >>> z)
  for xOff in 0..4 do
    for z in 0..63 do
      if ((inversePositions.[xOff] >>> z) &&& 1UL) = 1UL then
        inverseBits.[64*xOff + z] <- true
      else 
        inverseBits.[64*xOff + z] <- false
(*
  printf "[|"
  Array.iter (fun x -> printf "%A;" x) inverseBits
  printf "|]"
*)
  let inverseBits0 = [|
    false;false;false;true;true;false;true;true;true;false;false;false;false;true;false;true;false;
    false;true;true;false;true;true;true;false;false;false;false;true;false;true;false;false;true;
    true;false;true;true;true;false;false;false;false;true;false;true;false;false;true;true;false;
    true;true;true;false;false;false;false;true;false;true;false;false;true;false;false;false;false;
    true;false;true;false;false;true;true;false;true;true;true;false;false;false;false;true;false;
    true;false;false;true;true;false;true;true;true;false;false;false;false;true;false;true;false;
    false;true;true;false;true;true;true;false;false;false;false;true;false;true;false;false;true;
    true;false;true;true;true;false;false;false;false;true;true;false;true;true;true;false;false;
    false;false;true;false;true;false;false;true;true;false;true;true;true;false;false;false;false;
    true;false;true;false;false;true;true;false;true;true;true;false;false;false;false;true;false;
    true;false;false;true;true;false;true;true;true;false;false;false;false;true;false;true;false;
    false;true;true;false;true;true;false;true;false;true;true;false;false;true;false;false;false;
    true;true;true;true;false;true;false;true;true;false;false;true;false;false;false;true;true;true;
    true;false;true;false;true;true;false;false;true;false;false;false;true;true;true;true;false;
    true;false;true;true;false;false;true;false;false;false;true;true;true;true;false;true;false;
    false;false;false;true;true;true;true;false;true;false;true;true;false;false;true;false;false;
    false;true;true;true;true;false;true;false;true;true;false;false;true;false;false;false;true;
    true;true;true;false;true;false;true;true;false;false;true;false;false;false;true;true;true;true;
    false;true;false;true;true;false;false;true;false;false;false;true|]

  <@
    fun (A :bool array) (RC :bool array) ->

    let bxor (a: bool array) (b: bool array) =
      for i in 0..w-1 do
        a.[i] <- a.[i] <> b.[i]

    let theta (a: bool array) =
      let A = Array.zeroCreate (5*5*w) // Store the result
      let C = Array.zeroCreate (5*w)   // temporary storage
      let D = Array.zeroCreate (5*w)   // temporary storage
      for x in 0..4 do          // Copy input
        for y in 0..4 do
          bxor A.[5*w*x + w*y..5*w*x + w*y + w-1] a.[5*w*x + w*y..5*w*x + w*y + w-1]
      for x in 0..4 do          // C stage
        for y in 0..4 do
          bxor C.[w*x..w*x + w-1] A.[5*w*x + w*y..5*w*x + w*y + w-1]
      for x in 0..4 do          // D stage
        bxor D.[w*x..w*x + w-1] C.[w*((((x-1) % 5) + 5) % 5)..w*((((x-1) % 5) + 5) % 5) + w-1]
        bxor D.[w*x..w*x + w-1] (rot (1 % w) C.[w*((x+1) % 5)..w*((x+1) % 5) + w-1])
      for x in 0..4 do          // A stage
        for y in 0..4 do
          bxor A.[5*w*x + w*y..5*w*x + w*y + w-1] D.[w*x..w*x + w-1]
      for x in 0..4 do          // Cleanup D
        bxor D.[w*x..w*x + w-1] C.[w*((((x-1) % 5) + 5) % 5)..w*((((x-1) % 5) + 5) % 5) + w-1]
        bxor D.[w*x..w*x + w-1] (rot (1 % w) C.[w*((x+1) % 5)..w*((x+1) % 5) + w-1])
      for x in 0..4 do          // Cleanup C
        for y in 0..4 do
          bxor C.[w*x..w*x + w-1] a.[5*w*x + w*y..5*w*x + w*y + w-1]
      for x in 0..4 do
        for y in 0..w-1 do
          clean D.[w*x + y]
      // inverse theta
      for x in 0..4 do          // C stage
        for y in 0..4 do
          bxor C.[w*x..w*x + w-1] A.[5*w*x + w*y..5*w*x + w*y + w-1]
      for i in 0..w-1 do        // A stage
        for xOff in 0..4 do
          for x in 0..4 do
            for y in 0..4 do
              for z in 0..w-1 do
                a.[5*w*x + w*y + z] <- 
                  a.[5*w*x + w*y + z] <> C.[w*((((x-xOff) % 5) + 5) % 5) + ((z + i) % w)]
//                  a.[5*w*x + w*y + z] <> (inverseBits.[64*xOff + i] && 
//                                          C.[w*((((x-xOff) % 5) + 5) % 5) + ((z + i) % 64)])
      for x in 0..4 do          // Cleanup
        for z in 0..w-1 do
          clean C.[w*x + z]
          for y in 0..4 do
            clean a.[5*w*x + w*y + z]
      A

    let thetaNoTemp (a: bool array) =
      let A = Array.zeroCreate (5*5*w) // Store the result
      for x in 0..4 do          // A stage
        for y in 0..4 do
          for z in 0..w-1 do
            A.[5*w*x + w*y + z] <- A.[5*w*x + w*y + z] <> a.[5*w*x + w*y + z]
            for yp in 0..4 do
              A.[5*w*x + w*y + z] <- A.[5*w*x + w*y + z] <> 
                                     a.[5*w*((((x-1) % 5) + 5) % 5) + w*yp + z] <>
                                     a.[5*w*((((x+1) % 5) + 5) % 5) + w*yp + ((((z-1) % w) + w) % w)]
      // inverse theta
      for i in 0..w-1 do        // A stage
        for xOff in 0..4 do
          for x in 0..4 do
            for y in 0..4 do
              for z in 0..w-1 do
                for yp in 0..4 do
                  a.[5*w*x + w*y + z] <- 
                    a.[5*w*x + w*y + z] <> A.[5*w*((((x-xOff) % 5) + 5) % 5) + w*y + ((z + i) % w)]
//                  a.[5*w*x + w*y + z] <> (inverseBits.[64*xOff + i] && 
//                                          C.[w*((((x-xOff) % 5) + 5) % 5) + ((z + i) % 64)])
      for x in 0..4 do          // Cleanup
        for z in 0..w-1 do
          for y in 0..4 do
            clean a.[5*w*x + w*y + z]
      A

    let rhopi (A: bool array) =
      let B = Array.zeroCreate (5*5*w) // temporary storage
      for x in 0..4 do          // Shuffle indices
        for y in 0..4 do
          bxor B.[5*w*y + w*((2*x + 3*y) % 5)..5*w*y + w*((2*x + 3*y) % 5) + w-1] 
               (rot (r.[w*x + y] % w) A.[5*w*x + w*y..5*w*x + w*y + w-1])
      for x in 0..4 do          // Uncompute A
        for y in 0..4 do
          bxor (rot (r.[w*x + y] % w) A.[5*w*x + w*y..5*w*x + w*y + w-1])
               B.[5*w*y + w*((2*x + 3*y) % 5)..5*w*y + w*((2*x + 3*y) % 5) + w-1] 
      for x in 0..4 do
        for y in 0..4 do
          for z in 0..w-1 do
            clean A.[5*w*x + w*y + z]
      B

    let chi (B: bool array) =
      let A = Array.zeroCreate (5*5*w) // Store the result
      for x in 0..4 do         // Compute result
        for y in 0..4 do
          for z in 0..w-1 do
            A.[5*w*x + y*w + z] <- A.[5*w*x + y*w + z] 
              <> B.[5*w*x + y*w + z] <> B.[5*w*((x+2) % 5) + w*y + z]
              <> (B.[5*w*((x+1) % 5) + w*y + z] && B.[5*w*((x+2) % 5) + w*y + z])
      // inverse Chi
      for x in 0..4 do          // Copy output onto B
        for y in 0..4 do
          bxor B.[5*w*x + w*y..5*w*x + w*y + w-1] A.[5*w*x + w*y..5*w*x + w*y + w-1]
      for y in 0..4 do         // Uncompute B
        for x in 0..5 do
          for z in 0..w-1 do
            B.[5*w*((3*x) % 5) + w*y + z] <- B.[5*w*((3*x) % 5) + w*y + z]
              <> A.[5*w*((3*x) % 5) + w*y + z] <> B.[5*w*((3*x + 2) % 5) + w*y + z]
              <> (B.[5*w*((3*x + 2) % 5) + w*y + z] && A.[5*w*((3*x + 1) % 5) + w*y + z])
      for x in 0..4 do
        for y in 0..4 do
          for z in 0..w-1 do
            clean B.[5*w*x + w*y + z]
      A

    let iota (A: bool array) = 
      bxor A.[0..w-1] RC
      A

    iota (chi (rhopi (thetaNoTemp A)))
  @>

let chifun l = 
  let w = 1<<<l
  <@
    fun (B: bool array) ->
      let A = Array.zeroCreate (5*5*w) // Store the result
      for x in 0..4 do         // Compute result
        for y in 0..4 do
          for z in 0..w-1 do
            A.[5*w*x + y*w + z] <- A.[5*w*x + y*w + z] 
              <> B.[5*w*x + y*w + z] <> B.[5*w*((x+2) % 5) + w*y + z]
              <> (B.[5*w*((x+1) % 5) + w*y + z] && B.[5*w*((x+2) % 5) + w*y + z])
      // inverse Chi
      for x in 0..4 do          // Copy output onto B
        for y in 0..4 do
          for z in 0..w-1 do
            B.[5*w*x + w*y + z] <- B.[5*w*x + w*y + z] <> A.[5*w*x + w*y + z]
      for y in 0..4 do         // Uncompute B
        for x in 0..5 do
          for z in 0..w-1 do
            B.[5*w*((3*x) % 5) + w*y + z] <- B.[5*w*((3*x) % 5) + w*y + z]
              <> A.[5*w*((3*x) % 5) + w*y + z] <> B.[5*w*((3*x + 2) % 5) + w*y + z]
              <> (B.[5*w*((3*x + 2) % 5) + w*y + z] && A.[5*w*((3*x + 1) % 5) + w*y + z])
      for x in 0..4 do
        for y in 0..4 do
          for z in 0..w-1 do
            clean B.[5*w*x + w*y + z]
      A
  @>

let chifun2 l = 
  let w = 1<<<l
  <@
    fun (B: bool array) ->
      let A = Array.zeroCreate (5*5*w) // Store the result
      for x in 0..4 do         // XORs
        for y in 0..4 do
          for z in 0..w-1 do
            A.[5*w*x + y*w + z] <- A.[5*w*x + y*w + z] <> B.[5*w*x + y*w + z] <> B.[5*w*((x+2) % 5) + w*y + z]
        for y in 0..4 do
          for z in 0..w-1 do
            A.[5*w*x + y*w + z] <- A.[5*w*x + y*w + z] <> (B.[5*w*((x+1) % 5) + w*y + z] && B.[5*w*((x+2) % 5) + w*y + z])
      // inverse Chi
      for x in 0..4 do          // Copy output onto B
        for y in 0..4 do
          for z in 0..w-1 do
            B.[5*w*x + w*y + z] <- B.[5*w*x + w*y + z] <> A.[5*w*x + w*y + z]
      for x in 0..5 do         // Uncompute B
        for y in 0..4 do 
          for z in 0..w-1 do
            B.[5*w*((3*x) % 5) + w*y + z] <- B.[5*w*((3*x) % 5) + w*y + z] <> A.[5*w*((3*x) % 5) + w*y + z] <> B.[5*w*((3*x + 2) % 5) + w*y + z]
        for y in 0..4 do 
          for z in 0..w-1 do
            B.[5*w*((3*x) % 5) + w*y + z] <- B.[5*w*((3*x) % 5) + w*y + z] <> (B.[5*w*((3*x + 2) % 5) + w*y + z] && A.[5*w*((3*x + 1) % 5) + w*y + z])
      for x in 0..4 do
        for y in 0..4 do
          for z in 0..w-1 do
            clean B.[5*w*x + w*y + z]
      A
  @>

let thetafun l = 
  let w = 1<<<l
  <@
    fun (a: bool array) ->
      let A = Array.zeroCreate (5*5*w) // Store the result
      for x in 0..4 do          // A stage
        for y in 0..4 do
          for z in 0..w-1 do
            A.[5*w*x + w*y + z] <- A.[5*w*x + w*y + z] <> a.[5*w*x + w*y + z]
            for yp in 0..4 do
              A.[5*w*x + w*y + z] <- A.[5*w*x + w*y + z] <> 
                                     a.[5*w*((((x-1) % 5) + 5) % 5) + w*yp + z] <>
                                     a.[5*w*((((x+1) % 5) + 5) % 5) + w*yp + ((((z-1) % w) + w) % w)]
      // inverse theta
      for i in 0..w-1 do        // A stage
        for xOff in 2..3 do
          for x in 0..4 do
            for y in 0..4 do
              for z in 0..w-1 do
                for yp in 0..4 do
                  a.[5*w*x + w*y + z] <- 
                    a.[5*w*x + w*y + z] <> A.[5*w*((((x-xOff) % 5) + 5) % 5) + w*yp + ((z + i) % w)]
//                  a.[5*w*x + w*y + z] <> (inverseBits.[64*xOff + i] && 
//                                          C.[w*((((x-xOff) % 5) + 5) % 5) + ((z + i) % 64)])
      for x in 0..4 do          // Cleanup
        for z in 0..w-1 do
          for y in 0..4 do
            clean a.[5*w*x + w*y + z]
      A
  @>

let inversePositionsWt l =
  let w = 1<<<l
  let b = 25*w
  let n = 12+2*l
  let r = [| 0; 36; 3; 41; 18; 1; 44; 10; 45; 2; 62; 6; 43;
             15; 61; 28; 55; 25; 21; 56; 27; 20; 39; 8; 14 |]
  let inversePositions64 = [| 
    0xDE26BC4D789AF134UL;
    0x09AF135E26BC4D78UL;
    0xEBC4D789AF135E26UL;
    0x7135E26BC4D789AFUL;
    0xCD789AF135E26BC4UL |]
  let inversePositions = Array.zeroCreate 5
  let mutable total = 0

  for z in 0..w..63 do
    for x in 0..4 do
      inversePositions.[x] <- inversePositions.[x] ^^^ (inversePositions64.[x] >>> z)
  for xOff in 0..4 do
    for z in 0..w-1 do
      if ((inversePositions.[xOff] >>> z) &&& 1UL) = 1UL then
        total <- total + 1
  for x in 0..4 do
    printf "%d\n" inversePositions.[x]
  printf "Total: %d\n" total

//Some examples used in the paper
let circ1 =    
    <@
    let f a b = a || b
    let g a b = a && b
    let h a b c d = f a b <> g c d
    h false false false false
    @>

let circ2  =
    <@
    let a = false
    let mutable b = false
    let c = (a&&b)
    b <- b <> c
    b
    @>

let circ3 = 
    <@
    let xor4 (a:bool array) (b:bool array) =
        let c = Array.zeroCreate 4
        for i in 0 .. 3 do
            c.[i] <- a.[i] <> b.[i]
        c
    let and4 (a:bool array) (b:bool array) =
        let d = Array.zeroCreate 4
        for i in 0 .. 3 do
            d.[i] <- a.[i] && b.[i]
        d
    let mutable a = Array.zeroCreate 4
    let b = Array.zeroCreate 4
    let c = Array.zeroCreate 4
    a <- xor4 a b
    and4 a c
@>
