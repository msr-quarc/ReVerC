open System.IO
open System
open GenOp
open ReVerC

let carryRippleAdder n =
    <@
    fun (a : bool array) (b : bool array) ->
      let compute_carry (a : bool) (b : bool) (c : bool) =
        (a && (b <> c)) <> (b && c) // a && b <> a && c <> b && c

      let result = Array.zeroCreate(n)
      let mutable carry = false
      result.[0] <- a.[0] <> b.[0]
      for i in 1 .. n-1 do
        carry <- compute_carry a.[i-1] b.[i-1] carry
        result.[i]  <-  a.[i] <> b.[i] <> carry
      result           
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
    @>

let cucarro n =
  if n = 2 then
    <@ 
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
    @>
  else
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
      a.[0] <- a.[0] <> (c && b.[0])
      c <- c <> a.[0]
      b.[0] <- b.[0] <> c
      clean c
    @>

let mult n =
  if n = 2 then
    <@
    fun (a:bool array) (b:bool array) ->
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

      let result = Array.zeroCreate (2*n)
      for i in 0..n-1 do
        ctrlAddModn a.[i] b result.[i..i+n-1]
      result 
    @>
  else
    <@
    fun (a:bool array) (b:bool array) ->
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

      let result = Array.zeroCreate (2*n)
      for i in 0..n-1 do
        ctrlAddModn a.[i] b result.[i..i+n-1]
      result 
    @>

let carryLookaheadAdder n = 
    let adderSize = int (sqrt (float n))
    let imSpacing = 2*(adderSize+1)
    <@
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
      let a' = a.[adderSize .. adderSize*adderSize-1]
      let b' = b.[adderSize .. adderSize*adderSize-1]
      let intermediateResults = Array.zeroCreate (2*adderSize*adderSize-2)
      let mutable carry = a0b0.[adderSize]
      carryRipple a.[0..adderSize-1] b.[0..adderSize-1] false a0b0
      for i in 0 .. adderSize - 2 do
        carryRipple a'.[i*adderSize .. i*adderSize + adderSize-1] 
                    b'.[i*adderSize .. i*adderSize + adderSize-1] 
                    false 
                    intermediateResults.[2*i*(adderSize+1)..(2*i+1)*(adderSize+1) - 1]
        carryRipple a'.[i*adderSize .. i*adderSize + adderSize-1] 
                    b'.[i*adderSize .. i*adderSize + adderSize-1] 
                    true 
                    intermediateResults.[(2*i+1)*(adderSize+1)..2*(i+1)*(adderSize+1) - 1]
      for i in 0 .. adderSize - 2 do
        for j in 0 .. adderSize - 1 do
          result.[i*adderSize + j] <- (carry && intermediateResults.[i*imSpacing + j]) <> 
                                      ((true <> carry) && intermediateResults.[i*imSpacing + adderSize + 1 + j])
        carry <- (carry && intermediateResults.[i*imSpacing+adderSize]) <> 
                 ((true <> carry) && intermediateResults.[i*imSpacing+2*adderSize+1])
      Array.concat [a0b0.[0..adderSize-1]; result]
    @>

[<EntryPoint>]
let __main argv =
  let n = match argv with
      | [||] -> 32
      | _    -> int argv.[0]
  let src =
      qSharpHeader +
      printQSharpBody "oopAdder" (compile (carryRippleAdder n) false Eager) + "\n\n" +
      printQSharpBody "modAdder" (compile (addMod n) false Eager) + "\n\n" +
      printQSharpBody "cucarroAdder" (compile (cucarro n) false Eager) + "\n\n" +
      printQSharpBody "carryLookaheadAdder" (compile (carryLookaheadAdder n) false Eager) + "\n\n" +
      printQSharpBody "oopMultiplier" (compile (mult n) false Eager) + "\n}"
  File.WriteAllText("arithLib.qs", src)
  0
