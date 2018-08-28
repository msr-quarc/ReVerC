open System.IO
open System
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

[<EntryPoint>]
let __main argv =
  let res = match argv with
      | [||] -> compile (carryRippleAdder 32) false Eager
      | _    -> compile (carryRippleAdder <| int argv.[0]) false Eager
  File.WriteAllText("adder.qs", printQSharp "adder" res)
  0
