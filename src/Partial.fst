// Partial maps, implemented functionally
module Partial
open Util

type map (#a:Type) (d:set a) (b:Type) = v:a{d v} -> Tot b

val update : #a:Type -> #d:set a -> #b:Type ->
  map d b -> v:a -> b -> Tot (map (ins v d) b)
let update d map x y = fun z -> if z = x then y else map z

val lookup : #a:Type -> d:set a -> #b:Type -> map d b -> x:a{mem x d} -> Tot b
let lookup d map x = map x

val dom : #a:Type -> d:set a -> #b:Type -> map d b -> Tot (set a)
let dom d m = d
