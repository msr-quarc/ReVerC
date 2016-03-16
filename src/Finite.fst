// Finite maps from 0 to n inclusive
module Finite
open Util

type map (n:nat) (b:Type) = l:(list b){List.length l >= n}

val lookup : #b:Type -> i:nat -> map (i+1) b -> Tot b (decreases i)
let rec lookup i map =
  if i = 0
  then match map with | x::_  -> x
  else match map with | _::xs -> lookup (i-1) xs

val update : #b:Type -> i:nat -> b -> map i b -> Tot (map (i+1) b) (decreases i)
let rec update i y map =
  if i = 0
  then match map with
    | [] -> [y]
    | x::xs -> y::xs
  else match map with
    | x::xs -> x::(update (i-1) y xs)

val extend : #b:Type -> #i:nat -> b -> map i b -> Tot (map (i+1) b)
let extend i y map = map@[y]
