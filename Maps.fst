(* Maps - Various types of maps.
   Maps implemented functionally are implemented as functions in FStar.
   In particular, they're updated by creating a new function that agrees
   with the old on all inputs except the update input. This is particularly
   useful for proofs, but is extremely inefficient.
   Partial vs total maps should be an obvious distinction. Finite maps are
   maps for the naturals up to n into some type.
   Lookups always succeed, given inputs that typecheck, find may return
   nothing *)

// Total maps, implemented functionally
module Total
open Util
open FunctionalExtensionality

type map (a:Type) (b:Type) = a -> Tot b

type Equal (#a:Type) (#b:Type) (m1:map a b) (m2:map a b) = FEq m1 m2
val lemma_map_equal_intro: #a:Type -> #b:Type -> m1:map a b -> m2:map a b ->
  Lemma (requires  (forall x. m1 x = m2 x))
        (ensures   (Equal m1 m2))
  [SMTPatT (Equal m1 m2)]
val lemma_map_equal_elim: #a:Type -> #b:Type -> m1:map a b -> m2:map a b ->
  Lemma (requires (Equal m1 m2))
        (ensures  (m1 = m2))
  [SMTPatT (Equal m1 m2)]
val lemma_map_equal_refl: #a:Type -> #b:Type -> m1:map a b -> m2:map a b ->
  Lemma (requires (m1 = m2))
        (ensures  (Equal m1 m2))
  [SMTPatT (Equal m1 m2)]
let lemma_map_equal_intro m1 m2 = ()
let lemma_map_equal_elim m1 m2 = ()
let lemma_map_equal_refl m1 m2 = ()

val lookup : #a:Type -> #b:Type -> map a b -> a -> Tot b
let lookup map x = map x

val update : #a:Type -> #b:Type -> map a b -> a -> b -> Tot (map a b)
let update map x y = fun z -> if z = x then y else map z

val compose : #a:Type -> #b:Type -> #c:Type -> map a b -> map b c -> Tot (map a c)
let compose m m' = fun i -> m' (m i)

val const : #a:Type -> #b:Type -> b -> Tot (map a b)
let const v = fun _ -> v

type state = map int bool

type agree_on (#a:Type) (#b:Type) (mp:map a b) (mp':map a b) (s:set a) =
  forall x. mem x s ==> mp x = mp' x

val agree_on_trans : #a:Type -> #b:Type -> mp:map a b -> mp':map a b -> mp'':map a b -> s:set a ->
  Lemma (requires (agree_on mp mp' s /\ agree_on mp' mp'' s))
        (ensures  (agree_on mp mp'' s))
let agree_on_trans mp mp' mp'' s = ()

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

// Finite maps from 0 to n inclusive
module Finite
open Util

type map (n:nat) (b:Type) = l:(list b){List.length l >= n}

val lookup : #b:Type -> i:nat -> map (i+1) b -> Tot b (decreases i)
let rec lookup i map =
  if i = 0
  then match map with (x::_)  -> x
  else match map with (_::xs) -> lookup (i-1) xs

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

// Concrete implementation as lists
module Par
open Util

type map (key:Type) (value:Type) = list (key * value)

val dom : map 'k 'v -> Tot (set 'k)
let rec dom mp = match mp with
  | []    -> fun _ -> false
  | x::xs -> fun y -> (fst x) = y || dom xs y
val cod : map 'k 'v -> Tot (set 'v)
let rec cod mp = match mp with
  | []    -> fun _ -> false
  | x::xs -> fun y -> (snd x) = y || cod xs y

val defined : map 'k 'v -> 'k -> Tot bool
let defined m k = mem k (dom m)

let empty = []

val find : map 'k 'v -> k:'k -> Tot (option 'v)
let rec find lst v = match lst with
    | [] -> None
    | (x,y)::xs -> if x = v then Some y else find xs v

val lookup : m:(map 'k 'v) -> k:'k{defined m k} -> Tot 'v
let rec lookup lst v = match lst with
    | (x,y)::xs -> if x = v then y else lookup xs v

val lookupT : map 'k 'v -> 'k -> 'v -> Tot 'v
let rec lookupT lst v def = match lst with
    | [] -> def
    | (x,y)::xs -> if x = v then y else lookupT xs v def

val update : m:(map 'k 'v) -> k:'k -> v:'v -> Tot (m':(map 'k 'v){defined m' k})
let rec update lst k v = match lst with
    | [] -> [(k,v)]
    | (x,y)::xs -> if x = k then (x,v)::xs else (x,y)::(update xs k v)

val totalize : #a:Type -> #b:Type -> map a b -> b -> Tot (Total.map a b)
let totalize mp def = fun k -> match find mp k with
  | None -> def
  | Some b -> b
