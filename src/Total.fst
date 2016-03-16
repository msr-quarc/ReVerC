// Total maps, implemented functionally
module Total
open Util
open FStar.FunctionalExtensionality

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

val const_map : #a:Type -> #b:Type -> b -> Tot (map a b)
let const_map v = fun _ -> v

type state = map int bool

type agree_on (#a:Type) (#b:Type) (mp:map a b) (mp':map a b) (s:set a) =
  forall x. mem x s ==> mp x = mp' x

val agree_on_trans : #a:Type -> #b:Type -> mp:map a b -> mp':map a b -> mp'':map a b -> s:set a ->
  Lemma (requires (agree_on mp mp' s /\ agree_on mp' mp'' s))
        (ensures  (agree_on mp mp'' s))
let agree_on_trans mp mp' mp'' s = ()

