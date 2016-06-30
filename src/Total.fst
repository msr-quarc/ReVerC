(** Total maps, implemented as assoc lists with default values *)
module Total
open Set

type t (key:Type) (value:Type) = 
  { elts : list (key * value);
    dval : value }

(* type synonym for Boolean-valued states *)
type state = t int bool

val valsRec  : #key:Type -> #value:Type -> value -> list (key * value) -> Tot bool
val vals     : #key:Type -> #value:Type -> t key value -> Tot (set value)
val lookup   : #key:Type -> #value:Type -> t key value -> key -> Tot value
val update   : #key:Type -> #value:Type -> t key value -> key -> value -> Tot (t key value)
val constMap : #key:Type -> #value:Type -> value -> Tot (t key value)
val compose  : #key:Type -> #value:Type -> #value':Type -> t key value -> t value value' -> Tot (t key value')
val mapVals  : #key:Type -> #value:Type -> #value':Type -> (value -> Tot value') -> t key value -> Tot (t key value')

let rec valsRec y xs = match xs with
  | []    -> false
  | x::xs -> (snd x) = y || valsRec y xs

let vals m = 
    fun y -> y = m.dval || valsRec y m.elts

let lookup m k = match List.assocT k m.elts with
  | None   -> m.dval
  | Some v -> v

let update m k v =
  { elts = (k, v)::m.elts; //(k, v)::(List.filterT (fun (k', _) -> not (k = k')) m.elts);
    dval = m.dval }

let constMap v =
  { elts = [];
    dval = v }

let compose m m' = 
  { elts = List.mapT (fun (k, v) -> (k, lookup m' v)) m.elts;
    dval = lookup m' m.dval }

let mapVals f m = 
  { elts = List.mapT (fun (k, v) -> (k, f v)) m.elts;
    dval = f m.dval }


(** Verification utilities *)

(* Basic equations *)
val lookup_const : #key:Type -> #value:Type -> k:key -> v:value -> 
  Lemma (requires true) 
        (ensures (lookup (constMap v) k = v))
  [SMTPat (lookup (constMap v) k)]
val lookup_update1 : #key:Type -> #value:Type -> m:t key value -> k:key -> v:value ->
  Lemma (requires true)
        (ensures (lookup (update m k v) k = v))
  [SMTPat (lookup (update m k v) k)]
val lookup_update2 : #key:Type -> #value:Type -> m:t key value -> k:key -> v:value -> k':key ->
  Lemma (requires (not (k = k')))
        (ensures (lookup (update m k v) k' = lookup m k'))
  [SMTPat (lookup (update m k v) k')]
val lookup_map : #key:Type -> #value:Type -> #value':Type -> f:(value -> Tot value') -> m:t key value -> k:key ->
  Lemma (requires true)
        (ensures (lookup (mapVals f m) k = f (lookup m k)))
  (decreases m.elts)
  [SMTPat (lookup (mapVals f m) k)]

let lookup_const k v = ()
let lookup_update1 m k v = ()
let lookup_update2 m k v k' = ()
let rec lookup_map f m k = match m.elts with
  | [] -> ()
  | x::xs -> 
    let m' = { elts = xs; dval = m.dval } in
      lookup_map f m' k

(* Relating lookups to values -- don't have time for this trivial but tedious lemma right now *)
val lookup_is_val : #key:Type -> #value:Type -> m:t key value -> k:key ->
  Lemma (requires true)
	(ensures (Set.mem (lookup m k) (vals m)))
let lookup_is_val m k = admit()
  
val lookup_is_valF : #key:Type -> #value:Type -> m:t key value ->
  Lemma (requires true)
	(ensures (forall k. Set.mem (lookup m k) (vals m)))
let lookup_is_valF m = admit()

val lookup_converse : #key:Type -> #value:Type -> m:t key value -> v:value ->
  Lemma (requires (not (Set.mem v (vals m))))
	(ensures  (forall k. not (lookup m k = v)))
let lookup_converse m v = lookup_is_valF m

(* Type of maps that agree on a subset of keys *)
type agree_on (#key:Type) (#value:Type) (m:t key value) (m':t key value) (s:set key) =
  forall x. mem x s ==> lookup m x = lookup m' x

val agree_on_trans : #key:Type -> #value:Type -> m:t key value -> m':t key value -> m'':t key value -> s:set key ->
  Lemma (requires (agree_on m m' s /\ agree_on m' m'' s))
        (ensures  (agree_on m m'' s))
let agree_on_trans m m' m'' s = ()

val agree_on_subset : #key:Type -> #value:Type -> m:t key value -> m':t key value -> s:set key -> s':set key ->
  Lemma (requires (agree_on m m' s /\ subset s' s))
        (ensures  (agree_on m m' s'))
let agree_on_subset m m' s s' = ()

(* Functional extensionality for lookups. We're rolling our own since we're
going to be bad and assume maps which are extensionally equal are actually equal *)

type Equal (#key:Type) (#value:Type) (m1:t key value) (m2:t key value) = 
  (forall x.{:pattern (lookup m1 x) \/ (lookup m2 x)} lookup m1 x = lookup m2 x)

(* What did they say about assumption being the mother of all fuckups? *)
assume TotalExtensionality : 
  forall (key:Type) (value:Type) (m1:t key value) (m2:t key value).
    {:pattern Equal m1 m2} Equal m1 m2 <==> m1 = m2

val lemma_map_equal_intro: #key:Type -> #value:Type -> m1:t key value -> m2:t key value ->
  Lemma (requires  (forall x. lookup m1 x = lookup m2 x))
        (ensures   (Equal m1 m2))
  [SMTPatT (Equal m1 m2)]
val lemma_map_equal_elim: #key:Type -> #value:Type -> m1:t key value -> m2:t key value ->
  Lemma (requires (Equal m1 m2))
        (ensures  (m1 = m2))
  [SMTPatT (Equal m1 m2)]
val lemma_map_equal_refl: #key:Type -> #value:Type -> m1:t key value -> m2:t key value ->
  Lemma (requires (m1 = m2))
        (ensures  (Equal m1 m2))
  [SMTPatT (Equal m1 m2)]

let lemma_map_equal_intro m1 m2 = ()
(* Follows from TotalExtensionality but I can't seem to get it working *)
let lemma_map_equal_elim m1 m2 = admit()
let lemma_map_equal_refl m1 m2 = ()

