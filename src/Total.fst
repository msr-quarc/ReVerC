(** Total maps, implemented as assoc lists with default values *)
module Total
open FStar.Set
open SetExtra

type t (key:eqtype) (value:eqtype) = 
  { elts : list (key * value);
    dval : value }

(* type synonym for Boolean-valued states *)
type state = t int bool

val keys     : #key:eqtype -> #value:eqtype -> t key value -> Tot (set key)
val vals     : #key:eqtype -> #value:eqtype -> t key value -> Tot (set value)
val lookup   : #key:eqtype -> #value:eqtype -> t key value -> key -> Tot value
val update   : #key:eqtype -> #value:eqtype -> t key value -> key -> value -> Tot (t key value)
val delete   : #key:eqtype -> #value:eqtype -> t key value -> key -> Tot (t key value)
val constMap : #key:eqtype -> #value:eqtype -> value -> Tot (t key value)
val compose  : #key:eqtype -> #value:eqtype -> #value':eqtype -> t key value -> t value value' -> Tot (t key value')
val mapVals  : #key:eqtype -> #value:eqtype -> #value':eqtype -> (value -> Tot value') -> t key value -> Tot (t key value')

let keys #k #v m = FStar.List.Tot.fold_left (fun s x -> ins (fst x) s) empty m.elts

let vals #k #v m = ins m.dval (FStar.List.Tot.fold_left (fun s x -> ins (snd x) s) empty m.elts)

let lookup #k #v m key = match FStar.List.Tot.assoc key m.elts with
  | None   -> m.dval
  | Some v -> v

let update #k #v m key vl =
  { elts = (key, vl)::m.elts; //(k, v)::(FStar.List.filterT (fun (k', _) -> not (k = k')) m.elts);
    dval = m.dval }

let delete #k #v m key =
  { elts = FStar.List.Tot.filter (fun (k', _) -> not (key = k')) m.elts;
    dval = m.dval }

let constMap #k #v dv =
  { elts = [];
    dval = dv }

let compose #k #v #u m m' = 
  { elts = FStar.List.Tot.map (fun (k, v) -> (k, lookup m' v)) m.elts;
    dval = lookup m' m.dval }

let mapVals #k #v #u f m = 
  { elts = FStar.List.Tot.map (fun (k, v) -> (k, f v)) m.elts;
    dval = f m.dval }


(** Verification utilities *)

(* Basic equations *)
val lookup_const : #key:eqtype -> #value:eqtype -> k:key -> v:value -> 
  Lemma (requires true) 
        (ensures (lookup (constMap v) k = v))
  [SMTPat (lookup (constMap v) k)]
val lookup_update1 : #key:eqtype -> #value:eqtype -> m:t key value -> k:key -> v:value ->
  Lemma (requires true)
        (ensures (lookup (update m k v) k = v))
  [SMTPat (lookup (update m k v) k)]
val lookup_update2 : #key:eqtype -> #value:eqtype -> m:t key value -> k:key -> v:value -> k':key ->
  Lemma (requires (not (k = k')))
        (ensures (lookup (update m k v) k' = lookup m k'))
  [SMTPat (lookup (update m k v) k')]
val lookup_map : #key:eqtype -> #value:eqtype -> #value':eqtype -> f:(value -> Tot value') -> m:t key value -> k:key ->
  Lemma (requires true)
        (ensures (lookup (mapVals f m) k = f (lookup m k)))
  (decreases m.elts)
  [SMTPat (lookup (mapVals f m) k)]

let lookup_const #k #v k v = ()
let lookup_update1 #k #v m k v = ()
let lookup_update2 #k #v m k v k' = ()
let rec lookup_map #k #v #val' f m k = match m.elts with
  | [] -> ()
  | x::xs -> 
    let m' = { elts = xs; dval = m.dval } in
      lookup_map f m' k

(* Obvious axioms related to the codomain of a total map *)
val lookup_is_val : #key:eqtype -> #value:eqtype -> m:t key value -> k:key ->
  Lemma (requires true)
	(ensures (Set.mem (lookup m k) (vals m)))
let lookup_is_val #k #v m k = admit()
  
val lookup_is_valF : #key:eqtype -> #value:eqtype -> m:t key value ->
  Lemma (requires true)
	(ensures (forall k. Set.mem (lookup m k) (vals m)))
let lookup_is_valF #k #v m = admit()

val lookup_converse : #key:eqtype -> #value:eqtype -> m:t key value -> v:value ->
  Lemma (requires (not (Set.mem v (vals m))))
	(ensures  (forall k. not (lookup m k = v)))
let lookup_converse #k #v m v = lookup_is_valF m

val lookup_converse2 : #key:eqtype -> #value:eqtype -> m:t key value -> v:value ->
  Lemma (requires (forall k. not (lookup m k = v)))
	(ensures  (not (Set.mem v (vals m))))
let lookup_converse2 #k #v m v = admit()

val lookup_subset : #key:eqtype -> #value:eqtype -> m:t key value -> k:key -> v:value ->
  Lemma (requires True)
        (ensures (subset (vals (update m k v)) (ins v (vals m))))
let lookup_subset #k #v m k v = admit()

val update_subset : #key:eqtype -> #value:eqtype -> m:t key value -> k:key -> v:value ->
  Lemma (requires True)
        (ensures (subset (rem (lookup m k) (vals m)) (vals (update m k v))))
let update_subset #k #v m k v = admit()

val destruct_vals : #key:eqtype -> #value:eqtype -> x:(key * value) -> m:t key value -> m':t key value ->
  Lemma (requires (m.elts = x::m'.elts /\ m.dval = m'.dval))
        (ensures  (Set.equal (vals m) (ins (snd x) (vals m'))))
let destruct_vals #k #v x m m' = admit()

val destruct_val : #key:eqtype -> #value:eqtype -> x:(key * value) -> m:t key value ->
  Lemma (requires (exists xs. m.elts = x::xs))
        (ensures  (Set.mem (snd x) (vals m)))
let destruct_val #k #v x m = admit()

(* Type of maps that agree on a subset of keys *)
type agree_on (#key:eqtype) (#value:eqtype) (m:t key value) (m':t key value) (s:set key) =
  forall x. mem x s ==> lookup m x = lookup m' x

val agree_on_trans : #key:eqtype -> #value:eqtype -> m:t key value -> m':t key value -> m'':t key value -> s:set key ->
  Lemma (requires (agree_on m m' s /\ agree_on m' m'' s))
        (ensures  (agree_on m m'' s))
let agree_on_trans #k #v m m' m'' s = ()

val agree_on_subset : #key:eqtype -> #value:eqtype -> m:t key value -> m':t key value -> s:set key -> s':set key ->
  Lemma (requires (agree_on m m' s /\ subset s' s))
        (ensures  (agree_on m m' s'))
let agree_on_subset #k #v m m' s s' = ()

(* Functional extensionality for lookups. We're rolling our own since we're
going to be bad and assume maps which are extensionally equal are actually equal *)

type equal (#key:eqtype) (#value:eqtype) (m1:t key value) (m2:t key value) = 
  (forall x.{:pattern (lookup m1 x) \/ (lookup m2 x)} lookup m1 x = lookup m2 x)

(* What did they say about assumption being the mother of all fuckups? *)
assume TotalExtensionality : 
  forall (key:eqtype) (value:eqtype) (m1:t key value) (m2:t key value).
    {:pattern equal m1 m2} equal m1 m2 <==> m1 = m2

val lemma_map_equal_intro: #key:eqtype -> #value:eqtype -> m1:t key value -> m2:t key value ->
  Lemma (requires  (forall x. lookup m1 x = lookup m2 x))
        (ensures   (equal m1 m2))
  [SMTPatT (equal m1 m2)]
val lemma_map_equal_elim: #key:eqtype -> #value:eqtype -> m1:t key value -> m2:t key value ->
  Lemma (requires (equal m1 m2))
        (ensures  (m1 = m2))
  [SMTPatT (equal m1 m2)]
val lemma_map_equal_refl: #key:eqtype -> #value:eqtype -> m1:t key value -> m2:t key value ->
  Lemma (requires (m1 = m2))
        (ensures  (equal m1 m2))
  [SMTPatT (equal m1 m2)]

let lemma_map_equal_intro #k #v m1 m2 = ()
(* Follows from TotalExtensionality but I can't seem to get it working *)
let lemma_map_equal_elim #k #v m1 m2 = admit()
let lemma_map_equal_refl #k #v m1 m2 = ()

