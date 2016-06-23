(** Partial maps, implemented as assoc lists *)
module Partial
open Set

type t (key:Type) (value:Type) = list (key * value)

val keys     : #key:Type -> #value:Type -> t key value -> Tot (set key)
val vals     : #key:Type -> #value:Type -> t key value -> Tot (set value)
val defined  : #key:Type -> #value:Type -> t key value -> key -> Tot bool
val find     : #key:Type -> #value:Type -> t key value -> key -> Tot (option value)
val find_def : #key:Type -> #value:Type -> t key value -> key -> value -> Tot value
val update   : #key:Type -> #value:Type -> t key value -> key -> value -> Tot (t key value)
val remove   : #key:Type -> #value:Type -> t key value -> key -> Tot (t key value)
val totalize : #key:Type -> #value:Type -> t key value -> value -> Tot (Total.t key value)
val mapVals  : #key:Type -> #value:Type -> #value':Type -> 
	       (value -> Tot value) -> t key value -> Tot (t key value')

let rec keys m = match m with
  | []    -> fun _ -> false
  | x::xs -> fun y -> (fst x) = y || keys xs y

let rec vals m = match m with
  | []    -> fun _ -> false
  | x::xs -> fun y -> (snd x) = y || vals xs y

let defined m k = mem k (keys m)

let rec find m k = List.assocT k m

let rec find_def m k dval = match find m k with
  | None -> dval 
  | Some v -> v

let rec update m k v = match m with
    | [] -> [(k, v)]
    | (k', v')::xs -> if k = k' then (k, v)::xs else (k', v')::(update xs k v)

let rec remove m k = match m with
  | [] -> []
  | (k', v')::xs -> if k = k' then xs else (k', v')::(remove xs k)

let totalize m dval =
  { Total.elts = m;
    Total.dval = dval }

let mapVals f m = List.mapT (fun (k, v) -> (k, f v)) m

(** Verification utilities *)
val lookup   : #key:Type -> #value:Type -> m:t key value -> k:key{defined m k} -> Tot value

let rec lookup m k = match m with
  | (k', v)::xs -> if k = k' then v else lookup xs k
