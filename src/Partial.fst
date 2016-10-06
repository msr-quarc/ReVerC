(** Partial maps, implemented as assoc lists *)
module Partial
open FStar.Set
open SetExtra

type t (key:eqtype) (value:eqtype) = list (key * value)

val keys     : #key:eqtype -> #value:eqtype -> t key value -> Tot (set key)
val vals     : #key:eqtype -> #value:eqtype -> t key value -> Tot (set value)
val defined  : #key:eqtype -> #value:eqtype -> t key value -> key -> Tot bool
val find     : #key:eqtype -> #value:eqtype -> t key value -> key -> Tot (option value)
val find_def : #key:eqtype -> #value:eqtype -> t key value -> key -> value -> Tot value
val update   : #key:eqtype -> #value:eqtype -> t key value -> key -> value -> Tot (t key value)
val remove   : #key:eqtype -> #value:eqtype -> t key value -> key -> Tot (t key value)
val totalize : #key:eqtype -> #value:eqtype -> t key value -> value -> Tot (Total.t key value)
val mapVals  : #key:eqtype -> #value:eqtype -> #value':eqtype -> 
	       (value -> Tot value') -> t key value -> Tot (t key value')

let rec keys #k #v m = match m with
  | []   -> empty
  | x::xs -> ins (fst x) (keys xs)

let rec vals #k #v m = match m with
  | []   -> empty
  | x::xs -> ins (snd x) (vals xs)

let defined #k #v m key = mem key (keys m)

let rec find #k #v m key = match m with //FStar.List.Tot.assoc key m
  | []   -> None
  | x::xs -> if (fst x) = key then Some (snd x) else find xs key

let rec find_def #k #v m key dval = match find m key with
  | None -> dval 
  | Some v -> v

let rec update #k #v m key vl = match m with
    | [] -> [(key, vl)]
    | (key', vl')::xs -> if key = key' then (key, vl)::xs else (key', vl')::(update xs key vl)

let rec remove #k #v m key = match m with
  | [] -> []
  | (key', v')::xs -> if key = key' then xs else (key', v')::(remove xs key)

let totalize #k #v m dval =
  { Total.elts = m;
    Total.dval = dval }

let mapVals #k #v #u f m = FStar.List.mapT (fun (key, v) -> (key, f v)) m

(** Verification utilities *)
val lookup   : #key:eqtype -> #value:eqtype -> m:t key value -> k:key{defined m k} -> Tot value

let rec lookup #k #v m key = match m with
  | (key', v)::xs -> if key = key' then v else lookup xs key
