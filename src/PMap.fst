module PMap

// Concrete implementation as lists
type t (key:Type) (value:Type) = list (key * value)

val domain : t 'key 'value -> Tot (list 'key)
let domain m = List.mapT (fun (x, _) -> x) m

val defined : t 'key 'value -> 'key -> Tot bool
let defined m k = List.memT k (domain m)

let empty = []

val find : m:(t 'key 'value) -> k:'key{defined m k} -> Tot 'value
let rec find lst v = match lst with
    | (x,y)::xs -> if x = v then y else find xs v
    | _::xs -> find xs v

val update : m:(t 'key 'value) -> k:'key -> v:'value ->
  Tot (m':(t 'key 'value){defined m' k})
let rec update lst k v = match lst with
    | [] -> [(k,v)]
    | (x,y)::xs -> if x = k then (x,v)::xs else (x,y)::(update xs k v)
    | x::xs -> x::(update xs k v)

// Implementation as functions
(*
open Set

type pmap (key:Type) (dom:set key) (value:Type) = k:key{mem k dom} -> value

val emptypmap : #k:Type -> #v:Type -> Tot (pmap k Set.empty v)
//let emptypmap = fun _ -> false

val updatepmap : #k:Type -> #v:Type -> #d:(set k) ->
  m:(pmap k d v) -> key:k -> value:v -> Tot (pmap k (union d (singleton key)) v)
let updatepmap d m k v = fun x -> if x = k then v else m x
*)
