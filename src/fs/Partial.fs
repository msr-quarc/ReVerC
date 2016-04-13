(** Partial maps, implemented as assoc lists *)
module Partial

type t<'key,'value> = list<'key * 'value>

let defined m k = List.exists (fun (k', _) -> k = k') m

let empty = []

let rec find m k = match (List.tryFind (fun (k', v') -> k = k') m) with
  | None -> None
  | Some (_, v) -> Some v

let rec find_def m k dval = match find m k with
  | None -> dval 
  | Some v -> v

let rec update m k v = match m with
    | [] -> [(k, v)]
    | (k', v')::xs -> if k = k' then (k, v)::xs else (k', v')::(update xs k v)

let totalize m dval =
  { Total.elts = m;
    Total.dval = dval }

