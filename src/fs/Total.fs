(** Total maps, implemented as assoc lists with default values *)
module Total

type t<'key,'value> = 
  { elts : list<'key * 'value>;
    dval : 'value }

(* type synonym for Boolean-valued states *)
type state = t<int,bool>

let keys m = List.fold (fun s x -> Set.add (fst x) s) Set.empty m.elts

let lookup m k = match (List.tryFind (fun (k', v') -> k = k') m.elts) with
  | None   -> m.dval
  | Some (_, v) -> v

let update m k v =
  { elts = (k, v)::(List.filter (fun (k', _) -> not (k = k')) m.elts);
    dval = m.dval }

let delete m k =
  { elts = List.filter (fun (k', _) -> not (k = k')) m.elts;
    dval = m.dval }

let constMap v =
  { elts = [];
    dval = v }

let compose m m' = 
  { elts = List.map (fun (k, v) -> (k, lookup m' v)) m.elts;
    dval = lookup m' m.dval }

let mapVals f m = 
  { elts = List.map (fun (k, v) -> (k, f v)) m.elts;
    dval = f m.dval }

let mapKeyVals f m = 
  { elts = List.map (fun (k, v) -> (k, f (k, v))) m.elts;
    dval = m.dval }

