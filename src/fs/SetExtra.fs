(** Functional sets *)
module SetExtra

type set<'a when 'a:comparison>  = Set<'a>

let mem          = Set.contains
let empty        = Set.empty
let singleton    = Set.singleton
let union        = Set.union
let intersection = Set.intersect
let diff         = Set.difference
let ins          = Set.add
let fold         = Set.fold
