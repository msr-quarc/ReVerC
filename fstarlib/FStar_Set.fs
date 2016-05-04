module FStar.Set
  type set<'T when 'T:comparison> = Set<'T>
  let empty =  Set.empty
  let singleton = Set.singleton
  let union = Set.union
  let intersect = Set.intersect
  let complement x = Set.empty
  let mem = Set.contains
  let equal x y = Set.isSubset x y && Set.isSubset y x
