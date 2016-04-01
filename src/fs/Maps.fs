module Maps

// Total maps, implemented functionally
module Total = 
  open Util

  type map<'a,'b> = 'a -> 'b

  //val lookup : #a:Type -> #b:Type -> map a b -> a -> Tot b
  let lookup map x = map x

  //val update : #a:Type -> #b:Type -> map a b -> a -> b -> Tot (map a b)
  let update map x y = fun z -> if z = x then y else map z

  //val compose : #a:Type -> #b:Type -> #c:Type -> map a b -> map b c -> Tot (map a c)
  let compose m m' = fun i -> m' (m i)

  //val const : #a:Type -> #b:Type -> b -> Tot (map a b)
  let constant v = fun _ -> v

  type state = map<int, bool>

// Concrete implementation as lists
module Par =
  open Util

  type map<'key,'value> = list<'key * 'value>

  //val dom : map 'k 'v -> Tot (set 'k)
  let rec dom mp = match mp with
    | []    -> fun _ -> false
    | x::xs -> fun y -> (fst x) = y || dom xs y
  //val cod : map 'k 'v -> Tot (set 'v)
  let rec cod mp = match mp with
    | []    -> fun _ -> false
    | x::xs -> fun y -> (snd x) = y || cod xs y

  //val defined : map 'k 'v -> 'k -> Tot bool
  //let defined m k = mem k (dom m)

  let empty = []

  //val find : map 'k 'v -> k:'k -> Tot (option 'v)
  let rec find lst v = match lst with
      | [] -> None
      | (x,y)::xs -> if x = v then Some y else find xs v

  //val lookup : m:(map 'k 'v) -> k:'k{defined m k} -> Tot 'v
  let rec lookup lst v = match lst with
      | (x,y)::xs -> if x = v then y else lookup xs v

  //val lookupT : map 'k 'v -> 'k -> 'v -> Tot 'v
  let rec lookupT lst v def = match lst with
      | [] -> def
      | (x,y)::xs -> if x = v then y else lookupT xs v def

  //val update : m:(map 'k 'v) -> k:'k -> v:'v -> Tot (m':(map 'k 'v){defined m' k})
  let rec update lst k v = match lst with
      | [] -> [(k,v)]
      | (x,y)::xs -> if x = k then (x,v)::xs else (x,y)::(update xs k v)

  let rec map_mp f lst = match lst with
      | [] -> []
      | (x,y)::xs -> (x, f y)::(map_mp f xs)

  //val totalize : #a:Type -> #b:Type -> map a b -> b -> Tot (Total.map a b)
  let totalize mp def = fun k -> match find mp k with
    | None -> def
    | Some b -> b
