module FStar.List
let isEmpty l = l = []
let mem x = List.exists (fun y -> x = y)
let memT = mem
let hd = List.head
let tl = List.tail
let tail = List.tail
let nth = List.nth
let length = List.length
let rev = List.rev
let map = List.map
let mapT = map
let mapi = List.mapi
let map2 = List.map2
let map3 = List.map3
let iter = List.iter
let iter2 = List.iter2
let iteri = List.iteri
let partition = List.partition
let append = List.append
let rev_append l1 l2 = append l2 (rev l1)
let fold_left = List.fold
let fold_right = List.foldBack
let fold_left2 = List.fold2
let fold_right2 = List.foldBack2
let collect = List.collect
let unzip = List.unzip
let unzip3 = List.unzip3
let filter = List.filter
let sortWith = List.sortWith
let for_all = List.forall
let forall2 = List.forall2
let tryFind = List.tryFind
let tryFindT = tryFind
let find = tryFind
let tryPick = List.tryPick
let flatten = List.concat
let split = unzip
let choose = List.choose
let existsb = List.exists
let contains = mem
let zip = List.zip
let zip3 = List.zip3
let unique l = // removes all but last occurrence to coincide with the Batteries implementation
  let rec uni l acc = match l with
    | [] -> acc
    | x::xs -> if mem x xs then uni xs acc else uni xs (x::acc)
  in
    rev (uni l [])
