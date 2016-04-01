module Util

// Error reporting monads
type result<'a> =
  | Val of 'a
  | Err of string

//val bind : result 'a -> ('a -> result 'b) -> result 'b
//val bindT : result 'a -> ('a -> Tot (result 'b)) -> Tot (result 'b)
let bind v f = match v with
  | Val x -> f x
  | Err s -> Err s
let bindT v f = match v with
  | Val x -> f x
  | Err s -> Err s

//val foldM : ('a -> 'b -> result 'a) -> 'a -> l:(list 'b) -> result 'a
let rec foldM f a lst = match lst with
  | [] -> Val a
  | x::xs -> bind (f a x) (fun res -> foldM f res xs)

// Extra list operations

//val nthT : list 'a -> int -> Tot 'a
let rec nthT l i = match l with
  | x::xs -> if i = 0 then x else nthT xs (i-1)

//val for_someT: ('a -> Tot bool) -> list 'a -> Tot bool
let rec for_someT f l = match l with
    | [] -> false
    | hd::tl -> if f hd then true else for_someT f tl

//val take : l:(list 'a) -> i:int{i < List.length l} -> Tot (list 'a) (decreases i)
let rec take l i =
  if i <= 0 then []
  else match l with
    | x::xs -> x::(take xs (i - 1))

//val remove : l:(list 'a) -> i:nat{i < List.length l} ->
//  Tot (l':(list 'a){List.length l' = List.length l - i}) (decreases i)
let rec remove l i =
  if i = 0 then l
  else match l with
    | _::xs -> remove xs (i - 1)

//val rotate_rec : acc:(list 'a) -> l:(list 'a) -> i:nat{i < List.length l} -> Tot (list 'a) (decreases i)
let rec rotate_rec acc l i =
  if i = 0 then acc@(List.rev l)
  else match l with
    | x::xs -> rotate_rec (x::acc) xs (i-1)

//val rotate : l:(list 'a) -> i:nat{i < List.length l} -> Tot (list 'a) (decreases i)
let rotate l i = rotate_rec [] (List.rev l) i

//val slice : l:(list 'a) -> i:nat -> j:nat{i <= j && j < List.length l} -> Tot (list 'a)
let slice l i j = take (remove l i) (j - i + 1)

//val of_int : i:nat -> j:int -> Tot (list bool) (decreases j)
let rec of_int i j =
  if j <= 0 then []
  else (i % 2 = 1)::(of_int (i / 2) (j - 1))

let rec listmem y l = match l with
  | [] -> false
  | x::xs -> x = y || listmem y xs

let hd = List.head
let tl = List.tail

module IO =
  let string_of_int x = string x
  let print_string s = printf "%s\n" s
