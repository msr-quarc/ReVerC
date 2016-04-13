(** General utilities *)
module Util

(** Error reporting monads *)
type result<'a> =
  | Val of 'a
  | Err of string

let getVal r = match r with
  | Val v -> v

let bind v f = match v with
  | Val x -> f x
  | Err s -> Err s
let bindT v f = match v with
  | Val x -> f x
  | Err s -> Err s

let rec foldM f a lst = match lst with
  | [] -> Val a
  | x::xs -> bind (f a x) (fun res -> foldM f res xs)

(** Auxiliary list operations *)
let hdT l = match l with | x::xs -> x
let tlT l = match l with | x::xs -> xs

let mems l = fun i -> List.mem i l

let rec nthT l i = match l with
  | x::xs -> if i = 0 then x else nthT xs (i-1)

let rec forSomeT f l = match l with
    | [] -> false
    | hd::tl -> if f hd then true else forSomeT f tl

let rec take l i =
  if i <= 0 then []
  else match l with
    | x::xs -> x::(take xs (i - 1))

let rec remove l i =
  if i = 0 then l
  else match l with
    | _::xs -> remove xs (i - 1)

let rec rotateRec acc l i =
  if i = 0 then acc@(List.rev l)
  else match l with
    | x::xs -> rotateRec (x::acc) xs (i-1)

let rotate l i = rotateRec [] (List.rev l) i

let slice l i j = take (remove l i) (j - i + 1)

let rec ofInt i j =
  if j <= 0 then []
  else (i % 2 = 1)::(ofInt (i / 2) (j - 1))
