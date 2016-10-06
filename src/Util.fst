(** General utilities *)
module Util
open FStar.Set
open SetExtra

type fin (n:nat) = m:nat{m <= n}

(** Error reporting monads *)
type result 'a =
  | Val : 'a -> result 'a
  | Err : string -> result 'a

val getVal : r:(result 'a){is_Val r} -> Tot 'a
val bind   : result 'a -> ('a -> result 'b) -> result 'b
val bindT  : result 'a -> ('a -> Tot (result 'b)) -> Tot (result 'b)
val foldM  : ('a -> 'b -> result 'a) -> 'a -> l:(list 'b) -> result 'a

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
val hdT       : #a:Type -> l:(list a){List.lengthT l > 0} -> Tot a
val tlT       : #a:Type -> l:(list a){List.lengthT l > 0} -> Tot (list a)
val mems      : #a:Type -> list a -> Tot (set a)
val nthT      : l:list 'a -> i:int{i >= 0 && i < List.lengthT l} -> Tot 'a
val forSomeT  : ('a -> Tot bool) -> list 'a -> Tot bool
val take      : l:list 'a -> i:int{i <= List.length l} -> Tot (list 'a) (decreases i)
val remove    : l:list 'a -> i:nat{i < List.length l} -> Tot (list 'a) (decreases i)
val rotateRec : acc:list 'a -> l:list 'a -> i:nat{i < List.length l} -> Tot (list 'a) (decreases i)
val rotate    : l:list 'a -> i:nat{i < List.length l} -> Tot (list 'a) (decreases i)
val slice     : l:list 'a -> i:nat -> j:nat{i <= j && j < List.length l} -> Tot (list 'a)
val ofInt     : i:nat -> j:int -> Tot (list bool) (decreases j)

val listUnion   : #a:Type -> list a -> list a -> Tot (list a)
val listSymdiff : #a:Type -> list a -> list a -> Tot (list a)

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

(* Need this here so slice will type check *)
val length_remove : l:list 'a -> i:nat{i < List.length l} -> 
  Lemma (requires true)
        (ensures  (List.length (remove l i) = List.length l - i))
  [SMTPat (List.length (remove l i))]
let rec length_remove l i = 
  if i = 0 then ()
  else match l with
    | _::xs -> length_remove xs (i - 1)

let rec rotateRec acc l i =
  if i = 0 then acc@(List.rev l)
  else match l with
    | x::xs -> rotateRec (x::acc) xs (i-1)

let rotate l i =
  ListProperties.rev_length l;
  rotateRec [] (List.rev l) i

let slice l i j = take (remove l i) (j - i + 1)

let rec ofInt i j =
  if j <= 0 then []
  else (i % 2 = 1)::(ofInt (i / 2) (j - 1))

val unins : #a:Type -> list a -> a -> Tot (list a)
let rec unins l y = match l with
  | []    -> [y]
  | x::xs -> if x = y then x::xs else x::(unins xs y)

let listUnion x y = List.fold_leftT unins [] x

val symins : #a:Type -> list a -> a -> Tot (list a)
let rec symins l y = match l with
  | []    -> [y]
  | x::xs -> if x = y then xs else x::(symins xs y)

let listSymdiff x y = List.fold_leftT symins [] x

let listDiff x y = List.filter (fun x -> not (List.mem x y)) x
