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
val hdT       : #a:Type -> l:(list a){FStar.List.Tot.length l > 0} -> Tot a
val tlT       : #a:Type -> l:(list a){FStar.List.Tot.length l > 0} -> Tot (list a)
val mems      : #a:eqtype -> list a -> Tot (set a)
val nthT      : l:list 'a -> i:int{i >= 0 && i < FStar.List.Tot.length l} -> Tot 'a
val forSomeT  : ('a -> Tot bool) -> list 'a -> Tot bool
val take      : l:list 'a -> i:int{i <= FStar.List.Tot.length l} -> Tot (list 'a) (decreases i)
val remove    : l:list 'a -> i:nat{i < FStar.List.Tot.length l} -> Tot (list 'a) (decreases i)
val rotateRec : acc:list 'a -> l:list 'a -> i:nat{i < FStar.List.Tot.length l} -> Tot (list 'a) (decreases i)
val rotate    : l:list 'a -> i:nat{i < FStar.List.Tot.length l} -> Tot (list 'a) (decreases i)
val slice     : l:list 'a -> i:nat -> j:nat{i <= j && j < FStar.List.Tot.length l} -> Tot (list 'a)
val ofInt     : i:nat -> j:int -> Tot (list bool) (decreases j)

val listUnion   : #a:eqtype -> list a -> list a -> Tot (list a)
val listSymdiff : #a:eqtype -> list a -> list a -> Tot (list a)

let hdT #a l = match l with | x::xs -> x
let tlT #a l = match l with | x::xs -> xs

let rec mems #a l = match l with
  | []   -> empty
  | x::xs -> ins x (mems xs)

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
val length_remove : l:list 'a -> i:nat{i < FStar.List.Tot.length l} -> 
  Lemma (requires true)
        (ensures  (FStar.List.Tot.length (remove l i) = FStar.List.Tot.length l - i))
  [SMTPat (FStar.List.Tot.length (remove l i))]
let rec length_remove l i = 
  if i = 0 then ()
  else match l with
    | _::xs -> length_remove xs (i - 1)

let rec rotateRec acc l i =
  if i = 0 then acc@(FStar.List.Tot.rev l)
  else match l with
    | x::xs -> rotateRec (x::acc) xs (i-1)

let rotate l i =
  FStar.ListProperties.rev_length l;
  rotateRec [] (FStar.List.Tot.rev l) i

let slice l i j = take (remove l i) (j - i + 1)

let rec ofInt i j =
  if j <= 0 then []
  else (i % 2 = 1)::(ofInt (i / 2) (j - 1))

val unins : #a:eqtype -> list a -> a -> Tot (list a)
let rec unins #a l y = match l with
  | []    -> [y]
  | x::xs -> if x = y then x::xs else x::(unins xs y)

let listUnion #a x y = FStar.List.Tot.fold_left unins [] x

val symins : #a:eqtype -> list a -> a -> Tot (list a)
let rec symins #a l y = match l with
  | []    -> [y]
  | x::xs -> if x = y then xs else x::(symins xs y)

let listSymdiff #a x y = FStar.List.Tot.fold_left symins [] x

let listDiff #a x y = FStar.List.Tot.filter (fun x -> not (FStar.List.Tot.mem x y)) x

(** Verification utilities *)
val mems_iff_mem : #a:eqtype -> l:list a ->
  Lemma (requires True)
        (ensures (forall i. Set.mem i (mems l) <==> FStar.List.Tot.mem i l))
let rec mems_iff_mem #a l = match l with
  | [] -> ()
  | x::xs -> mems_iff_mem xs

val mems_append : #a:eqtype -> l1:list a -> l2:list a ->
  Lemma (requires True)
        (ensures (Set.equal (mems (l1@l2)) (union (mems l1) (mems l2))))
let rec mems_append #a l1 l2 = match l1 with
  | [] -> ()
  | x::xs -> mems_append xs l2
