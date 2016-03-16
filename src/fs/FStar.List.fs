#light "off"
module FStar.List
open Prims

let isEmpty = (fun ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
true
end
| _9_18 -> begin
false
end))


let isEmptyT = isEmpty


let hd = (fun ( _9_1  :  'a Prims.list ) -> (match (_9_1) with
| hd::tl -> begin
hd
end
| _9_25 -> begin
(FStar.All.failwith "head of empty list")
end))


let tail = (fun ( _9_2  :  'A_9_1232 Prims.list ) -> (match (_9_2) with
| hd::tl -> begin
tl
end
| _9_31 -> begin
(FStar.All.failwith "tail of empty list")
end))


let tl = tail


let rec length = (fun ( _9_3  :  'a Prims.list ) -> (match (_9_3) with
| [] -> begin
(Prims.parse_int "0")
end
| _9_37::tl -> begin
((Prims.parse_int "1") + (length tl))
end))


let lengthT = length


let rec nth = (fun ( l  :  'a Prims.list ) ( n  :  Prims.int ) -> if (n < (Prims.parse_int "0")) then begin
(FStar.All.failwith "nth takes a non-negative integer as input")
end else begin
if (n = (Prims.parse_int "0")) then begin
(match (l) with
| [] -> begin
(FStar.All.failwith "not enough elements")
end
| hd::_9_44 -> begin
hd
end)
end else begin
(match (l) with
| [] -> begin
(FStar.All.failwith "not enough elements")
end
| _9_50::tl -> begin
(nth tl (n - (Prims.parse_int "1")))
end)
end
end)


let rec total_nth = (fun ( l  :  'a Prims.list ) ( n  :  Prims.nat ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
if (n = (Prims.parse_int "0")) then begin
Some (hd)
end else begin
(total_nth tl (n - (Prims.parse_int "1")))
end
end))


let rec count = (fun ( x  :  'a ) ( _9_4  :  'a Prims.list ) -> (match (_9_4) with
| [] -> begin
(Prims.parse_int "0")
end
| hd::tl -> begin
if (x = hd) then begin
((Prims.parse_int "1") + (count x tl))
end else begin
(count x tl)
end
end))


let countT = count


let rec rev_acc = (fun ( l  :  'a Prims.list ) ( acc  :  'a Prims.list ) -> (match (l) with
| [] -> begin
acc
end
| hd::tl -> begin
(rev_acc tl ((hd)::acc))
end))


let rev_append = rev_acc


let rev = (fun ( l  :  'a Prims.list ) -> (rev_acc l []))


let revT = rev


let rec append = (fun ( x  :  'a Prims.list ) ( y  :  'a Prims.list ) -> (match (x) with
| [] -> begin
y
end
| a::tl -> begin
(a)::(append tl y)
end))


let appendT = append


let rec flatten = (fun ( l  :  'a Prims.list Prims.list ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(append hd (flatten tl))
end))


let flattenT = flatten


let concat = flatten


let concatT = flattenT


let rec iter = (fun ( f  :  'a  ->  Prims.unit ) ( x  :  'a Prims.list ) -> (match (x) with
| [] -> begin
()
end
| a::tl -> begin
(

let _9_95 = (f a)
in (iter f tl))
end))


let rec iteri_aux = (fun ( i  :  Prims.int ) ( f  :  Prims.int  ->  'A_9_6759  ->  Prims.unit ) ( x  :  'A_9_6759 Prims.list ) -> (match (x) with
| [] -> begin
()
end
| a::tl -> begin
(

let _9_104 = (f i a)
in (iteri_aux (i + (Prims.parse_int "1")) f tl))
end))


let iteri = (fun ( f  :  Prims.int  ->  'a  ->  Prims.unit ) ( x  :  'a Prims.list ) -> (iteri_aux (Prims.parse_int "0") f x))


let rec iterT = (fun ( f  :  'a  ->  Prims.unit ) ( x  :  'a Prims.list ) -> ())


let rec map = (fun ( f  :  'a  ->  'b ) ( x  :  'a Prims.list ) -> (match (x) with
| [] -> begin
[]
end
| a::tl -> begin
((f a))::(map f tl)
end))


let rec mapT = (fun ( f  :  'a  ->  'b ) ( x  :  'a Prims.list ) -> (match (x) with
| [] -> begin
[]
end
| a::tl -> begin
((f a))::(mapT f tl)
end))


let rec mapi_init = (fun ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) ( i  :  Prims.int ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
((f i hd))::(mapi_init f tl (i + (Prims.parse_int "1")))
end))


let rec mapi_initT = (fun ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) ( i  :  Prims.int ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
((f i hd))::(mapi_initT f tl (i + (Prims.parse_int "1")))
end))


let mapi = (fun ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) -> (mapi_init f l (Prims.parse_int "0")))


let mapiT = (fun ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) -> (mapi_initT f l (Prims.parse_int "0")))


let rec concatMap = (fun ( f  :  'a  ->  'b Prims.list ) ( _9_5  :  'a Prims.list ) -> (match (_9_5) with
| [] -> begin
[]
end
| a::tl -> begin
(

let fa = (f a)
in (

let ftl = (concatMap f tl)
in (append fa ftl)))
end))


let rec concatMapT = (fun ( f  :  'a  ->  'b Prims.list ) ( _9_6  :  'a Prims.list ) -> (match (_9_6) with
| [] -> begin
[]
end
| a::tl -> begin
(

let fa = (f a)
in (

let ftl = (concatMapT f tl)
in (appendT fa ftl)))
end))


let rec map2 = (fun ( f  :  'a  ->  'b  ->  'c ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match ((l1, l2)) with
| ([], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2) -> begin
((f hd1 hd2))::(map2 f tl1 tl2)
end
| (_9_199, _9_201) -> begin
(FStar.All.failwith "The lists do not have the same length")
end))


let rec map3 = (fun ( f  :  'a  ->  'b  ->  'c  ->  'd ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) ( l3  :  'c Prims.list ) -> (match ((l1, l2, l3)) with
| ([], [], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2, hd3::tl3) -> begin
((f hd1 hd2 hd3))::(map3 f tl1 tl2 tl3)
end
| (_9_226, _9_228, _9_230) -> begin
(FStar.All.failwith "The lists do not have the same length")
end))


let rec fold_left = (fun ( f  :  'a  ->  'b  ->  'a ) ( x  :  'a ) ( y  :  'b Prims.list ) -> (match (y) with
| [] -> begin
x
end
| hd::tl -> begin
(fold_left f (f x hd) tl)
end))


let rec fold_leftT = (fun ( f  :  'a  ->  'b  ->  'a ) ( x  :  'a ) ( y  :  'b Prims.list ) -> (match (y) with
| [] -> begin
x
end
| hd::tl -> begin
(fold_leftT f (f x hd) tl)
end))


let rec fold_left2 = (fun ( f  :  's  ->  'a  ->  'b  ->  's ) ( a  :  's ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match ((l1, l2)) with
| ([], []) -> begin
a
end
| (hd1::tl1, hd2::tl2) -> begin
(fold_left2 f (f a hd1 hd2) tl1 tl2)
end
| (_9_269, _9_271) -> begin
(FStar.All.failwith "The lists do not have the same length")
end))


let rec fold_right = (fun ( f  :  'a  ->  'b  ->  'b ) ( l  :  'a Prims.list ) ( x  :  'b ) -> (match (l) with
| [] -> begin
x
end
| hd::tl -> begin
(f hd (fold_right f tl x))
end))


let rec fold_rightT = (fun ( f  :  'a  ->  'b  ->  'b ) ( l  :  'a Prims.list ) ( x  :  'b ) -> (match (l) with
| [] -> begin
x
end
| hd::tl -> begin
(f hd (fold_rightT f tl x))
end))


let rec mem = (fun ( x  :  'a ) ( _9_7  :  'a Prims.list ) -> (match (_9_7) with
| [] -> begin
false
end
| hd::tl -> begin
if (hd = x) then begin
true
end else begin
(mem x tl)
end
end))


let memT = mem


let contains = mem


let containsT = memT


let rec existsb = (fun ( f  :  'Aa  ->  Prims.bool ) ( l  :  'Aa Prims.list ) -> (match (l) with
| [] -> begin
false
end
| hd::tl -> begin
if (f hd) then begin
true
end else begin
(existsb f tl)
end
end))


let rec find = (fun ( f  :  'Aa  ->  Prims.bool ) ( l  :  'Aa Prims.list ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
if (f hd) then begin
Some (hd)
end else begin
(find f tl)
end
end))


let findT = find


let rec filter = (fun ( f  :  'a  ->  Prims.bool ) ( _9_8  :  'a Prims.list ) -> (match (_9_8) with
| [] -> begin
[]
end
| hd::tl -> begin
if (f hd) then begin
(hd)::(filter f tl)
end else begin
(filter f tl)
end
end))


let rec filterT = (fun ( f  :  'a  ->  Prims.bool ) ( _9_9  :  'a Prims.list ) -> (match (_9_9) with
| [] -> begin
[]
end
| hd::tl -> begin
if (f hd) then begin
(hd)::(filterT f tl)
end else begin
(filterT f tl)
end
end))


let rec for_all = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
true
end
| hd::tl -> begin
if (f hd) then begin
(for_all f tl)
end else begin
false
end
end))


let rec for_allT = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
true
end
| hd::tl -> begin
if (f hd) then begin
(for_allT f tl)
end else begin
false
end
end))


let rec forall2 = (fun ( f  :  'a  ->  'b  ->  Prims.bool ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match ((l1, l2)) with
| ([], []) -> begin
true
end
| (hd1::tl1, hd2::tl2) -> begin
if (f hd1 hd2) then begin
(forall2 f tl1 tl2)
end else begin
false
end
end
| (_9_366, _9_368) -> begin
(FStar.All.failwith "The lists do not have the same length")
end))


let rec collect = (fun ( f  :  'a  ->  'b Prims.list ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(append (f hd) (collect f tl))
end))


let rec collectT = (fun ( f  :  'a  ->  'b Prims.list ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(appendT (f hd) (collectT f tl))
end))


let rec tryFind = (fun ( p  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
if (p hd) then begin
Some (hd)
end else begin
(tryFind p tl)
end
end))


let rec tryFindT = (fun ( p  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
if (p hd) then begin
Some (hd)
end else begin
(tryFindT p tl)
end
end))


let rec tryPick = (fun ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
Some (x)
end
| None -> begin
(tryPick f tl)
end)
end))


let rec tryPickT = (fun ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
Some (x)
end
| None -> begin
(tryPickT f tl)
end)
end))


let rec choose = (fun ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
(x)::(choose f tl)
end
| None -> begin
(choose f tl)
end)
end))


let rec chooseT = (fun ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
(x)::(chooseT f tl)
end
| None -> begin
(chooseT f tl)
end)
end))


let rec partition = (fun ( f  :  'a  ->  Prims.bool ) ( _9_10  :  'a Prims.list ) -> (match (_9_10) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(

let _9_453 = (partition f tl)
in (match (_9_453) with
| (l1, l2) -> begin
if (f hd) then begin
((hd)::l1, l2)
end else begin
(l1, (hd)::l2)
end
end))
end))


let rec partitionT = (fun ( f  :  'a  ->  Prims.bool ) ( _9_11  :  'a Prims.list ) -> (match (_9_11) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(

let _9_464 = (partitionT f tl)
in (match (_9_464) with
| (l1, l2) -> begin
if (f hd) then begin
((hd)::l1, l2)
end else begin
(l1, (hd)::l2)
end
end))
end))


let rec assoc = (fun ( a  :  'a ) ( x  :  ('a * 'b) Prims.list ) -> (match (x) with
| [] -> begin
None
end
| (a', b)::tl -> begin
if (a = a') then begin
Some (b)
end else begin
(assoc a tl)
end
end))


let assocT = assoc


let rec split = (fun ( l  :  ('a * 'b) Prims.list ) -> (match (l) with
| [] -> begin
([], [])
end
| (hd1, hd2)::tl -> begin
(

let _9_486 = (split tl)
in (match (_9_486) with
| (tl1, tl2) -> begin
((hd1)::tl1, (hd2)::tl2)
end))
end))


let splitT = split


let unzip = split


let unzipT = splitT


let rec unzip3 = (fun ( l  :  ('a * 'b * 'c) Prims.list ) -> (match (l) with
| [] -> begin
([], [], [])
end
| (hd1, hd2, hd3)::tl -> begin
(

let _9_501 = (unzip3 tl)
in (match (_9_501) with
| (tl1, tl2, tl3) -> begin
((hd1)::tl1, (hd2)::tl2, (hd3)::tl3)
end))
end))


let unzip3T = unzip3


let rec zip = (fun ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match ((l1, l2)) with
| ([], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2) -> begin
((hd1, hd2))::(zip tl1 tl2)
end
| (_9_517, _9_519) -> begin
(FStar.All.failwith "The lists do not have the same length")
end))


let rec zip3 = (fun ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) ( l3  :  'c Prims.list ) -> (match ((l1, l2, l3)) with
| ([], [], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2, hd3::tl3) -> begin
((hd1, hd2, hd3))::(zip3 tl1 tl2 tl3)
end
| (_9_542, _9_544, _9_546) -> begin
(FStar.All.failwith "The lists do not have the same length")
end))


let rec sortWith = (fun ( f  :  'a  ->  'a  ->  Prims.int ) ( _9_12  :  'a Prims.list ) -> (match (_9_12) with
| [] -> begin
[]
end
| pivot::tl -> begin
(

let _9_558 = (partition (fun ( x  :  'a ) -> ((f pivot x) > (Prims.parse_int "0"))) tl)
in (match (_9_558) with
| (hi, lo) -> begin
(append (sortWith f lo) ((pivot)::(sortWith f hi)))
end))
end))


let rec partition_length = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> ())


let bool_of_compare = (fun ( f  :  'a  ->  'a  ->  Prims.int ) ( x  :  'a ) ( y  :  'a ) -> ((f x y) >= (Prims.parse_int "0")))


let rec sortWithT = (fun ( f  :  'a  ->  'a  ->  Prims.int ) ( _9_13  :  'a Prims.list ) -> (match (_9_13) with
| [] -> begin
[]
end
| pivot::tl -> begin
(

let _9_582 = (partitionT (bool_of_compare f pivot) tl)
in (match (_9_582) with
| (hi, lo) -> begin
(

let _9_583 = ()
in (append (sortWithT f lo) ((pivot)::(sortWithT f hi))))
end))
end))




