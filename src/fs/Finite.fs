#light "off"
module Finite
open Prims

type ('An, 'Ab) map =
'Ab Prims.list


let rec lookup = (fun ( i  :  Prims.nat ) ( map  :  (Prims.unit, 'Ab) map ) -> if (i = 0) then begin
(match (map) with
| x::_12_98 -> begin
x
end)
end else begin
(match (map) with
| _12_103::xs -> begin
(lookup (i - 1) xs)
end)
end)


let rec update = (fun ( i  :  Prims.nat ) ( y  :  'Ab ) ( map  :  (Prims.unit, 'Ab) map ) -> if (i = 0) then begin
(match (map) with
| [] -> begin
(y)::[]
end
| x::xs -> begin
(y)::xs
end)
end else begin
(match (map) with
| x::xs -> begin
(x)::(update (i - 1) y xs)
end)
end)


let extend = (fun ( i  :  Prims.nat ) ( y  :  'Ab ) ( map  :  (Prims.unit, 'Ab) map ) -> (FStar.List.append map ((y)::[])))




