#light "off"
module Par
open Prims

type ('Akey, 'Avalue) map =
('Akey * 'Avalue) Prims.list


let rec dom = (fun ( mp  :  ('k, 'v) map ) -> (match (mp) with
| [] -> begin
(fun ( _17_7  :  'k ) -> false)
end
| x::xs -> begin
(fun ( y  :  'k ) -> (((Prims.fst x) = y) || (dom xs y)))
end))


let rec cod = (fun ( mp  :  ('k, 'v) map ) -> (match (mp) with
| [] -> begin
(fun ( _17_17  :  'v ) -> false)
end
| x::xs -> begin
(fun ( y  :  'v ) -> (((Prims.snd x) = y) || (cod xs y)))
end))


let defined = (fun ( m  :  ('k, 'v) map ) ( k  :  'k ) -> (Util.mem k (dom m)))


let empty = []


let rec find = (fun ( lst  :  ('k, 'v) map ) ( v  :  'k ) -> (match (lst) with
| [] -> begin
None
end
| (x, y)::xs -> begin
if (x = v) then begin
Some (y)
end else begin
(find xs v)
end
end))


let rec lookup = (fun ( lst  :  ('k, 'v) map ) ( v  :  'k ) -> (match (lst) with
| (x, y)::xs -> begin
if (x = v) then begin
y
end else begin
(lookup xs v)
end
end))


let rec lookupT = (fun ( lst  :  ('k, 'v) map ) ( v  :  'k ) ( def  :  'v ) -> (match (lst) with
| [] -> begin
def
end
| (x, y)::xs -> begin
if (x = v) then begin
y
end else begin
(lookupT xs v def)
end
end))


let rec update = (fun ( lst  :  ('k, 'v) map ) ( k  :  'k ) ( v  :  'v ) -> (match (lst) with
| [] -> begin
((k, v))::[]
end
| (x, y)::xs -> begin
if (x = k) then begin
((x, v))::xs
end else begin
((x, y))::(update xs k v)
end
end))


let totalize = (fun ( mp  :  ('Aa, 'Ab) map ) ( def  :  'Ab ) ( k  :  'Aa ) -> (match ((find mp k)) with
| None -> begin
def
end
| Some (b) -> begin
b
end))




