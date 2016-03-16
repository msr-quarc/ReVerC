#light "off"
module Partial
open Prims

type ('Aa, 'Ad, 'Ab) map =
'Aa  ->  'Ab


let update = (fun ( d  :  'Aa Util.set ) ( b  :  Prims.unit ) ( map  :  ('Aa, Prims.unit, obj) map ) ( x  :  'Aa ) ( y  :  obj ) ( z  :  'Aa ) -> if (z = x) then begin
y
end else begin
(map z)
end)


let lookup = (fun ( d  :  'Aa Util.set ) ( b  :  Prims.unit ) ( map  :  ('Aa, Prims.unit, obj) map ) ( x  :  'Aa ) -> (map x))


let dom = (fun ( d  :  'Aa Util.set ) ( b  :  Prims.unit ) ( m  :  ('Aa, Prims.unit, obj) map ) -> d)




