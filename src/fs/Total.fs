#light "off"
module Total
open Prims

type ('Aa, 'Ab) map =
'Aa  ->  'Ab


let lemma_map_equal_intro = (fun ( m1  :  ('Aa, 'Ab) map ) ( m2  :  ('Aa, 'Ab) map ) -> ())


let lemma_map_equal_elim = (fun ( m1  :  ('Aa, 'Ab) map ) ( m2  :  ('Aa, 'Ab) map ) -> ())


let lemma_map_equal_refl = (fun ( m1  :  ('Aa, 'Ab) map ) ( m2  :  ('Aa, 'Ab) map ) -> ())


let lookup = (fun ( map  :  ('Aa, 'Ab) map ) ( x  :  'Aa ) -> (map x))


let update = (fun ( map  :  ('Aa, 'Ab) map ) ( x  :  'Aa ) ( y  :  'Ab ) ( z  :  'Aa ) -> if (z = x) then begin
y
end else begin
(map z)
end)


let compose = (fun ( m  :  ('Aa, 'Ab) map ) ( m'  :  ('Ab, 'Ac) map ) ( i  :  'Aa ) -> (m' (m i)))


let const_map = (fun ( v  :  'Ab ) ( _10_45  :  'Aa ) -> v)


type state =
(Prims.int, Prims.bool) map


let agree_on_trans = (fun ( mp  :  ('Aa, 'Ab) map ) ( mp'  :  ('Aa, 'Ab) map ) ( mp''  :  ('Aa, 'Ab) map ) ( s  :  'Aa Util.set ) -> ())


let map_mp = (fun ( f  :  'Ab  ->  'Ab ) ( m  :  ('Aa, 'Ab) map ) -> m)




