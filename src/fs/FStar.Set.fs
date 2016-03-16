#light "off"
module FStar.Set
open Prims

type 'Aa set =
'Aa  ->  Prims.bool


let mem = (fun ( x  :  'Aa ) ( s  :  'Aa set ) -> (s x))


let empty = (fun ( _2_10  :  'Aa ) -> false)


let singleton = (fun ( x  :  'Aa ) ( y  :  'Aa ) -> (y = x))


let union = (fun ( s1  :  'Aa set ) ( s2  :  'Aa set ) ( x  :  'Aa ) -> ((s1 x) || (s2 x)))


let intersect = (fun ( s1  :  'Aa set ) ( s2  :  'Aa set ) ( x  :  'Aa ) -> ((s1 x) && (s2 x)))


let complement = (fun ( s  :  'Aa set ) ( x  :  'Aa ) -> (not ((s x))))


let subset = (fun ( s1  :  'Aa set ) ( s2  :  'Aa set ) -> ((intersect s1 s2) = s1))


let mem_empty = (fun ( x  :  'Aa ) -> ())


let mem_singleton = (fun ( x  :  'Aa ) ( y  :  'Aa ) -> ())


let mem_union = (fun ( x  :  'Aa ) ( s1  :  'Aa set ) ( s2  :  'Aa set ) -> ())


let mem_intersect = (fun ( x  :  'Aa ) ( s1  :  'Aa set ) ( s2  :  'Aa set ) -> ())


let mem_complement = (fun ( x  :  'Aa ) ( s  :  'Aa set ) -> ())


type ('Aa, 'As1, 'As2) l__Equal =
('Aa, Prims.bool, Prims.unit, Prims.unit) FStar.FunctionalExtensionality.l__FEq


let lemma_equal_intro = (fun ( s1  :  'Aa set ) ( s2  :  'Aa set ) -> ())


let lemma_equal_elim = (fun ( s1  :  'Aa set ) ( s2  :  'Aa set ) -> ())


let lemma_equal_refl = (fun ( s1  :  'Aa set ) ( s2  :  'Aa set ) -> ())


let mem_subset = (fun ( s1  :  'Aa set ) ( s2  :  'Aa set ) -> ())


let subset_mem = (fun ( s1  :  'Aa set ) ( s2  :  'Aa set ) -> ())




