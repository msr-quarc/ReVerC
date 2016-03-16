#light "off"
module FStar.Map
open Prims

type ('Akey, 'Avalue) t =
{mappings : 'Akey  ->  'Avalue; domain : 'Akey  ->  Prims.bool}


let is_Mkt = (Prims.checked_cast(fun ( _  :  ('Akey, 'Avalue) t ) -> (FStar.All.failwith "Not yet implemented:is_Mkt")))


let sel = (fun ( m  :  ('Akey, 'Avalue) t ) ( k  :  'Akey ) -> (m.mappings k))


let upd = (fun ( m  :  ('Akey, 'Avalue) t ) ( k  :  'Akey ) ( v  :  'Avalue ) -> {mappings = (fun ( x  :  'Akey ) -> if (x = k) then begin
v
end else begin
(m.mappings x)
end); domain = (fun ( x  :  'Akey ) -> ((x = k) || (m.domain x)))})


let const = (fun ( v  :  'Avalue ) -> {mappings = (fun ( _8_26  :  'Akey ) -> v); domain = (fun ( _8_28  :  'Akey ) -> true)})


let concat = (fun ( m1  :  ('Akey, 'Avalue) t ) ( m2  :  ('Akey, 'Avalue) t ) -> {mappings = (fun ( x  :  'Akey ) -> if (m2.domain x) then begin
(m2.mappings x)
end else begin
(m1.mappings x)
end); domain = (fun ( x  :  'Akey ) -> ((m1.domain x) || (m2.domain x)))})


let contains = (fun ( m  :  ('Akey, 'Avalue) t ) ( k  :  'Akey ) -> (m.domain k))


let restrict = (fun ( s  :  'Akey FStar.Set.set ) ( m  :  ('Akey, 'Avalue) t ) -> {mappings = m.mappings; domain = (fun ( x  :  'Akey ) -> ((FStar.Set.mem x s) && (contains m x)))})


let lemma_SelUpd1 = (fun ( m  :  ('Akey, 'Avalue) t ) ( k  :  'Akey ) ( v  :  'Avalue ) -> ())


let lemma_SelUpd2 = (fun ( m  :  ('Akey, 'Avalue) t ) ( k1  :  'Akey ) ( k2  :  'Akey ) ( v  :  'Avalue ) -> ())


let lemma_SelConst = (fun ( v  :  'Avalue ) ( k  :  'Akey ) -> ())


let lemma_SelRestrict = (fun ( m  :  ('Akey, 'Avalue) t ) ( ks  :  'Akey FStar.Set.set ) ( k  :  'Akey ) -> ())


let lemma_SelConcat1 = (fun ( m1  :  ('Akey, 'Avalue) t ) ( m2  :  ('Akey, 'Avalue) t ) ( k  :  'Akey ) -> ())


let lemma_SelConcat2 = (fun ( m1  :  ('Akey, 'Avalue) t ) ( m2  :  ('Akey, 'Avalue) t ) ( k  :  'Akey ) -> ())


let lemma_InDomUpd1 = (fun ( m  :  ('Akey, 'Avalue) t ) ( k1  :  'Akey ) ( k2  :  'Akey ) ( v  :  'Avalue ) -> ())


let lemma_InDomUpd2 = (fun ( m  :  ('Akey, 'Avalue) t ) ( k1  :  'Akey ) ( k2  :  'Akey ) ( v  :  'Avalue ) -> ())


let lemma_InDomConstMap = (fun ( v  :  'Avalue ) ( k  :  'Akey ) -> ())


let lemma_InDomConcat = (fun ( m1  :  ('Akey, 'Avalue) t ) ( m2  :  ('Akey, 'Avalue) t ) ( k  :  'Akey ) -> ())


let lemma_InDomRestrict = (fun ( m  :  ('Akey, 'Avalue) t ) ( ks  :  'Akey FStar.Set.set ) ( k  :  'Akey ) -> ())


let lemma_equal_intro = (fun ( m1  :  ('Akey, 'Avalue) t ) ( m2  :  ('Akey, 'Avalue) t ) -> ())


let lemma_equal_elim = (fun ( m1  :  ('Akey, 'Avalue) t ) ( m2  :  ('Akey, 'Avalue) t ) -> ())


let lemma_equal_refl = (fun ( m1  :  ('Akey, 'Avalue) t ) ( m2  :  ('Akey, 'Avalue) t ) -> ())


let const_on = (fun ( dom  :  'Akey FStar.Set.set ) ( v  :  'Avalue ) -> (restrict dom (const v)))




