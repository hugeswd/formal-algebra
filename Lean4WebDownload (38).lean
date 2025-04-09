
 import Mathlib.Tactic.FieldSimp
 import Mathlib.Tactic.LinearCombination
 import Mathlib.RingTheory.Polynomial.Vieta
 
 namespace Polynomial
 
 variable {R T S : Type*}
 
 /--引理1. -/
 lemma eq_neg_mul_add_of_roots_quadratic_eq_pair [CommRing R] [IsDomain R] {a b c x1 x2 : R}
     (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
     b = -a * (x1 + x2) := by
   let p : R[X] := C a * X ^ 2 + C b * X + C c
   have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
     (by convert p.card_roots'; rw [hroots, Multiset.card_pair])
   have hp_roots_card : p.roots.card = p.natDegree := by
     rw [hp_natDegree, hroots, Multiset.card_pair]
   simpa [leadingCoeff, hp_natDegree, p, hroots, mul_assoc, add_comm x1] using
     coeff_eq_esymm_roots_of_card hp_roots_card (k := 1) (by norm_num [hp_natDegree])
 
 /-- 引理2 -/
 lemma eq_mul_mul_of_roots_quadratic_eq_pair [CommRing R] [IsDomain R] {a b c x1 x2 : R}
     (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
     c = a * x1 * x2 := by
   let p : R[X] := C a * X ^ 2 + C b * X + C c
   have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
     (by convert p.card_roots'; rw [hroots, Multiset.card_pair])
   have hp_roots_card : p.roots.card = p.natDegree := by
     rw [hp_natDegree, hroots, Multiset.card_pair]
   simpa [leadingCoeff, hp_natDegree, p, hroots, mul_assoc, add_comm x1] using
     coeff_eq_esymm_roots_of_card hp_roots_card (k := 0) (by norm_num [hp_natDegree])
 


 /-- 引理3 -/
 lemma roots_quadratic_eq_pair_iff_of_ne_zero [CommRing R] [IsDomain R] {a b c x1 x2 : R}
     (ha : a ≠ 0) : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
       b = -a * (x1 + x2) ∧ c = a * x1 * x2 :=
   have roots_of_ne_zero_of_vieta (hvieta : b = -a * (x1 + x2) ∧ c = a * x1 * x2) :
       (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} := by
     suffices C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) by
       have h1 : C a * (X - C x1) ≠ 0 := mul_ne_zero (by simpa) (Polynomial.X_sub_C_ne_zero _)
       have h2 : C a * (X - C x1) * (X - C x2) ≠ 0 := mul_ne_zero h1 (Polynomial.X_sub_C_ne_zero _)
       simp [this, Polynomial.roots_mul h2, Polynomial.roots_mul h1]
     simpa [hvieta.1, hvieta.2] using by ring
   ⟨fun h => ⟨eq_neg_mul_add_of_roots_quadratic_eq_pair h, eq_mul_mul_of_roots_quadratic_eq_pair h⟩,
     roots_of_ne_zero_of_vieta⟩
 

 /-- 主定理. -/
 theorem roots_quadratic_eq_pair_iff_of_ne_zero' [Field R] {a b c x1 x2 : R} (ha : a ≠ 0) :
     (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
       x1 + x2 = -b / a ∧ x1 * x2 = c / a := by
   rw [roots_quadratic_eq_pair_iff_of_ne_zero ha]
   field_simp
   exact and_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
     ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩



