import Pilz.F9Combinatorics
import Pilz.SmallCases
import Pilz.Slices

/-! The exceptional core bound `distance f₉ ≥ 5` by the paper's parametrization. -/

noncomputable section

namespace Pilz.F9Param

open MvPolynomial
open scoped BigOperators

def values (p : ℕ) : R := if p = 2 then U else if p = 3 then V else 1
def param : Poly →+* R := MvPolynomial.eval₂Hom Polynomial.C values

@[simp] theorem param_X_two : param (MvPolynomial.X 2) = U := by simp [param, values]
@[simp] theorem param_X_three : param (MvPolynomial.X 3) = V := by simp [param, values]

theorem values_ne_zero (p : ℕ) : values p ≠ 0 := by
  unfold values
  split_ifs <;> first | exact U_ne_zero | exact V_ne_zero | exact one_ne_zero

theorem param_monomial_ne_zero (d : ℕ →₀ ℕ) :
    param (MvPolynomial.monomial d 1) ≠ 0 := by
  rw [param, MvPolynomial.eval₂Hom_monomial, map_one, one_mul]
  apply Finsupp.prod_ne_zero_iff.mpr
  intro p _
  exact pow_ne_zero _ (values_ne_zero p)

theorem param_f9 : param SmallCore.f9 = 0 := by
  simp only [SmallCore.f9, SmallCore.f9At, SmallCore.cAt, Finset.sum_range_succ,
    Finset.sum_empty, zero_add, map_add, map_mul, map_pow, map_one,
    param_X_two, param_X_three]
  unfold U V
  ring_nf
  have h4 : (4 : R) = 0 := (CharP.cast_eq_zero_iff R 2 4).mpr (by decide)
  have h6 : (6 : R) = 0 := (CharP.cast_eq_zero_iff R 2 6).mpr (by decide)
  have h10 : (10 : R) = 0 := (CharP.cast_eq_zero_iff R 2 10).mpr (by decide)
  have h12 : (12 : R) = 0 := (CharP.cast_eq_zero_iff R 2 12).mpr (by decide)
  simp [h4, h6, h10, h12, CharTwo.two_eq_zero]

def pairOf (d : ℕ →₀ ℕ) : ℕ × ℕ := (d 2, d 3)

theorem exponent_eq_of_vars (P : Poly) (hvars : P.vars ⊆ ({2, 3} : Finset ℕ))
    {d : ℕ →₀ ℕ} (hd : d ∈ P.support) :
    d = Finsupp.single 2 (d 2) + Finsupp.single 3 (d 3) := by
  ext p
  by_cases h2 : p = 2
  · subst p; simp [Finsupp.add_apply]
  by_cases h3 : p = 3
  · subst p; simp [Finsupp.add_apply]
  have hz : d p = 0 := MvPolynomial.mem_support_notMem_vars_zero hd (by
    intro hp
    have := hvars hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact this.elim h2 h3)
  simp [Finsupp.add_apply, Finsupp.single_apply, h2, h3, hz]

theorem pairOf_injOn (P : Poly) (hvars : P.vars ⊆ ({2, 3} : Finset ℕ)) :
    Set.InjOn pairOf (P.support : Set (ℕ →₀ ℕ)) := by
  intro d hd e he hde
  have h2 : d 2 = e 2 := congrArg Prod.fst hde
  have h3 : d 3 = e 3 := congrArg Prod.snd hde
  rw [exponent_eq_of_vars P hvars hd, exponent_eq_of_vars P hvars he, h2, h3]

theorem param_eq_sum (P : Poly) (hvars : P.vars ⊆ ({2, 3} : Finset ℕ)) :
    param P = ∑ t ∈ P.support.image pairOf, term t := by
  classical
  rw [Finset.sum_image (pairOf_injOn P hvars)]
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hc : MvPolynomial.coeff d P = 1 := by
    have hne := MvPolynomial.mem_support_iff.mp hd
    generalize hv : MvPolynomial.coeff d P = v at *
    fin_cases v <;> simp_all
  have hm : MvPolynomial.monomial d (1 : ZMod 2) =
      (MvPolynomial.X 2 : Poly) ^ d 2 * MvPolynomial.X 3 ^ d 3 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul, one_mul, ← exponent_eq_of_vars P hvars hd]
  rw [hc, hm, map_mul, map_pow, map_pow, param_X_two, param_X_three]
  rfl

/-- A normalized polynomial in the two base variables with at most four
terms cannot vanish under the parametrization. -/
theorem param_ne_zero_of_four (P : Poly) (hvars : P.vars ⊆ ({2, 3} : Finset ℕ))
    (hcard : weight P ≤ 4) (hfree : ∃ d ∈ P.support, d 3 = 0) : param P ≠ 0 := by
  rw [param_eq_sum P hvars]
  apply sum_terms_ne_zero_of_card_le_four
  · exact (Finset.card_image_le).trans hcard
  · obtain ⟨d, hd, h3⟩ := hfree
    exact ⟨pairOf d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, h3⟩

theorem f9_vars : SmallCore.f9.vars ⊆ ({2, 3} : Finset ℕ) := by
  intro p hp
  obtain ⟨d, hd, hdp⟩ := (MvPolynomial.mem_vars p).mp hp
  rw [SmallCore.f9_terms] at hd
  obtain ⟨t, ht, hdt⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  have hsup : (SmallCore.coreTerm t).support = {SmallCore.coreExponent t.1 t.2.1 t.2.2} := by
    simp [SmallCore.coreTerm, MvPolynomial.support_monomial]
  rw [hsup, Finset.mem_singleton] at hdt
  subst d
  simp only [SmallCore.terms9, Finset.mem_insert, Finset.mem_singleton] at ht
  by_contra hn
  have h2 : 2 ≠ p := fun hh => hn (by simp [hh])
  have h3 : 3 ≠ p := fun hh => hn (by simp [hh])
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa [SmallCore.coreExponent, Finsupp.mem_support_iff,
      Finsupp.add_apply, Finsupp.single_apply, h2, h3] using hdp

/-- The special core bound in Lemma `lem:cores`. -/
theorem f9_distance_lower_five : 5 ≤ distance SmallCore.f9 := by
  apply (le_distance_iff _ _).mpr
  intro H hH
  by_contra hnot
  have hshort : weight (SmallCore.f9 * H) ≤ 4 := by
    change ¬5 ≤ weight (SmallCore.f9 * H) at hnot
    omega
  obtain ⟨E, hE, hEvars, hprod⟩ := exists_base_multiplier ({2, 3} : Finset ℕ)
    SmallCore.f9 H f9_vars hH
  let G := SmallCore.f9 * E
  have hf9 : SmallCore.f9 ≠ 0 := by
    intro hz
    have hh := SmallCore.constantCoeff_f9
    rw [hz, map_zero] at hh
    exact zero_ne_one hh
  have hG : G ≠ 0 := mul_ne_zero hf9 hE
  have hGvars : G.vars ⊆ ({2, 3} : Finset ℕ) :=
    (MvPolynomial.vars_mul SmallCore.f9 E).trans (Finset.union_subset f9_vars hEvars)
  have hGcard : weight G ≤ 4 := hprod.trans hshort
  have hGzero : param G = 0 := by simp [G, map_mul, param_f9]
  obtain ⟨e, D, hfactor, hD, hnorm, hweight, _, hocc⟩ := exists_normalization G hG
  have hDvars : D.vars ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    obtain ⟨d, hd, hdp⟩ := (MvPolynomial.mem_vars p).mp hp
    obtain ⟨b, hb, hbp⟩ := hocc p ⟨d, hd, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hdp)⟩
    exact hGvars ((MvPolynomial.mem_vars p).mpr
      ⟨b, hb, Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hbp)⟩)
  have hDzero : param D = 0 := by
    rw [hfactor, map_mul] at hGzero
    exact (mul_eq_zero.mp hGzero).resolve_left (param_monomial_ne_zero e)
  exact param_ne_zero_of_four D hDvars (hweight.trans_le hGcard) (hnorm 3) hDzero

end Pilz.F9Param
