import Pilz.Compatibility
import Pilz.Slices

/-! Summing the compatibility budget over independent-variable slices. -/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

theorem outsideSlice_ne_zero_iff (S : Finset ℕ) (β : ℕ →₀ ℕ) (P : Poly) :
    outsideSlice S β P ≠ 0 ↔ β ∈ P.support.image (outsideExponent S) := by
  classical
  constructor
  · intro h
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr h
    rw [support_outsideSlice] at hd
    obtain ⟨hd, heq⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_image.mpr ⟨d, hd, heq⟩
  · intro h
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp h
    have hmem : d ∈ (outsideSlice S β P).support := by
      rw [support_outsideSlice]
      exact Finset.mem_filter.mpr ⟨hd, heq⟩
    exact MvPolynomial.support_nonempty.mp ⟨d, hmem⟩

theorem outsideFibers_mul (S : Finset ℕ) (P H : Poly) (hP : P ≠ 0) (hvars : P.vars ⊆ S) :
    (P * H).support.image (outsideExponent S) = H.support.image (outsideExponent S) := by
  classical
  ext β
  rw [← outsideSlice_ne_zero_iff, ← outsideSlice_ne_zero_iff, outsideSlice_mul S β P H hvars]
  constructor
  · intro h
    exact (mul_ne_zero_iff.mp h).2
  · intro h
    exact mul_ne_zero hP h

theorem weight_mul_eq_sum_outsideFibers (S : Finset ℕ) (P H : Poly)
    (hP : P ≠ 0) (hvars : P.vars ⊆ S) :
    weight (P * H) = ∑ β ∈ H.support.image (outsideExponent S),
      weight (P * outsideSlice S β H) := by
  rw [weight_eq_sum_outsideSlice S (P * H), outsideFibers_mul S P H hP hvars]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [outsideSlice_mul S β P H hvars]

private theorem interval_two_vars_pair : (interval 2).vars ⊆ ({2, 3} : Finset ℕ) := by
  rw [interval_two]
  exact (MvPolynomial.vars_add_subset _ _).trans (by simp)

private theorem interval_three_vars_pair : (interval 3).vars ⊆ ({2, 3} : Finset ℕ) := by
  rw [interval_three]
  apply (MvPolynomial.vars_add_subset _ _).trans
  apply Finset.union_subset
  · exact (MvPolynomial.vars_add_subset _ _).trans (by simp)
  · simp

/-- For a normalized four-term multiplier involving `x₅`, the compatibility
budgets sum to twelve across its nonempty outside-variable fibers. -/
theorem four_term_interval_compatibility (D : Poly) (hfour : weight D = 4)
    (hnorm : Normalized D) (hocc : VariableOccurs D 5) :
    12 ≤ weight (interval 2 * D) + weight (interval 3 * D) := by
  classical
  let S : Finset ℕ := {2, 3}
  let T := D.support.image (outsideExponent S)
  have hTtwo : 2 ≤ T.card := by
    obtain ⟨d, hd, hd0⟩ := hnorm 5
    obtain ⟨e, he, hepos⟩ := hocc
    have hne : outsideExponent S d ≠ outsideExponent S e := by
      intro heq
      have hh := congrArg (fun a : ℕ →₀ ℕ => a 5) heq
      simp [outsideExponent_apply, S] at hh
      omega
    have hdT : outsideExponent S d ∈ T := Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have heT : outsideExponent S e ∈ T := Finset.mem_image.mpr ⟨e, he, rfl⟩
    exact Nat.succ_le_iff.mpr (Finset.one_lt_card.mpr
      ⟨outsideExponent S d, hdT, outsideExponent S e, heT, hne⟩)
  have hsum : weight D = ∑ β ∈ T, weight (outsideSlice S β D) :=
    weight_eq_sum_outsideSlice S D
  have hne : ∀ β ∈ T, outsideSlice S β D ≠ 0 := by
    intro β hβ
    exact (outsideSlice_ne_zero_iff S β D).mpr hβ
  have hfew : ∀ β ∈ T, weight (outsideSlice S β D) ≤ 3 := by
    intro β hβ
    obtain ⟨γ, hγ, hγβ⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) β
    have hsub : ({β, γ} : Finset (ℕ →₀ ℕ)) ⊆ T := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hβ
      · exact hγ
    have hpair : (∑ a ∈ ({β, γ} : Finset (ℕ →₀ ℕ)), weight (outsideSlice S a D)) ≤
        ∑ a ∈ T, weight (outsideSlice S a D) := Finset.sum_le_sum_of_subset hsub
    simp only [Finset.sum_pair hγβ.symm] at hpair
    have hpos := weight_pos (hne γ hγ)
    rw [← hsum, hfour] at hpair
    omega
  have hcompat := Finset.sum_le_sum (s := T) (fun β hβ =>
    small_interval_compatibility (outsideSlice S β D) (hne β hβ) (hfew β hβ))
  have htwo := weight_mul_eq_sum_outsideFibers S (interval 2) D
    (interval_ne_zero (by decide)) interval_two_vars_pair
  have hthree := weight_mul_eq_sum_outsideFibers S (interval 3) D
    (interval_ne_zero (by decide)) interval_three_vars_pair
  change weight (interval 2 * D) = ∑ β ∈ T, weight (interval 2 * outsideSlice S β D) at htwo
  change weight (interval 3 * D) = ∑ β ∈ T, weight (interval 3 * outsideSlice S β D) at hthree
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at hcompat
  rw [← hsum, hfour, ← htwo, ← hthree] at hcompat
  omega

end Pilz
