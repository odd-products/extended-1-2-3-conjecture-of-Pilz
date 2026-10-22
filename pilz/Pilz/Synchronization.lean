import Pilz.Extremal
import Pilz.FreshDerivatives

/-!
# Synchronizing the fresh derivatives

This file implements the first two steps of Proposition `prop:normal-form`:
fresh-variable multiplication makes every odd-term count at most half the
weight, and one strict inequality forces all fresh derivatives to agree.
-/

noncomputable section

namespace Pilz

open MvPolynomial

/-- Step 1: multiplying by selected variables makes their odd-term counts
at most half the weight. Counts in all other variables are preserved. -/
theorem exists_oddCount_bounded_extremal (F : Poly) (B T : Finset ℕ) (N : ℕ)
    (G : Poly) (hG : Extremal F B N G) :
    ∃ Q : Poly, Extremal F B N Q ∧ weight Q = weight G ∧
      (∀ i ∈ T, 2 * oddCount Q i ≤ weight Q) ∧
      (∀ i ∉ T, oddCount Q i = oddCount G i) := by
  classical
  induction T using Finset.induction_on generalizing G with
  | empty => exact ⟨G, hG, rfl, by simp, by simp⟩
  | @insert i T hi ih =>
    obtain ⟨Q, hQ, hweight, hcounts, houtside⟩ := ih G hG
    by_cases hbound : 2 * oddCount Q i ≤ weight Q
    · refine ⟨Q, hQ, hweight, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hji | hjT
        · subst j
          exact hbound
        · exact hcounts j hjT
      · intro j hj
        exact houtside j (fun h => hj (Finset.mem_insert_of_mem h))
    · have hxext : Extremal F B N (X i * Q) :=
        extremal_monomial_mul F B N Q hQ (Finsupp.single i 1)
      have hxweight : weight (X i * Q) = weight Q :=
        weight_monomial_mul (Finsupp.single i 1) Q
      refine ⟨X i * Q, hxext, hxweight.trans hweight, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hji | hjT
        · subst j
          have hc := oddCount_X_mul_self Q i
          rw [hxweight]
          omega
        · have hji : j ≠ i := fun h => hi (h ▸ hjT)
          rw [oddCount_X_mul_of_ne Q i j hji, hxweight]
          exact hcounts j hjT
      · intro j hj
        have hji : j ≠ i := fun h => hj (Finset.mem_insert.mpr (Or.inl h))
        rw [oddCount_X_mul_of_ne Q i j hji]
        exact houtside j (fun h => hj (Finset.mem_insert_of_mem h))

/-- The base widths of a pair derivative cannot increase when both
differentiated variables lie outside the base set. -/
theorem pair_pderiv_width_le (B : Finset ℕ) (G : Poly) (i j : ℕ)
    (hi : i ∉ B) (hj : j ∉ B)
    (hQ : pderiv i G + pderiv j G ≠ 0) :
    ∀ p ∈ B, widthOf p (pderiv i G + pderiv j G) ≤ widthOf p G := by
  intro p hp
  have hpi : p ≠ i := by rintro rfl; exact hi hp
  have hpj : p ≠ j := by rintro rfl; exact hj hp
  apply widthOf_mono_exponents p hQ
  intro d hd
  obtain ⟨e, he, hcoord⟩ := pair_pderiv_base_exponent hd hpi hpj
  exact ⟨e, he, hcoord.symm⟩

/-- An extremal multiple has no nonzero pair derivative whose odd-row
budget is strictly less than its weight. -/
theorem extremal_pair_pderiv_eq_zero (S : FreshData) (B : Finset ℕ)
    (N : ℕ) (G : Poly) (hG : Extremal S.F B N G) {i j : ℕ}
    (hi : i ∈ S.vars) (hj : j ∈ S.vars)
    (hBi : i ∉ B) (hBj : j ∉ B)
    (hbudget : oddCount G i + oddCount G j < weight G) :
    pderiv i G + pderiv j G = 0 := by
  apply extremal_eq_zero_of_weight_lt S.F B N G _ hG
  · exact S.dvd_pair_pderiv hi hj hG.1.2.1
  · exact (weight_pair_pderiv_le G i j).trans_lt hbudget
  · intro hQ
    exact pair_pderiv_width_le B G i j hBi hBj hQ

/-- Step 2: a single row below half the weight synchronizes every fresh row. -/
theorem derivatives_eq_of_strict_oddCount (S : FreshData) (B : Finset ℕ)
    (N : ℕ) (G : Poly) (hG : Extremal S.F B N G)
    (hdisjoint : Disjoint B S.vars) {i : ℕ} (hi : i ∈ S.vars)
    (hstrict : 2 * oddCount G i < weight G)
    (hcounts : ∀ j ∈ S.vars, 2 * oddCount G j ≤ weight G) :
    ∀ j ∈ S.vars, pderiv j G = pderiv i G := by
  intro j hj
  have hBi : i ∉ B := fun h => Finset.disjoint_left.mp hdisjoint h hi
  have hBj : j ∉ B := fun h => Finset.disjoint_left.mp hdisjoint h hj
  have hbudget : oddCount G i + oddCount G j < weight G := by
    have hjcount := hcounts j hj
    omega
  have hz := extremal_pair_pderiv_eq_zero S B N G hG hi hj hBi hBj hbudget
  exact ((eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq _)).symm

/-- The one-fresh-variable case is already synchronized, without any strict
count assumption. -/
theorem derivatives_eq_of_singleton (S : FreshData) {i : ℕ}
    (hvars : S.vars = {i}) (G : Poly) :
    ∀ j ∈ S.vars, pderiv j G = pderiv i G := by
  intro j hj
  have hji : j = i := Finset.mem_singleton.mp (hvars ▸ hj)
  subst j
  rfl

end Pilz
