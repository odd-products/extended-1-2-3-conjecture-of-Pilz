import WeightedPilz.PositiveAffineReduction
import WeightedPilz.IntegerResidues
import WeightedPilz.Arithmetic.LargeResidueBudgets
import WeightedPilz.LargeAffineFinite

/-! Assembly of the arbitrary-characteristic large interval argument. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]

theorem intervalCore_large_residue_capacity (n p j : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n) (hj : 0 < j) (hjp : j < p) :
    residueSigma p (intervalCore n c ^ j) ≤
      (Pilz.freshCount n + j - 1).choose j := by
  exact residueSigma_intervalCore_pow_le n p j _ c hc (by omega)
    (Arithmetic.large_residue_budget hn hj hjp)

/-- All characteristics reduce to the explicit affine estimate after the
integer residue capacities have been discharged. -/
theorem intervalBound_large_of_affine (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n)
    (haffine : ∀ D B : Poly K,
      (∀ p ∈ intervalFreshPrimes n, ∀ d ∈ D.support, d p = 0) →
      (∀ p ∈ intervalFreshPrimes n, ∀ d ∈ B.support, d p = 0) →
      (D ≠ 0 ∨ B ≠ 0) → (2 : K) ≠ 0 →
      n ≤ weight ((intervalCore n c + ∑ p ∈ intervalFreshPrimes n, X p) *
        (D + (∑ p ∈ intervalFreshPrimes n, X p) * B))) :
    IntervalBound n c := by
  have hnpos : 0 < n := by omega
  have hr : (intervalFreshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    rw [Pilz.card_freshPrimes]
    have h := Arithmetic.fresh_count_eight n hn
    omega
  let S := intervalFreshData n c hnpos hc hr
  have hdegree : ∀ j, 3 ≤ j → n ≤ (S.vars.card + j - 1).choose j := by
    intro j hj
    change n ≤ ((intervalFreshPrimes n).card + j - 1).choose j
    rw [Pilz.card_freshPrimes]
    exact (Arithmetic.large_degree_cost hn hj).le
  have hcapacity : ∀ p j, 0 < j → j < p → residueSigma p (S.C ^ j) ≤
      (S.vars.card + j - 1).choose j := by
    intro p j hj hjp
    change residueSigma p (intervalCore n c ^ j) ≤
      ((intervalFreshPrimes n).card + j - 1).choose j
    rw [Pilz.card_freshPrimes]
    exact intervalCore_large_residue_capacity n p j c hc hn hj hjp
  have hnoaffine (h2 : (2 : K) ≠ 0) :
      ¬ ∃ D B : Poly K, S.BaseOnly D ∧ S.BaseOnly B ∧
        D + S.freshSum * B ≠ 0 ∧ weight (S.F * (D + S.freshSum * B)) < n := by
    rintro ⟨D, B, hDb, hBb, hne, hshort⟩
    have hne' : D ≠ 0 ∨ B ≠ 0 := by
      by_contra h
      push_neg at h
      apply hne
      simp [h.1, h.2]
    have hlo := haffine D B hDb hBb hne' h2
    exact Nat.not_lt_of_ge hlo hshort
  have hdist : n ≤ distance S.F := by
    by_contra hnot
    obtain ⟨H, hH, hmin⟩ := exists_weight_eq_distance S.F
    have hcounter : ∃ H : Poly K, H ≠ 0 ∧ weight (S.F * H) < n :=
      ⟨H, hH, by rw [hmin]; omega⟩
    obtain ⟨p, hpchar⟩ := CharP.exists K
    letI : CharP K p := hpchar
    rcases CharP.char_is_prime_or_zero K p with hp | rfl
    · letI : Fact (Nat.Prime p) := ⟨hp⟩
      by_cases hp2 : p = 2
      · subst p
        have hc2 : residueSigma 2 S.C ≤ S.vars.card := by
          simpa using hcapacity 2 1 (by decide) (by decide)
        obtain ⟨D, hD, hDb, hshort⟩ := S.base_counterexample_charTwo n hc2 hcounter
        have hweight := S.weight_mul_base D hDb
        change weight (S.F * D) = weight (intervalCore n c * D) +
          (intervalFreshPrimes n).card * weight D at hweight
        rw [Pilz.card_freshPrimes] at hweight
        have hlo := large_base_unrestricted n c D hc hn hD
        rw [← hweight] at hlo
        omega
      · have h2 : (2 : K) ≠ 0 := by
          intro hz
          have hd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp hz
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
        exact hnoaffine h2 (S.affine_counterexample_of_finite_residue p n
          (hcapacity p) hdegree hcounter)
    · letI : CharZero K := CharP.charP_to_charZero K
      exact hnoaffine (by norm_num) (S.affine_counterexample_charZero n hdegree hcounter)
  have hdist' : n ≤ distance (interval n c) := by
    rw [distance_interval_eq_freshData n c hnpos hc hr]
    exact hdist
  exact (le_distance_iff (interval n c) n).mp hdist'

/-- The entire range from sixty-seven, requiring only the initial weighted
theorem through fifteen. No restriction is imposed on the field or multiplier. -/
theorem intervalBound_large_of_initial (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n)
    (hinitial : ∀ j ≤ 15, ∀ w : ℕ → K, NonzeroWeights j w → IntervalBound j w) :
    IntervalBound n c := by
  apply intervalBound_large_of_affine n c hc hn
  intro D B hDb hBb hne h2
  exact large_affine_all n c D B hc hn hDb hBb hne h2 hinitial

/-- The unconditional weighted interval theorem on the full unbounded tail. -/
theorem intervalBound_ge229 (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 229 ≤ n) : IntervalBound n c := by
  apply intervalBound_large_of_affine n c hc (by omega)
  intro D B hDb hBb hne h2
  exact large_affine n c D B hc hn hDb hBb hne h2

end WeightedPilz
