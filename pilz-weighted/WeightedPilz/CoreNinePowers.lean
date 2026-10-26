import WeightedPilz.CoreNine
import WeightedPilz.BivariatePower
import WeightedPilz.AxisBinomial

/-! Power and binomial estimates for the actual interval-nine core. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem coreNineMiddle_support_card (c : ℕ → K) (hc : NonzeroWeights 9 c) :
    (coreNineMiddle c).support.card = 2 := by
  apply Polynomial.card_support_eq_two.mpr
  refine ⟨0, 1, by decide, c 3, c 6, hc 3 (by decide), hc 6 (by decide), ?_⟩
  simp [coreNineMiddle]

theorem intervalCore_nine_power_six (c : ℕ → K) (hc : NonzeroWeights 9 c)
    {n : ℕ} (hn : 0 < n) : 6 ≤ weight (intervalCore 9 c ^ n) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hA0 : (coreNineBottom c).coeff 0 ≠ 0 := by
    simpa [coreNineBottom] using hnz 1 (by omega)
  have hA1 : (coreNineBottom c).coeff 1 ≠ 0 := by
    simpa [coreNineBottom] using hnz 2 (by omega)
  have hdegA : (coreNineBottom c).natDegree = 3 := by
    dsimp [coreNineBottom]
    compute_degree <;> first | exact hnz 8 (by omega) | decide
  have h := bivariateQuadratic_constant_power (coreNineBottom c) (coreNineMiddle c)
    (c 9) (hnz 9 (by omega)) hA0 hA1 (by omega) hn
  rw [coreNineMiddle_support_card c hc] at h
  rw [intervalCore_nine_rename, ← map_pow,
    weight_rename_of_injective coreNineVariables coreNineVariables_injective]
  exact h

theorem intervalCore_nine_distinguished_binomial_six (p e : ℕ) [ExpChar K p]
    (c : ℕ → K) (hc : NonzeroWeights 9 c) (B : Poly K) (hB : weight B = 2) :
    6 ≤ weight (intervalCore 9 c ^ p ^ e * B) := by
  have hmem : ∀ a ∈ ({1, 2, 3, 4, 9} : Finset ℕ),
      a ∈ Finset.Icc 1 9 \ intervalFreshPrimes 9 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
  have hs (a : ℕ) (ha : a ∈ ({1, 2, 3, 4, 9} : Finset ℕ)) :
      a.factorization ∈ (intervalCore 9 c).support :=
    mem_support_iff.mpr (coeff_intervalCore_ne_zero 9 c hc (hmem a ha))
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := Nat.prime_two.factorization
  have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 :=
    (by decide : Nat.Prime 3).factorization
  have h4 : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using Nat.prime_two.factorization_pow (k := 2)
  have h9 : (9 : ℕ).factorization = Finsupp.single 3 2 := by
    simpa using (by decide : Nat.Prime 3).factorization_pow (k := 2)
  apply weight_distinguished_power_mul_binomial_of_two_axes p e (intervalCore 9 c) 2 3 (by decide)
  · simpa only [Nat.factorization_one] using hs 1 (by simp)
  · simpa only [h2] using hs 2 (by simp)
  · simpa only [h4] using hs 4 (by simp)
  · simpa only [h3] using hs 3 (by simp)
  · simpa only [h9] using hs 9 (by simp)
  · exact hB

end WeightedPilz
