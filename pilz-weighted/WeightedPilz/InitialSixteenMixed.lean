import WeightedPilz.InitialMixedRows
import WeightedPilz.CoreSixteen

/-! The mixed distinguished/double-distinguished estimate at sixteen. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem intervalCore_sixteen_mixed_distinguished_monomials (p e r : ℕ) [ExpChar K p]
    (c : ℕ → K) (hc : NonzeroWeights 16 c) (h2 : (2 : K) ≠ 0)
    (a b : ℕ →₀ ℕ) (u v : K) (hv : v ≠ 0) :
    11 ≤ weight (monomial a u * intervalCore 16 c ^ p ^ e +
      monomial b v * intervalCore 16 c ^ (2 * p ^ r)) := by
  classical
  have hAvars : (baseSixteen c).vars ⊆ {2, 3} := by
    rw [baseSixteen_rename]
    intro q hq
    obtain ⟨i, _, rfl⟩ := mem_vars_rename coreNineVariables _ hq
    cases i <;> simp [coreNineVariables]
  rw [intervalCore_sixteen_decomposition]
  exact arithmetic_linear_pair_mixed_power_weight p e r c hc h2
    (baseSixteen c) hAvars (baseSixteen_distance_four c hc) a b u v hv

theorem intervalCore_sixteen_mixed_distinguished (p e r : ℕ) [ExpChar K p]
    (c : ℕ → K) (hc : NonzeroWeights 16 c) (h2 : (2 : K) ≠ 0)
    (M N : Poly K) (hM : weight M = 1) (hN : weight N = 1) :
    11 ≤ weight (M * intervalCore 16 c ^ p ^ e + N * intervalCore 16 c ^ (2 * p ^ r)) := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hM
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hN
  have hvm : coeff b N ≠ 0 := mem_support_iff.mp (by rw [hb]; simp)
  have hMM : M = monomial a (coeff a M) := (Finsupp.support_eq_singleton.mp ha).2
  have hNN : N = monomial b (coeff b N) := (Finsupp.support_eq_singleton.mp hb).2
  rw [hMM, hNN]
  exact intervalCore_sixteen_mixed_distinguished_monomials p e r c hc h2 a b _ _ hvm

end WeightedPilz


