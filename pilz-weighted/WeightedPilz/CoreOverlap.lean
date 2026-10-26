import WeightedPilz.DilationOverlap
import WeightedPilz.IntegerResidues

/-! A uniform arithmetic bound for unequal distinguished powers of an interval core. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem intervalCore_residue_capacity_of_square (n r : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : n < (r + 1) ^ 2)
    {q : ℕ} (hq : 2 ≤ q) : residueSigma q (intervalCore n c) ≤ r := by
  have hpow : (r + 1) ^ 2 ≤ (r + 1) ^ q :=
    Nat.pow_le_pow_right (by omega) hq
  have h := residueSigma_intervalCore_pow_le n q 1 r c hc (by omega)
    (by simpa using hn.trans_le hpow)
  simpa only [pow_one] using h

theorem intervalCore_unequal_distinguished_sum_bound (n r p e f : ℕ) [ExpChar K p]
    (c : ℕ → K) (hc : NonzeroWeights n c) (hn : n < (r + 1) ^ 2)
    (M L : Poly K) (hef : p ^ e ≠ p ^ f) (hM : weight M = 1) (hL : weight L = 1) :
    2 * weight (intervalCore n c) ≤
      weight (M * intervalCore n c ^ p ^ e + L * intervalCore n c ^ p ^ f) + 2 * r := by
  obtain ⟨a, u, hu, rfl⟩ := exists_monomial_of_weight_one M hM
  obtain ⟨b, v, hv, rfl⟩ := exists_monomial_of_weight_one L hL
  have hp : 2 ≤ p := by
    have hp0 := expChar_pos K p
    by_contra hnot
    have hp1 : p = 1 := by omega
    simp [hp1] at hef
  have aux (i j : ℕ) (hij : i ≤ j) (hneq : p ^ i ≠ p ^ j)
      (a b : ℕ →₀ ℕ) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) :
      2 * weight (intervalCore n c) ≤
        weight (monomial a u * intervalCore n c ^ p ^ i +
          monomial b v * intervalCore n c ^ p ^ j) + 2 * r := by
    have hlt : i < j := by
      have hne : i ≠ j := fun h => hneq (congrArg (fun k => p ^ k) h)
      omega
    have hratio : 2 ≤ p ^ (j - i) := by
      have h := Nat.pow_le_pow_right (by omega : 1 ≤ p) (show 1 ≤ j - i by omega)
      simp only [pow_one] at h
      exact hp.trans h
    have hσ := intervalCore_residue_capacity_of_square n r c hc hn hratio
    have h := distinguished_monomial_sum_overlap p i j hij (intervalCore n c) a b u v hu hv
    omega
  rcases le_total e f with h | h
  · exact aux e f h hef a b u v hu hv
  · simpa only [add_comm] using aux f e h hef.symm b a v u hv hu

end WeightedPilz
