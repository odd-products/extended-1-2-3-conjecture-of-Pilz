import WeightedPilz.BinomialZeroSlices
import WeightedPilz.IntervalFresh
import WeightedPilz.Frobenius
import Mathlib.Data.Nat.Factorization.Basic

/-! The binomial column of the initial core table. A large coordinate-zero
slice is transverse to every direction having a nonzero component in that
coordinate. This also treats directions in additional variables. -/

namespace WeightedPilz.Arithmetic

def initialCoreLineCount (n : ℕ) : ℕ :=
  if n = 12 then 4 else if n = 21 then 7 else if n = 22 ∨ n = 24 then 8 else 6

theorem initial_core_zero_slice (n : ℕ)
    (hn : n = 12 ∨ n = 15 ∨ n = 16 ∨ n = 18 ∨ n = 21 ∨ n = 22 ∨ n = 24)
    (j : ℕ) :
    initialCoreLineCount n ≤
      ((Finset.Icc 1 n \ intervalFreshPrimes n).filter (fun m => m.factorization j = 0)).card := by
  have hfinite : ∀ j ∈ Finset.range (n + 1), initialCoreLineCount n ≤
      ((Finset.Icc 1 n \ intervalFreshPrimes n).filter (fun m => m.factorization j = 0)).card := by
    simp only [Nat.factorization_eq_zero_iff]
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  by_cases hj : j ≤ n
  · exact hfinite j (Finset.mem_range.mpr (by omega))
  · have hcard : initialCoreLineCount n ≤ (Finset.Icc 1 n \ intervalFreshPrimes n).card := by
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    have heq : (Finset.Icc 1 n \ intervalFreshPrimes n).filter
        (fun m => m.factorization j = 0) = Finset.Icc 1 n \ intervalFreshPrimes n := by
      apply Finset.filter_eq_self.mpr
      intro m hm
      have hmn := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hm).1).2
      exact Nat.factorization_eq_zero_of_lt (by omega)
    rwa [heq]

theorem initial_core_binomial_budget (n : ℕ)
    (hn : n = 12 ∨ n = 15 ∨ n = 16 ∨ n = 18 ∨ n = 21 ∨ n = 22 ∨ n = 24) :
    n - 2 * Pilz.freshCount n ≤ 2 * initialCoreLineCount n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end WeightedPilz.Arithmetic

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem mem_support_distinguished_power {σ : Type*} (p e : ℕ) [ExpChar K p]
    (P : MvPolynomial σ K) (d : σ →₀ ℕ) (hd : d ∈ P.support) :
    scaleExponent (p ^ e) d ∈ (P ^ p ^ e).support := by
  classical
  rw [support_pow_expChar]
  exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

/-- Uniform coordinate-zero fiber bounds pass to arbitrary distinguished
powers, with all original coefficients and arbitrary binomial variables. -/
theorem intervalCore_distinguished_binomial_of_zero_slices (n N p e : ℕ)
    [ExpChar K p]
    (hN : ∀ j, N ≤ ((Finset.Icc 1 n \ intervalFreshPrimes n).filter
      (fun m => m.factorization j = 0)).card)
    (c : ℕ → K) (hc : NonzeroWeights n c) (B : Poly K) (hB : weight B = 2) :
    2 * N ≤ weight (intervalCore n c ^ p ^ e * B) := by
  classical
  obtain ⟨a, b, u, v, hab, hu, hv, rfl⟩ := exists_two_monomials_of_weight_two B hB
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ b j := by
    by_contra! h
    exact hab (Finsupp.ext h)
  let T := (Finset.Icc 1 n \ intervalFreshPrimes n).filter (fun m => m.factorization j = 0)
  let f : ℕ → (ℕ →₀ ℕ) := fun m => scaleExponent (p ^ e) m.factorization
  have hq : 0 < p ^ e := pow_pos (expChar_pos K p) e
  have hT : T.image f ⊆ (intervalCore n c ^ p ^ e).support := by
    intro d hd
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
    apply mem_support_distinguished_power p e (intervalCore n c) m.factorization
    rw [intervalCore_support n c hc]
    exact Finset.mem_image.mpr ⟨m, (Finset.mem_filter.mp hm).1, rfl⟩
  have hinj : Set.InjOn f T := by
    intro x hx y hy hxy
    have hxpos := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1).1
    have hypos := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).1).1
    exact Nat.factorization_inj (Nat.ne_of_gt hxpos) (Nat.ne_of_gt hypos)
      (scaleExponent_injective hq hxy)
  have hlines := weight_mul_binomial_of_zero_slice (intervalCore n c ^ p ^ e)
    (T.image f) hT a b u v hu hv j hj (by
      intro d hd
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
      have hz := (Finset.mem_filter.mp hm).2
      simp [f, scaleExponent, hz])
  rw [Finset.card_image_iff.mpr hinj] at hlines
  exact (Nat.mul_le_mul_left 2 (hN j)).trans hlines

/-- The exact `2b` bound in every remaining initial core-table row. -/
theorem intervalCore_initial_distinguished_binomial (p e n : ℕ) [ExpChar K p]
    (hn : n = 12 ∨ n = 15 ∨ n = 16 ∨ n = 18 ∨ n = 21 ∨ n = 22 ∨ n = 24)
    (c : ℕ → K) (hc : NonzeroWeights n c) (B : Poly K) (hB : weight B = 2) :
    2 * Arithmetic.initialCoreLineCount n ≤ weight (intervalCore n c ^ p ^ e * B) :=
  intervalCore_distinguished_binomial_of_zero_slices n _ p e
    (Arithmetic.initial_core_zero_slice n hn) c hc B hB

theorem intervalCore_initial_distinguished_binomial_budget (p e n : ℕ) [ExpChar K p]
    (hn : n = 12 ∨ n = 15 ∨ n = 16 ∨ n = 18 ∨ n = 21 ∨ n = 22 ∨ n = 24)
    (c : ℕ → K) (hc : NonzeroWeights n c) (B : Poly K) (hB : weight B = 2) :
    n - 2 * Pilz.freshCount n ≤ weight (intervalCore n c ^ p ^ e * B) :=
  (Arithmetic.initial_core_binomial_budget n hn).trans
    (intervalCore_initial_distinguished_binomial p e n hn c hc B hB)

end WeightedPilz
