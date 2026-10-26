import WeightedPilz.LargeBaseCore
import WeightedPilz.AffineRows
import WeightedPilz.Arithmetic.LargeBudgets

/-! Concrete endpoint and affine bounds for the weighted interval core. -/

noncomputable section
namespace WeightedPilz

open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]

theorem coeff_intervalCore_zero (n : ℕ) (c : ℕ → K) (hn : 0 < n) :
    coeff 0 (intervalCore n c) = c 1 := by
  classical
  have hmem : 1 ∈ Finset.Icc 1 n \ intervalFreshPrimes n := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨le_rfl, hn⟩, ?_⟩
    intro h
    exact Nat.not_prime_one ((Pilz.mem_freshPrimes_iff n 1).mp h).1
  have h := coeff_polynomialOf (Finset.Icc 1 n \ intervalFreshPrimes n) c
    (fun a ha => (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).1)
    (a := 1) (by decide)
  simpa only [Nat.factorization_one, if_pos hmem] using h

theorem coeff_intervalCore_prime (n : ℕ) (c : ℕ → K) {p : ℕ}
    (hp : Nat.Prime p) (hpn : p ≤ n / 2) :
    coeff (Finsupp.single p 1) (intervalCore n c) = c p := by
  classical
  have hmem : p ∈ Finset.Icc 1 n \ intervalFreshPrimes n := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hp.pos, hpn.trans (Nat.div_le_self n 2)⟩, ?_⟩
    intro h
    have hh := ((Pilz.mem_freshPrimes_iff n p).mp h).2.2
    omega
  have h := coeff_polynomialOf (Finset.Icc 1 n \ intervalFreshPrimes n) c
    (fun a ha => (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).1) hp.pos
  simpa only [hp.factorization, if_pos hmem] using h

theorem intervalCore_prime_count_lower (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 0 < n) (hD : D ≠ 0) :
    1 + Pilz.primeCount (n / 2) ≤ weight (intervalCore n c * D) := by
  have h0 : coeff 0 (intervalCore n c) ≠ 0 := by
    rw [coeff_intervalCore_zero n c hn]
    exact hc 1 (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
  have hpure : ∀p∈Pilz.primesUpTo (n / 2), ∃k:ℕ, 0 < k ∧
      coeff (Finsupp.single p k) (intervalCore n c) ≠ 0 := by
    intro p hp
    obtain ⟨hpp, hpn⟩ := (Pilz.mem_primesUpTo (n / 2) p).mp hp
    refine ⟨1, by decide, ?_⟩
    rw [coeff_intervalCore_prime n c hpp hpn]
    exact hc p (Finset.mem_Icc.mpr ⟨hpp.pos, hpn.trans (Nat.div_le_self n 2)⟩)
  have h := pure_endpoints_weight_mul (Pilz.primesUpTo (n / 2))
    (intervalCore n c) D h0 hpure hD
  simpa only [Pilz.card_primesUpTo, Nat.add_comm] using h

/-- Every affine row budget is at least `n` for all `n≥229`, with the actual
weighted core and no assumed component or numerical inequalities. -/
theorem large_affine_budget (n : ℕ) (c : ℕ → K) (D B : Poly K)
    (hc : NonzeroWeights n c) (hn : 229 ≤ n)
    (hne : D ≠ 0 ∨ B ≠ 0) :
    n ≤ weight (intervalCore n c * D) + Pilz.freshCount n * weight (D + intervalCore n c * B) +
      Arithmetic.squareCost n * weight B := by
  have hr := Arithmetic.fresh_count_eight n (show 67 ≤ n by omega)
  have hR := Arithmetic.fresh_le_squareCost n
  change Pilz.freshCount n ≤ Arithmetic.squareCost n at hR
  by_cases hB : B = 0
  · have hD : D ≠ 0 := by simpa [hB] using hne
    simpa [hB, weight] using large_base_unrestricted n c D hc (by omega) hD
  by_cases hD : D = 0
  · have hbase := large_base_unrestricted n c B hc (by omega) hB
    have hfirst : weight (intervalCore n c * B) ≤
        Pilz.freshCount n * weight (intervalCore n c * B) := by
      nlinarith
    have hsecond := Nat.mul_le_mul_right (weight B) hR
    simp only [hD, mul_zero, weight_zero, zero_add]
    omega
  · have hd := intervalCore_prime_count_lower n c D hc (by omega) hD
    have hb : 1 ≤ weight B := Finset.card_pos.mpr (MvPolynomial.support_nonempty.mpr hB)
    have hRmul := Nat.mul_le_mul_left (Arithmetic.squareCost n) hb
    have hbudget := Arithmetic.dimension_square_budget hn
    change n ≤ 1 + Pilz.primeCount (n / 2) + Arithmetic.squareCost n at hbudget
    omega

/-- The normalized weighted interval times any nonzero affine base cofactor
has at least `n` terms throughout the unbounded range `n≥229`. -/
theorem large_affine (n : ℕ) (c : ℕ → K) (D B : Poly K)
    (hc : NonzeroWeights n c) (hn : 229 ≤ n)
    (hDb : ∀p∈intervalFreshPrimes n, ∀d∈D.support, d p = 0)
    (hBb : ∀p∈intervalFreshPrimes n, ∀d∈B.support, d p = 0)
    (hne : D ≠ 0 ∨ B ≠ 0) (h2 : (2 : K) ≠ 0) :
    n ≤ weight ((intervalCore n c + ∑p∈intervalFreshPrimes n, X p) *
      (D + (∑p∈intervalFreshPrimes n, X p) * B)) := by
  have hr : (intervalFreshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    rw [Pilz.card_freshPrimes]
    have h := Arithmetic.fresh_count_eight n (show 67 ≤ n by omega)
    omega
  let S := intervalFreshData n c (show 0 < n by omega) hc hr
  have heq := S.weight_mul_affine D B hDb hBb h2
  change weight ((intervalCore n c + ∑p∈intervalFreshPrimes n, X p) *
    (D + (∑p∈intervalFreshPrimes n, X p) * B)) =
    weight (intervalCore n c * D) + (intervalFreshPrimes n).card *
      weight (D + intervalCore n c * B) +
      ((intervalFreshPrimes n).card * ((intervalFreshPrimes n).card + 1) / 2) * weight B at heq
  rw [Pilz.card_freshPrimes] at heq
  rw [heq]
  exact large_affine_budget n c D B hc hn hne

end WeightedPilz
