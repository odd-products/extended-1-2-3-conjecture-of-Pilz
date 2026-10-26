import WeightedPilz.ParityConvolution
import WeightedPilz.ParityDecomposition
import WeightedPilz.ParityTriple

/-! Sharp weighted cancellation estimates for a three-plus-one parity input. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] [ExpChar K 2]

private theorem parity_weight_mul_one (P Q : Poly K) (hQ : weight Q = 1) :
    weight (P * Q) = weight P := by
  classical
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hQ
  have hc : coeff d Q ≠ 0 := mem_support_iff.mp (by rw [hd]; simp)
  have hmono : Q = monomial d (coeff d Q) := (Finsupp.support_eq_singleton.mp hd).2
  rw [hmono, mul_comm]
  exact weight_scalar_monomial_mul d hc P

/-- The cost function used by the finite arithmetic tables agrees with the
algebraic three-term lower bound on the complete required range. -/
theorem tripleIntervalCost_eq_parityTripleCost {k : ℕ} (hk : k ≤ 6) :
    tripleIntervalCost k = Arithmetic.parityTripleCost k := by
  interval_cases k <;> decide

theorem interval_parity_mul_three_cost (n s : ℕ) (hn : n ≤ 48)
    (c : ℕ → K) (hc : NonzeroWeights n c) (hs : Squarefree s)
    (D : Poly K) (β : ℕ →₀ ℕ) (hβ : residueWeight 2 D β = 3) :
    Arithmetic.parityTripleCost (Nat.sqrt (n / s)) ≤
      weight (residuePart 2 (interval n c) s.factorization * residuePart 2 D β) := by
  have hk : Nat.sqrt (n / s) ≤ 6 := by
    have hdiv := Nat.div_le_self n s
    have hsqrt := Nat.sqrt_le_sqrt (hdiv.trans hn)
    exact hsqrt.trans (Nat.le_of_lt_succ (Nat.sqrt_lt.mpr (by decide : 48 < 7 * 7)))
  have hw := interval_three_term_cost (Nat.sqrt (n / s)) hk
    (fun b => c (s * b ^ 2)) (interval_parity_class_weights n s c hc hs)
    (residueRoot 2 D β) (by rwa [weight_residueRoot (by decide : 0 < 2)])
  rw [tripleIntervalCost_eq_parityTripleCost hk] at hw
  rw [interval_parity_class n s c hs,
    residuePart_eq_monomial_mul_dilate 2 D β, monomialOf]
  have heq :
      (monomial s.factorization 1 * dilate 2 (interval (Nat.sqrt (n / s)) (fun b => c (s * b ^ 2)))) *
        (monomial β 1 * dilate 2 (residueRoot 2 D β)) =
      monomial (s.factorization + β) (1 : K) *
        dilate 2 (interval (Nat.sqrt (n / s)) (fun b => c (s * b ^ 2)) * residueRoot 2 D β) := by
    calc
      _ = (monomial s.factorization 1 * monomial β 1) *
          (dilate 2 (interval (Nat.sqrt (n / s)) (fun b => c (s * b ^ 2))) *
            dilate 2 (residueRoot 2 D β)) := by ac_rfl
      _ = _ := by rw [monomial_mul, one_mul, dilate_mul]
  rw [heq, weight_monomial_mul, weight_dilate (by decide : 0 < 2)]
  exact hw

/-- The monomial input class has exactly the size of the kernel class. -/
theorem interval_parity_mul_one_weight (n s : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hs : Squarefree s)
    (D : Poly K) (γ : ℕ →₀ ℕ) (hγ : residueWeight 2 D γ = 1) :
    weight (residuePart 2 (interval n c) s.factorization * residuePart 2 D γ) =
      Nat.sqrt (n / s) := by
  rw [parity_weight_mul_one _ _ hγ]
  exact interval_parity_class_weight n s c hc hs

/-- The two kernel classes competing for a fixed output class obey the
literal truncated-subtraction cost from the manuscript. -/
theorem interval_parity_cancellation_cost (n s t : ℕ) (hn : n ≤ 48)
    (c : ℕ → K) (hc : NonzeroWeights n c) (hs : Squarefree s) (ht : Squarefree t)
    (D : Poly K) (β γ : ℕ →₀ ℕ)
    (hβ : residueWeight 2 D β = 3) (hγ : residueWeight 2 D γ = 1)
    (hD : D = residuePart 2 D β + residuePart 2 D γ)
    (hst : residueExponent 2 (s.factorization + β + γ) = t.factorization) :
    Arithmetic.parityTripleCost (Nat.sqrt (n / s)) - Nat.sqrt (n / t) ≤
      residueWeight 2 (interval n c * D) (residueExponent 2 (s.factorization + β)) := by
  have hcost := interval_parity_mul_three_cost n s hn c hc hs D β hβ
  have hone := interval_parity_mul_one_weight n t c hc ht D γ hγ
  have hcancel := weight_le_weight_add_add
    (residuePart 2 (interval n c) s.factorization * residuePart 2 D β)
    (residuePart 2 (interval n c) t.factorization * residuePart 2 D γ)
  have hconv := parity_convolution_two (interval n c) D s.factorization β γ
    (residue_factorization_squarefree hs) hD
  rw [hst] at hconv
  rw [← hconv] at hcancel
  rw [hone] at hcancel
  change _ ≤ weight _
  omega

/-- If the competing kernel class is empty, the complete three-term cost
survives in its output class. -/
theorem interval_parity_unpaired_three_cost (n s : ℕ) (hn : n ≤ 48)
    (c : ℕ → K) (hc : NonzeroWeights n c) (hs : Squarefree s)
    (D : Poly K) (β γ : ℕ →₀ ℕ)
    (hβ : residueWeight 2 D β = 3)
    (hD : D = residuePart 2 D β + residuePart 2 D γ)
    (hempty : residuePart 2 (interval n c) (residueExponent 2 (s.factorization + β + γ)) = 0) :
    Arithmetic.parityTripleCost (Nat.sqrt (n / s)) ≤
      residueWeight 2 (interval n c * D) (residueExponent 2 (s.factorization + β)) := by
  have hconv := parity_convolution_two (interval n c) D s.factorization β γ
    (residue_factorization_squarefree hs) hD
  rw [hempty, zero_mul, add_zero] at hconv
  rw [residueWeight, hconv]
  exact interval_parity_mul_three_cost n s hn c hc hs D β hβ

/-- Both members of a parity pair give the exact pair cost, including pairs
with one empty kernel class. -/
theorem interval_parity_pair_cost (n s t : ℕ) (hn : n ≤ 48)
    (c : ℕ → K) (hc : NonzeroWeights n c) (hs : Squarefree s) (ht : Squarefree t)
    (D : Poly K) (β γ : ℕ →₀ ℕ)
    (hβ : residueWeight 2 D β = 3) (hγ : residueWeight 2 D γ = 1)
    (hD : D = residuePart 2 D β + residuePart 2 D γ)
    (hst : residueExponent 2 (s.factorization + β + γ) = t.factorization) :
    Arithmetic.parityPairCost (Nat.sqrt (n / s)) (Nat.sqrt (n / t)) ≤
      residueWeight 2 (interval n c * D) (residueExponent 2 (s.factorization + β)) +
      residueWeight 2 (interval n c * D) (residueExponent 2 (t.factorization + β)) := by
  have hts : residueExponent 2 (t.factorization + β + γ) = s.factorization := by
    ext i
    have hi := congrArg (fun d : ℕ →₀ ℕ => d i) hst
    have hs0 := congrArg (fun d : ℕ →₀ ℕ => d i) (residue_factorization_squarefree hs)
    simp only [residueExponent_apply, Finsupp.add_apply] at hi hs0 ⊢
    omega
  have hconvS := parity_convolution_two (interval n c) D s.factorization β γ
    (residue_factorization_squarefree hs) hD
  have hconvT := parity_convolution_two (interval n c) D t.factorization β γ
    (residue_factorization_squarefree ht) hD
  rw [hst] at hconvS
  rw [hts] at hconvT
  by_cases hk : Nat.sqrt (n / s) = 0
  · have hs0 : residuePart 2 (interval n c) s.factorization = 0 := by
      by_contra hne
      have hpos := weight_pos hne
      have hw := interval_parity_class_weight n s c hc hs
      change weight _ = _ at hw
      omega
    rw [hs0, zero_mul, zero_add] at hconvS
    rw [hs0, zero_mul, add_zero] at hconvT
    have h3 := interval_parity_mul_three_cost n t hn c hc ht D β hβ
    have h1 := interval_parity_mul_one_weight n t c hc ht D γ hγ
    rw [Arithmetic.parityPairCost, if_pos hk, residueWeight, residueWeight, hconvS, hconvT, h1]
    omega
  · by_cases hl : Nat.sqrt (n / t) = 0
    · have ht0 : residuePart 2 (interval n c) t.factorization = 0 := by
        by_contra hne
        have hpos := weight_pos hne
        have hw := interval_parity_class_weight n t c hc ht
        change weight _ = _ at hw
        omega
      rw [ht0, zero_mul, add_zero] at hconvS
      rw [ht0, zero_mul, zero_add] at hconvT
      have h3 := interval_parity_mul_three_cost n s hn c hc hs D β hβ
      have h1 := interval_parity_mul_one_weight n s c hc hs D γ hγ
      rw [Arithmetic.parityPairCost, if_neg hk, if_pos hl,
        residueWeight, residueWeight, hconvS, hconvT, h1]
      omega
    · rw [Arithmetic.parityPairCost, if_neg hk, if_neg hl]
      exact Nat.add_le_add
        (interval_parity_cancellation_cost n s t hn c hc hs ht D β γ hβ hγ hD hst)
        (interval_parity_cancellation_cost n t s hn c hc ht hs D β γ hβ hγ hD hts)

end WeightedPilz
