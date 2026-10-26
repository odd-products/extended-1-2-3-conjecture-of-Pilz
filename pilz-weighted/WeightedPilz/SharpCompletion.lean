import WeightedPilz.Completion
import WeightedPilz.PowerGapPositive
import Mathlib.Algebra.Ring.Parity

/-! Sharp completion and rigidity over arbitrary fields (`thm:completion`). -/

noncomputable section

namespace WeightedPilz

open MvPolynomial

variable {σ K : Type*} [Field K]

theorem weight_freshCompletion (A : MvPolynomial σ K) :
    weight (freshCompletion A) = weight A + 1 := by
  classical
  have hdeg : (rename (some : σ → Option σ) A).degreeOf none = 0 := by
    rw [← natDegree_optionEquivLeft, optionEquivLeft_rename_some, Polynomial.natDegree_C]
  have hdis : Disjoint (rename (some : σ → Option σ) A).support (X none : MvPolynomial (Option σ) K).support := by
    rw [support_X, Finset.disjoint_singleton_right]
    intro h
    have hbound := monomial_le_degreeOf none h
    simp [hdeg] at hbound
  rw [freshCompletion, weight_add_of_disjoint _ _ hdis, weight_rename_some]
  simp [weight, support_X]

private theorem weight_neg_pow (A : MvPolynomial σ K) (n : ℕ) :
    weight ((-A) ^ n) = weight (A ^ n) := by
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_pow]
  · rw [hn.neg_pow]
    simp only [weight, support_neg]

/-- The exact power-weight consequence of the sparse normalized shape. -/
theorem freshCompletion_short_power_weight (A : MvPolynomial σ K)
    (G : MvPolynomial (Option σ) K) (hG : freshCompletion A ∣ G)
    (h0 : (optionEquivLeft K σ G).coeff 0 ≠ 0)
    (hshort : weight G < distance A + 2) :
    ∃ n : ℕ, 0 < n ∧ weight G = weight (A ^ n) + 1 := by
  obtain ⟨d, c, hc, hd, hshape, hw⟩ := freshCompletion_short_shape A G hG h0 hshort
  have hroot := (freshCompletion_dvd_iff A G).mp hG
  rw [hshape, map_add, optionEquivLeft_rename_some, optionEquivLeft_monomial,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_monomial] at hroot
  have hB : (optionEquivLeft K σ G).coeff 0 = -(monomial d.some c * (-A) ^ d none) :=
    eq_neg_of_add_eq_zero_left hroot
  refine ⟨d none, hd, ?_⟩
  rw [hw, hB]
  simp only [weight, support_neg]
  change weight (monomial d.some c * (-A) ^ d none) + 1 = _
  rw [weight_scalar_monomial_mul _ hc, weight_neg_pow]
  rfl

/-- The sharp one-variable lower bound in `thm:completion`. -/
theorem sharp_completion_one (A : MvPolynomial σ K) (hA : A ≠ 0) :
    min (weight A + 1) (distance A + 2) ≤ distance (freshCompletion A) := by
  apply (le_distance_iff _ _).mpr
  intro H hH
  by_contra hnot
  have hshort : weight (freshCompletion A * H) < min (weight A + 1) (distance A + 2) :=
    Nat.lt_of_not_ge hnot
  obtain ⟨k, G, _, hw, hG, hdvd, h0⟩ := freshCompletion_normalize A hA
    (freshCompletion A * H) (mul_ne_zero (freshCompletion_ne_zero A) hH) (dvd_mul_right _ _)
  have hshortG : weight G < distance A + 2 := by
    rw [hw]
    exact hshort.trans_le (Nat.min_le_right _ _)
  obtain ⟨n, hn, hpower⟩ := freshCompletion_short_power_weight A G hdvd h0 hshortG
  by_cases hmany : 2 ≤ weight A
  · have hgap := min_weight_distance_add_one_le_weight_pow (ringExpChar K) A hmany hn
    rw [← hw, hpower] at hshort
    omega
  · have hp : 0 < weight (A ^ n) := by
      simpa [weight, Finset.card_pos, support_nonempty] using pow_ne_zero n hA
    rw [← hw, hpower] at hshort
    have hle := Nat.min_le_left (weight A + 1) (distance A + 2)
    omega

/-- At a core whose minimum equals its weight, every minimum completion
multiple is a scalar monomial times an exponential-characteristic power. -/
theorem sharp_completion_one_rigidity (p : ℕ) [ExpChar K p]
    (A : MvPolynomial σ K) (hA : A ≠ 0) (hmany : 2 ≤ weight A)
    (hminA : distance A = weight A)
    (G : MvPolynomial (Option σ) K) (hG : G ≠ 0) (hdvd : freshCompletion A ∣ G)
    (hweight : weight G = weight A + 1) :
    ∃ (e : ℕ) (d : Option σ →₀ ℕ) (c : K), c ≠ 0 ∧
      G = monomial d c * freshCompletion A ^ p ^ e := by
  classical
  obtain ⟨k, F, hfactor, hw, hF, hFdvd, hF0⟩ :=
    freshCompletion_normalize A hA G hG hdvd
  have hshort : weight F < distance A + 2 := by rw [hw, hweight, hminA]; omega
  obtain ⟨d, c, hc, hd, hshape, hFweight⟩ :=
    freshCompletion_short_shape A F hFdvd hF0 hshort
  have hroot := (freshCompletion_dvd_iff A F).mp hFdvd
  rw [hshape, map_add, optionEquivLeft_rename_some, optionEquivLeft_monomial,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_monomial] at hroot
  have hBneg : (optionEquivLeft K σ F).coeff 0 = -(monomial d.some c * (-A) ^ d none) :=
    eq_neg_of_add_eq_zero_left hroot
  have hpowweight : weight (A ^ d none) = weight A := by
    have hBweight : weight ((optionEquivLeft K σ F).coeff 0) = weight (A ^ d none) := by
      rw [hBneg]
      change (- (monomial d.some c * (-A) ^ d none)).support.card = _
      rw [support_neg]
      change weight (monomial d.some c * (-A) ^ d none) = _
      rw [weight_scalar_monomial_mul _ hc, weight_neg_pow]
    rw [hBweight, hw, hweight] at hFweight
    omega
  have hdistinguished : ∃ e : ℕ, d none = p ^ e := by
    by_contra hn
    have hgap := power_gap p A hmany hd (by simpa using hn)
    rw [hminA, hpowweight] at hgap
    omega
  obtain ⟨e, he⟩ := hdistinguished
  letI : ExpChar (MvPolynomial σ K) p :=
    expChar_of_injective_ringHom (MvPolynomial.C_injective (σ := σ) (R := K)) p
  letI : ExpChar (Polynomial (MvPolynomial σ K)) p :=
    expChar_of_injective_ringHom Polynomial.C_injective p
  have hneg : (-A) ^ p ^ e = -(A ^ p ^ e) := by
    rw [neg_pow, neg_one_pow_expChar_pow, neg_one_mul]
  have hB : (optionEquivLeft K σ F).coeff 0 = monomial d.some c * A ^ p ^ e := by
    simpa only [he, hneg, mul_neg, neg_neg] using hBneg
  let d0 : Option σ →₀ ℕ := d.some.embDomain .some
  have hFform : F = monomial d0 c * freshCompletion A ^ p ^ e := by
    apply (optionEquivLeft K σ).injective
    calc
      optionEquivLeft K σ F =
          Polynomial.C (monomial d.some c * A ^ p ^ e) + Polynomial.monomial (p ^ e) (monomial d.some c) := by
        rw [hshape, map_add, optionEquivLeft_rename_some, optionEquivLeft_monomial, he, hB]
      _ = optionEquivLeft K σ (monomial d0 c * freshCompletion A ^ p ^ e) := by
        simp only [map_mul, map_pow]
        rw [optionEquivLeft_monomial, optionEquivLeft_freshCompletion]
        simp only [d0, Finsupp.embDomain_some_none, Finsupp.some_embDomain_some,
          Polynomial.monomial_zero_left]
        rw [add_pow_expChar_pow]
        simp only [map_mul, map_pow, ← Polynomial.C_mul_X_pow_eq_monomial]
        ring
  refine ⟨e, Finsupp.single none k + d0, c, hc, ?_⟩
  rw [hfactor, hFform, ← mul_assoc, monomial_mul, one_mul]

end WeightedPilz

