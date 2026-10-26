import WeightedPilz.VariableSlices
import WeightedPilz.Endpoints
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The coprime two-row extraction in `lem:initial-extraction`.
Relative primality is the gcd-one condition, without a Bezout assumption. -/

noncomputable section
namespace WeightedPilz

section AlgebraicExtraction
variable {A : Type*} [CommRing A] [IsDomain A]

theorem linear_factor_two_row_relation (R D U V : A) (hD : D ≠ 0) (k : ℕ)
    (hdiv : (Polynomial.C R + Polynomial.C D * Polynomial.X) ∣
      (Polynomial.C U + Polynomial.C V * Polynomial.X ^ k)) :
    U * D ^ k + V * (-R) ^ k = 0 := by
  let F := FractionRing A
  let f : A →+* F := algebraMap A F
  have hinj : Function.Injective f := IsFractionRing.injective A F
  have hDf : f D ≠ 0 := by
    intro h
    apply hD
    apply hinj
    simpa using h
  let z : F := -f R / f D
  have hroot : Polynomial.eval₂ f z
      (Polynomial.C R + Polynomial.C D * Polynomial.X) = 0 := by
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul,
      Polynomial.eval₂_X]
    dsimp [z]
    rw [mul_comm (f D), div_mul_cancel₀ _ hDf]
    exact add_neg_cancel _
  have heval : f U + f V * (-f R / f D) ^ k = 0 := by
    obtain ⟨Q, hQ⟩ := hdiv
    have h := congrArg (Polynomial.eval₂ f z) hQ
    rw [Polynomial.eval₂_mul, hroot, zero_mul] at h
    simpa only [Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, z] using h
  have hscaled := congrArg (fun x : F => x * (f D) ^ k) heval
  change (f U + f V * (-f R / f D) ^ k) * f D ^ k = 0 * f D ^ k at hscaled
  rw [zero_mul, add_mul, mul_assoc, div_pow,
    div_mul_cancel₀ _ (pow_ne_zero k hDf)] at hscaled
  apply hinj
  simpa only [map_add, map_mul, map_pow, map_neg, map_zero] using hscaled

variable [DecompositionMonoid A]

/-- The two nonzero rows have the same polynomial cofactor. -/
theorem coprime_linear_factor_two_row_extraction (R D U V : A)
    (hD : D ≠ 0) (hV : V ≠ 0) (hcop : IsRelPrime R D) (k : ℕ)
    (hdiv : (Polynomial.C R + Polynomial.C D * Polynomial.X) ∣
      (Polynomial.C U + Polynomial.C V * Polynomial.X ^ k)) :
    ∃ M : A, M ≠ 0 ∧ V = D ^ k * M ∧ U = -((-R) ^ k * M) := by
  have hrel := linear_factor_two_row_relation R D U V hD k hdiv
  have hneg : IsRelPrime D (-R) := by
    intro a ha h
    exact hcop.symm ha (dvd_neg.mp h)
  have hpow : IsRelPrime (D ^ k) ((-R) ^ k) := hneg.pow
  have hdivpow : D ^ k ∣ V * (-R) ^ k := by
    have h : D ^ k ∣ U * D ^ k := dvd_mul_left _ _
    rw [eq_neg_of_add_eq_zero_left hrel] at h
    exact dvd_neg.mp h
  obtain ⟨M, hM⟩ := hpow.dvd_of_dvd_mul_right hdivpow
  refine ⟨M, ?_, hM, ?_⟩
  · intro hz
    exact hV (by rw [hM, hz, mul_zero])
  · apply mul_right_cancel₀ (pow_ne_zero k hD)
    rw [hM] at hrel
    calc
      U * D ^ k = -(D ^ k * M * (-R) ^ k) := eq_neg_of_add_eq_zero_left hrel
      _ = -((-R) ^ k * M) * D ^ k := by ring

end AlgebraicExtraction

section UnitCoefficient
variable {A : Type*} [CommRing A] [IsDomain A]

/-- A unit coefficient prevents a polynomial from having a nonunit constant
common divisor. This applies over multivariate coefficient rings. -/
theorem isRelPrime_constant_of_unit_coeff (R : Polynomial A) (D : A)
    (hD : D ≠ 0) (i : ℕ) (hi : IsUnit (R.coeff i)) :
    IsRelPrime R (Polynomial.C D) := by
  intro Q hQR hQD
  have hdeg : Q.natDegree = 0 := by
    have hle := Polynomial.natDegree_le_of_dvd hQD
      (show Polynomial.C D ≠ 0 by simpa using hD)
    simpa only [Polynomial.natDegree_C, Nat.le_zero] using hle
  have hQ := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hcoeff : Q.coeff 0 ∣ R.coeff i := by
    obtain ⟨T, hT⟩ := hQR
    refine ⟨T.coeff i, ?_⟩
    rw [hT, hQ, Polynomial.coeff_C_mul, Polynomial.coeff_C_zero]
  rw [hQ]
  exact (isUnit_of_dvd_unit hcoeff hi).map Polynomial.C

end UnitCoefficient

section SliceExtraction
variable {σ K : Type*} [DecidableEq σ] [Field K]
open MvPolynomial

theorem weight_two_outsideSlices (S : Set σ) (P : MvPolynomial σ K)
    (β γ : σ →₀ ℕ) (hne : β ≠ γ) :
    weight (outsideSlice S β P) + weight (outsideSlice S γ P) ≤ weight P := by
  classical
  rw [weight, weight, weight, ← Finset.card_union_of_disjoint
    (disjoint_support_outsideSlice S β γ P P hne)]
  apply Finset.card_le_card
  apply Finset.union_subset
  · rw [support_outsideSlice]
    exact Finset.filter_subset _ _
  · rw [support_outsideSlice]
    exact Finset.filter_subset _ _

/-- A product with at most three terms has only one outside-variable fiber
whenever each occupied fiber of the product has at least two terms. -/
theorem single_outsideSlice_of_weight_le_three (S : Set σ)
    (P M : MvPolynomial σ K) (hPvars : (P.vars : Set σ) ⊆ S)
    (hM : M ≠ 0) (hbound : ∀ Q : MvPolynomial σ K, Q ≠ 0 → 2 ≤ weight (P * Q))
    (hw : weight (P * M) ≤ 3) :
    ∃ β : σ →₀ ℕ, outsideExponent S β = β ∧ M = outsideSlice S β M := by
  classical
  obtain ⟨d, hd⟩ := support_nonempty.mpr hM
  let β := outsideExponent S d
  have hβ : outsideSlice S β M ≠ 0 := by
    apply support_nonempty.mp
    refine ⟨d, ?_⟩
    rw [support_outsideSlice]
    exact Finset.mem_filter.mpr ⟨hd, rfl⟩
  have hall : ∀ e ∈ M.support, outsideExponent S e = β := by
    intro e he
    by_contra hne
    have hγ : outsideSlice S (outsideExponent S e) M ≠ 0 := by
      apply support_nonempty.mp
      refine ⟨e, ?_⟩
      rw [support_outsideSlice]
      exact Finset.mem_filter.mpr ⟨he, rfl⟩
    have htwo := weight_two_outsideSlices S (P * M) (outsideExponent S e) β hne
    rw [outsideSlice_mul S _ P M hPvars, outsideSlice_mul S _ P M hPvars] at htwo
    have hb := hbound _ hβ
    have hg := hbound _ hγ
    omega
  refine ⟨β, outsideExponent_idempotent S d, ?_⟩
  ext e
  rw [coeff_outsideSlice]
  by_cases he : e ∈ M.support
  · rw [if_pos (hall e he)]
  · simp [notMem_support_iff.mp he]

/-- The small upper row in the initial extraction lemma forces its cofactor
to be a monomial times a polynomial in the variables of the binomial. -/
theorem small_power_product_single_base_slice (S : Set σ)
    (D M : MvPolynomial σ K) (hDvars : (D.vars : Set σ) ⊆ S)
    (hD : 2 ≤ weight D) (hM : M ≠ 0) (k : ℕ) (hk : 0 < k)
    (hw : weight (D ^ k * M) ≤ 3) :
    ∃ (β : σ →₀ ℕ) (M₀ : MvPolynomial σ K),
      M₀ ≠ 0 ∧ M = monomial β 1 * M₀ ∧ (M₀.vars : Set σ) ⊆ S := by
  classical
  have hD0 : D ≠ 0 := by
    intro hz
    simp [hz, weight] at hD
  have hbound : ∀ Q : MvPolynomial σ K, Q ≠ 0 → 2 ≤ weight (D ^ k * Q) := by
    intro Q hQ
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [pow_succ', mul_assoc]
    exact nonmonomial_weight_mul_two D (D ^ l * Q) hD
      (mul_ne_zero (pow_ne_zero l hD0) hQ)
  have hPvars : ((D ^ k).vars : Set σ) ⊆ S := fun i hi => hDvars (vars_pow D k hi)
  obtain ⟨β, hβ, hslice⟩ := single_outsideSlice_of_weight_le_three S
    (D ^ k) M hPvars hM hbound hw
  obtain ⟨M₀, hfactor, hvars⟩ := outsideSlice_division S β hβ M
  refine ⟨β, M₀, ?_, hslice.trans hfactor, hvars⟩
  intro hz
  apply hM
  rw [hslice, hfactor, hz, mul_zero]

end SliceExtraction
end WeightedPilz
