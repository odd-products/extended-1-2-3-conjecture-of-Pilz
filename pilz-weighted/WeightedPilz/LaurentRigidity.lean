import WeightedPilz.Laurent
import WeightedPilz.Frobenius

/-! Lift polynomial equality classification to Laurent multipliers. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial

variable {σ K : Type*} [Field K] [DecidableEq σ]

@[simp] theorem toLaurent_monomial (d : σ →₀ ℕ) (c : K) :
    toLaurent (monomial d c) = AddMonoidAlgebra.single (integerExponent d) c := by
  change Finsupp.mapDomain integerExponent (Finsupp.single d c) = _
  exact Finsupp.mapDomain_single

/-- Multiplication by a nonzero ordinary polynomial stays injective on
Laurent polynomials, proved by clearing a finite Laurent support. -/
theorem toLaurent_mul_ne_zero (P : MvPolynomial σ K) (hP : P ≠ 0)
    (H : LaurentPoly σ K) (hH : H ≠ 0) : toLaurent P * H ≠ 0 := by
  obtain ⟨e, Q, hQ, hclear⟩ := exists_laurent_clearing H hH
  intro hz
  have heq : toLaurent (P * Q) = 0 := by
    rw [map_mul, hclear, mul_left_comm, hz, mul_zero]
  exact mul_ne_zero hP hQ ((toLaurent_eq_zero _).mp heq)

theorem toLaurent_mul_left_injective (P : MvPolynomial σ K) (hP : P ≠ 0) :
    Function.Injective (fun H : LaurentPoly σ K => toLaurent P * H) := by
  intro H J heq
  change toLaurent P * H = toLaurent P * J at heq
  by_contra hne
  have hdiff : H - J ≠ 0 := sub_ne_zero.mpr hne
  apply toLaurent_mul_ne_zero P hP (H - J) hdiff
  rw [mul_sub, heq, sub_self]

theorem polynomial_cofactor_of_power_output (P Q : MvPolynomial σ K) (hP : P ≠ 0)
    (n : ℕ) (hn : 0 < n) (d : σ →₀ ℕ) (c : K)
    (h : P * Q = monomial d c * P ^ n) :
    Q = monomial d c * P ^ (n - 1) := by
  apply mul_left_cancel₀ hP
  rw [h]
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  calc
    monomial d c * P ^ n = monomial d c * (P ^ (n - 1) * P) := by rw [← pow_succ, hn']
    _ = P * (monomial d c * P ^ (n - 1)) := by ac_rfl

/-- An arbitrary polynomial classification hypothesis transfers to all Laurent
multipliers without changing the attained output support size. -/
theorem laurent_rigidity_of_polynomial_rigidity (p : ℕ) [ExpChar K p]
    (P : MvPolynomial σ K) (hP : P ≠ 0) (N : ℕ)
    (hpoly : ∀ Q : MvPolynomial σ K, Q ≠ 0 → weight (P * Q) = N →
      ∃ (e : ℕ) (d : σ →₀ ℕ) (c : K), c ≠ 0 ∧ P * Q = monomial d c * P ^ p ^ e)
    (H : LaurentPoly σ K) (hH : H ≠ 0)
    (hweight : (toLaurent P * H).support.card = N) :
    ∃ (e : ℕ) (d : σ →₀ ℤ) (c : K), c ≠ 0 ∧
      toLaurent P * H = AddMonoidAlgebra.single d c * (toLaurent P) ^ p ^ e ∧
      H = AddMonoidAlgebra.single d c * (toLaurent P) ^ (p ^ e - 1) := by
  obtain ⟨a, Q, hQ, hclear⟩ := exists_laurent_clearing H hH
  have hweightQ : weight (P * Q) = N := by
    rw [← card_support_toLaurent, map_mul, hclear, mul_left_comm,
      card_support_laurent_translate]
    exact hweight
  obtain ⟨e, d, c, hc, hform⟩ := hpoly Q hQ hweightQ
  have hcleared : AddMonoidAlgebra.single a 1 * (toLaurent P * H) =
      AddMonoidAlgebra.single (integerExponent d) c * (toLaurent P) ^ p ^ e := by
    calc
      AddMonoidAlgebra.single a 1 * (toLaurent P * H) = toLaurent P * toLaurent Q := by
        rw [hclear, mul_left_comm]
      _ = toLaurent (P * Q) := (map_mul _ _ _).symm
      _ = _ := by rw [hform, map_mul, toLaurent_monomial, map_pow]
  let b := -a + integerExponent d
  have hG : toLaurent P * H = AddMonoidAlgebra.single b c * (toLaurent P) ^ p ^ e := by
    have hundo : AddMonoidAlgebra.single (-a) (1 : K) *
        (AddMonoidAlgebra.single a 1 * (toLaurent P * H)) = toLaurent P * H := by
      rw [← mul_assoc, AddMonoidAlgebra.single_mul_single]
      simp only [neg_add_cancel, one_mul]
      change (1 : LaurentPoly σ K) * (toLaurent P * H) = toLaurent P * H
      exact one_mul _
    calc
      toLaurent P * H = AddMonoidAlgebra.single (-a) 1 *
          (AddMonoidAlgebra.single a 1 * (toLaurent P * H)) := hundo.symm
      _ = AddMonoidAlgebra.single (-a) 1 *
          (AddMonoidAlgebra.single (integerExponent d) c * (toLaurent P) ^ p ^ e) := by rw [hcleared]
      _ = _ := by rw [← mul_assoc, AddMonoidAlgebra.single_mul_single, one_mul]
  refine ⟨e, b, c, hc, hG, ?_⟩
  apply toLaurent_mul_left_injective P hP
  change toLaurent P * H = toLaurent P *
    (AddMonoidAlgebra.single b c * (toLaurent P) ^ (p ^ e - 1))
  rw [hG]
  have hn : p ^ e - 1 + 1 = p ^ e := Nat.sub_add_cancel (expChar_pow_pos K p e)
  calc
    AddMonoidAlgebra.single b c * (toLaurent P) ^ p ^ e =
        AddMonoidAlgebra.single b c * ((toLaurent P) ^ (p ^ e - 1) * toLaurent P) := by
      rw [← pow_succ, hn]
    _ = toLaurent P * (AddMonoidAlgebra.single b c * (toLaurent P) ^ (p ^ e - 1)) := by ac_rfl

/-- If a Laurent monomial times a polynomial with nonzero constant term is
itself polynomial, that monomial exponent already occurs in its polynomial support. -/
theorem laurent_exponent_in_polynomial_support (P Q : MvPolynomial σ K)
    (h0 : coeff 0 P ≠ 0) (n : ℕ) (d : σ →₀ ℤ) (c : K) (hc : c ≠ 0)
    (h : toLaurent Q = AddMonoidAlgebra.single d c * (toLaurent P) ^ n) :
    ∃ a ∈ Q.support, integerExponent a = d := by
  have h0pow : coeff 0 (P ^ n) ≠ 0 := by
    rw [← constantCoeff_eq, map_pow, constantCoeff_eq]
    exact pow_ne_zero n h0
  have hzero : (0 : σ →₀ ℤ) ∈ (toLaurent (P ^ n)).support := by
    rw [support_toLaurent]
    exact Finset.mem_image.mpr ⟨0, MvPolynomial.mem_support_iff.mpr h0pow, by simp⟩
  have hd : d ∈ (toLaurent Q).support := by
    rw [h, ← map_pow]
    have hs : (AddMonoidAlgebra.single d c * toLaurent (P ^ n)).support =
        (toLaurent (P ^ n)).support.map (addLeftEmbedding d) :=
      AddMonoidAlgebra.support_single_mul _ c (by simp [hc]) d
    rw [hs]
    exact Finset.mem_map.mpr ⟨0, hzero, by simp⟩
  rw [support_toLaurent] at hd
  exact Finset.mem_image.mp hd

/-- The monomial in the Laurent equality classification has no negative
coordinates whenever the output is an ordinary polynomial. -/
theorem laurent_exponent_nonnegative_of_polynomial_output (P Q : MvPolynomial σ K)
    (h0 : coeff 0 P ≠ 0) (n : ℕ) (d : σ →₀ ℤ) (c : K) (hc : c ≠ 0)
    (h : toLaurent Q = AddMonoidAlgebra.single d c * (toLaurent P) ^ n) :
    ∀ i, 0 ≤ d i := by
  obtain ⟨a, _, rfl⟩ := laurent_exponent_in_polynomial_support P Q h0 n d c hc h
  intro i
  exact Int.natCast_nonneg (a i)

end WeightedPilz
