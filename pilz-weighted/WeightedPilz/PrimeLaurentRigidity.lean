import WeightedPilz.PrimeRigidity
import WeightedPilz.LaurentRigidity

/-! Prime-index equality for arbitrary Laurent multipliers. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial

variable {K : Type*} [Field K]

theorem prime_interval_laurent_rigidity_of_predecessor_bound
    (p ℓ : ℕ) [ExpChar K p] (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ)
    (c : ℕ → K) (hc : NonzeroWeights ℓ c) (hfield : IntervalBound (ℓ - 1) c)
    (H : LaurentPoly ℕ K) (hH : H ≠ 0)
    (hw : (toLaurent (interval ℓ c) * H).support.card = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℤ) (a : K), a ≠ 0 ∧
      toLaurent (interval ℓ c) * H =
        AddMonoidAlgebra.single d a * (toLaurent (interval ℓ c)) ^ p ^ e ∧
      H = AddMonoidAlgebra.single d a * (toLaurent (interval ℓ c)) ^ (p ^ e - 1) := by
  apply laurent_rigidity_of_polynomial_rigidity p (interval ℓ c)
    (interval_ne_zero c (by omega) hc) ℓ ?_ H hH hw
  intro Q hQ hweight
  exact prime_index_rigidity_of_predecessor_bound p ℓ hℓ hthree c hc hfield
    _ (mul_ne_zero (interval_ne_zero c (by omega) hc) hQ) (dvd_mul_right _ _) hweight

theorem prime_interval_laurent_exponent_nonnegative
    (ℓ : ℕ) (hℓ : 0 < ℓ) (c : ℕ → K) (hc : NonzeroWeights ℓ c)
    (G : Poly K) (n : ℕ) (d : ℕ →₀ ℤ) (a : K) (ha : a ≠ 0)
    (hform : toLaurent G =
      AddMonoidAlgebra.single d a * (toLaurent (interval ℓ c)) ^ n) :
    ∀ i, 0 ≤ d i := by
  apply laurent_exponent_nonnegative_of_polynomial_output (interval ℓ c) G ?_ n d a ha hform
  have hcoeff := coeff_interval ℓ c (a := 1) (by omega)
  have hmem : 1 ∈ Finset.Icc 1 ℓ := Finset.mem_Icc.mpr ⟨le_rfl, hℓ⟩
  have hle : 1 ≤ ℓ := hℓ
  simp only [Nat.factorization_one, if_pos hle] at hcoeff
  exact hcoeff.trans_ne (hc 1 hmem)

end WeightedPilz
