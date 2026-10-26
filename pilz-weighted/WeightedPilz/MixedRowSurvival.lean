import WeightedPilz.SliceSurvival

/-! Frobenius and monomial translations preserve the six-versus-three row
argument used for the mixed power at sixteen. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ Γ K : Type*} [AddCancelCommMonoid Γ] [IsAddTorsionFree Γ] [DecidableEq Γ] [Field K]

theorem mixed_distinguished_weight_of_six_rows (f : (σ →₀ ℕ) →+ Γ)
    (C : MvPolynomial σ K) (U : Fin 3 → MvPolynomial σ K)
    (V : Fin 6 → MvPolynomial σ K) (uGrade : Fin 3 → Γ) (vGrade : Fin 6 → Γ)
    (hU : C = ∑ i, U i) (hV : C ^ 2 = ∑ i, V i)
    (hUg : ∀ i, PureGrade f (uGrade i) (U i))
    (hVg : ∀ i, PureGrade f (vGrade i) (V i))
    (hVin : Function.Injective vGrade) (bad : Fin 6)
    (hlow : ∀ i, 3 ≤ weight (V i))
    (hhigh : ∀ i, i ≠ bad → 4 ≤ weight (V i))
    (p e r : ℕ) [ExpChar K p] (a b : σ →₀ ℕ) (u v : K) (hv : v ≠ 0) :
    11 ≤ weight (monomial a u * C ^ p ^ e + monomial b v * C ^ (2 * p ^ r)) := by
  classical
  letI : ExpChar (MvPolynomial σ K) p :=
    expChar_of_injective_ringHom (MvPolynomial.C_injective (σ := σ) (R := K)) p
  have hpowsum (n m : ℕ) (B : Fin n → MvPolynomial σ K) :
      (∑ i, B i) ^ p ^ m = ∑ i, B i ^ p ^ m :=
    map_sum (iterateFrobenius (MvPolynomial σ K) p m) B Finset.univ
  let U' : Fin 3 → MvPolynomial σ K := fun i => monomial a u * (U i) ^ p ^ e
  let V' : Fin 6 → MvPolynomial σ K := fun i => monomial b v * (V i) ^ p ^ r
  let ug : Fin 3 → Γ := fun i => f a + (p ^ e) • uGrade i
  let vg : Fin 6 → Γ := fun i => f b + (p ^ r) • vGrade i
  have hUsum : monomial a u * C ^ p ^ e = ∑ i, U' i := by
    rw [hU, hpowsum 3 e U, Finset.mul_sum]
  have hVsum : monomial b v * C ^ (2 * p ^ r) = ∑ i, V' i := by
    rw [pow_mul, hV, hpowsum 6 r V, Finset.mul_sum]
  have hU'g : ∀ i, PureGrade f (ug i) (U' i) := fun i =>
    (PureGrade.monomial f a u).mul ((hUg i).pow (p ^ e))
  have hV'g : ∀ i, PureGrade f (vg i) (V' i) := fun i =>
    (PureGrade.monomial f b v).mul ((hVg i).pow (p ^ r))
  have hPcard : ((monomial a u * C ^ p ^ e).support.image f).card ≤ 3 := by
    rw [hUsum]
    simpa using grade_image_sum_card_le f Finset.univ ug U' (fun i _ => hU'g i)
  have hvg : Function.Injective vg := by
    intro i j hij
    apply hVin
    apply IsAddTorsionFree.nsmul_right_injective (pow_ne_zero r (Nat.ne_of_gt (expChar_pos K p)))
    exact add_left_cancel hij
  have hweight (i : Fin 6) : weight (V' i) = weight (V i) := by
    dsimp [V']
    rw [weight_scalar_monomial_mul b hv, weight_pow_expChar]
  have h := six_rows_survive_three f (monomial a u * C ^ p ^ e) V' vg bad hvg hV'g hPcard
    (fun i => (hlow i).trans_eq (hweight i).symm)
    (fun i hi => (hhigh i hi).trans_eq (hweight i).symm)
  rwa [← hVsum] at h

end WeightedPilz
