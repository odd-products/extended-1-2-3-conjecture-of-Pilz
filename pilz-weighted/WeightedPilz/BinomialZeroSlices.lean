import WeightedPilz.BinomialLines

/-! Coordinate-zero slices are transverse to a binomial direction having
a nonzero component in that coordinate. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K]

theorem binomialLineProjection_injOn_zero (a b : σ →₀ ℕ) (j : σ)
    (hj : a j ≠ b j) :
    Set.InjOn (binomialLineProjection a b j) {e : σ →₀ ℕ | e j = 0} := by
  intro e he f hf h
  change e j = 0 at he
  change f j = 0 at hf
  have hdelta : (b j : ℤ) - a j ≠ 0 := by
    intro hz
    exact hj (Int.ofNat_inj.mp (sub_eq_zero.mp hz).symm)
  ext k
  have hk := congrFun h k
  change ((b j : ℤ) - a j) * e k - (e j : ℤ) * ((b k : ℤ) - a k) =
    ((b j : ℤ) - a j) * f k - (f j : ℤ) * ((b k : ℤ) - a k) at hk
  simp only [he, hf, Nat.cast_zero, zero_mul, sub_zero] at hk
  exact Int.ofNat_inj.mp (mul_left_cancel₀ hdelta hk)

/-- A transverse support slice gives two surviving endpoints per exponent. -/
theorem weight_mul_binomial_of_zero_slice (F : MvPolynomial σ K)
    (S : Finset (σ →₀ ℕ)) (hS : S ⊆ F.support)
    (a b : σ →₀ ℕ) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0)
    (j : σ) (hj : a j ≠ b j) (hzero : ∀ e ∈ S, e j = 0) :
    2 * S.card ≤ weight (F * (monomial a u + monomial b v)) := by
  classical
  have hab : a ≠ b := fun h => hj (congrArg (fun e : σ →₀ ℕ => e j) h)
  have hinj : Set.InjOn (binomialLineProjection a b j) S := by
    intro e he f hf h
    exact binomialLineProjection_injOn_zero a b j hj (hzero e he) (hzero f hf) h
  have h := weight_mul_binomial_projection_of_subset F S hS a b u v hu hv hab
    (binomialLineProjection a b j) (binomialLineProjection_eq a b j)
  rwa [Finset.card_image_iff.mpr hinj] at h

theorem exists_two_monomials_of_weight_two (B : MvPolynomial σ K) (hB : weight B = 2) :
    ∃ (a b : σ →₀ ℕ) (u v : K), a ≠ b ∧ u ≠ 0 ∧ v ≠ 0 ∧
      B = monomial a u + monomial b v := by
  classical
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hB
  refine ⟨a, b, coeff a B, coeff b B, hab, ?_, ?_, ?_⟩
  · exact MvPolynomial.mem_support_iff.mp (by rw [hs]; simp)
  · exact MvPolynomial.mem_support_iff.mp (by rw [hs]; simp)
  · conv_lhs => rw [B.as_sum]
    rw [hs]
    simp [hab]

end WeightedPilz
