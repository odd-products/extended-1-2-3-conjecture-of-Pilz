import Pilz.Normalize
import Pilz.Width

/-!
# Factoring coordinates of width zero

If a nonzero polynomial has width zero in each base coordinate, its dependence
on those coordinates is entirely a common monomial factor. Removing that
factor leaves a polynomial independent of every base variable and preserves
all product weights.
-/

noncomputable section

namespace Pilz

/-- Zero base widths allow all base dependence to be removed as a monomial. -/
theorem exists_base_independent_factor (B : Finset ℕ) (H : Poly) (hH : H ≠ 0)
    (hwidth : ∀ p ∈ B, widthOf p H = 0) :
    ∃ (e : ℕ →₀ ℕ) (Q : Poly),
      H = MvPolynomial.monomial e 1 * Q ∧ Q ≠ 0 ∧
      (∀ p ∈ B, ∀ d ∈ Q.support, d p = 0) ∧
      (∀ P : Poly, weight (P * Q) = weight (P * H)) := by
  obtain ⟨e, Q, hfactor, hQ, hnorm, _hweight, hproducts, _hvars⟩ :=
    exists_normalization H hH
  refine ⟨e, Q, hfactor, hQ, ?_, hproducts⟩
  intro p hp
  obtain ⟨d, hd, hd0⟩ := hnorm p
  have hord : orderOf p Q = 0 := by
    have hle := orderOf_le_support p hd
    rw [hd0] at hle
    exact Nat.eq_zero_of_le_zero hle
  have hwQ : widthOf p Q = 0 := by
    have hw := widthOf_monomial_mul p e hQ
    rw [← hfactor] at hw
    exact hw.symm.trans (hwidth p hp)
  have hdegree : Q.degreeOf p = 0 := by
    simpa only [widthOf, hord, Nat.sub_zero] using hwQ
  intro d hd
  have hle := MvPolynomial.monomial_le_degreeOf p hd
  rw [hdegree] at hle
  exact Nat.eq_zero_of_le_zero hle

end Pilz
