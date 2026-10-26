import WeightedPilz.ResidueCapacity

/-! Translation of full exponent-parity classes under multiplication. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ R : Type*} [CommSemiring R]

theorem residueExponent_idempotent (q : ℕ) (α : σ →₀ ℕ) :
    residueExponent q (residueExponent q α) = residueExponent q α := by
  ext i
  exact Nat.mod_mod _ _

theorem residueExponent_add_congr (q : ℕ) {a b c d : σ →₀ ℕ}
    (hac : residueExponent q a = residueExponent q c)
    (hbd : residueExponent q b = residueExponent q d) :
    residueExponent q (a + b) = residueExponent q (c + d) := by
  ext i
  have hi := congrArg (fun x : σ →₀ ℕ => x i) hac
  have hj := congrArg (fun x : σ →₀ ℕ => x i) hbd
  simp only [residueExponent_apply] at hi hj
  simp only [residueExponent_apply, Finsupp.add_apply, Nat.add_mod, Nat.mod_mod, hi, hj]

/-- Translation by a monomial permutes full residue classes. -/
theorem residuePart_monomial_mul_translate (q : ℕ) (s α : σ →₀ ℕ)
    (hα : residueExponent q α = α) (c : R) (P : MvPolynomial σ R) :
    residuePart q (monomial s c * P) (residueExponent q (s + α)) =
      monomial s c * residuePart q P α := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
      have hiff : residueExponent q (s + d) = residueExponent q (s + α) ↔
          residueExponent q d = α := by
        constructor
        · intro h
          have hc := residueExponent_add_right_cancel q d α s (by simpa only [add_comm] using h)
          exact hc.trans hα
        · intro h
          exact residueExponent_add_congr q rfl (h.trans hα.symm)
      rw [monomial_mul, residuePart_monomial, residuePart_monomial]
      simp only [hiff]
      split_ifs <;> simp [monomial_mul]
  | add P Q hP hQ =>
      simp only [mul_add, residuePart_add, hP, hQ]

/-- A factor concentrated in one class shifts the class selected from the
other factor, without introducing any extra cancellation. -/
theorem residuePart_mul_residuePart (q : ℕ) (P Q : MvPolynomial σ R)
    (α β : σ →₀ ℕ) (hα : residueExponent q α = α) :
    residuePart q (P * residuePart q Q β) (residueExponent q (α + β)) =
      residuePart q P α * residuePart q Q β := by
  rw [residuePart_eq_monomial_mul_dilate q Q β]
  calc
    _ = residuePart q (dilate q (residueRoot q Q β) * (monomial β 1 * P))
          (residueExponent q (β + α)) := by ac_rfl
    _ = dilate q (residueRoot q Q β) *
        residuePart q (monomial β 1 * P) (residueExponent q (β + α)) :=
      residuePart_dilate_mul _ _ _ _
    _ = _ := by rw [residuePart_monomial_mul_translate q β α hα]; ac_rfl

/-- Parity translation is its own inverse. -/
theorem parity_translate_twice (α β γ : σ →₀ ℕ) :
    residueExponent 2 (residueExponent 2 (α + β + γ) + γ) =
      residueExponent 2 (α + β) := by
  ext i
  simp only [residueExponent_apply, Finsupp.add_apply]
  omega

/-- Exact two-source convolution in an output parity class. -/
theorem parity_convolution_two (P Q : MvPolynomial σ R) (α β γ : σ →₀ ℕ)
    (hα : residueExponent 2 α = α)
    (hQ : Q = residuePart 2 Q β + residuePart 2 Q γ) :
    residuePart 2 (P * Q) (residueExponent 2 (α + β)) =
      residuePart 2 P α * residuePart 2 Q β +
      residuePart 2 P (residueExponent 2 (α + β + γ)) * residuePart 2 Q γ := by
  conv_lhs => rw [hQ, mul_add, residuePart_add]
  rw [residuePart_mul_residuePart 2 P Q α β hα]
  rw [← parity_translate_twice α β γ]
  rw [residuePart_mul_residuePart 2 P Q _ γ (residueExponent_idempotent _ _)]

theorem weight_residueRoot {q : ℕ} (hq : 0 < q) (P : MvPolynomial σ R) (α : σ →₀ ℕ) :
    weight (residueRoot q P α) = residueWeight q P α := by
  classical
  rw [residueWeight, residuePart_eq_monomial_mul_dilate, weight_monomial_mul, weight_dilate hq]

end WeightedPilz
