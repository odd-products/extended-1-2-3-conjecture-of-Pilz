import Pilz.Extremal
import Pilz.ParityClasses

/-! Square-root descent for extremal multiples and expensive residual classes. -/

namespace Pilz

/-- Step 4 of the synchronized normal form: a positive-width extremal
multiple cannot itself be divisible by `F²`. -/
theorem extremal_not_square_multiple (F G J : Poly) (B : Finset ℕ) (N : ℕ)
    (hG : Extremal F B N G) (hpositive : 0 < totalWidth B G)
    (hfactor : G = F ^ 2 * J) : False := by
  obtain ⟨ε, _hε, hclass⟩ := exists_nonzero_parityClass G hG.1.1
  rw [hfactor] at hclass
  have hroot := squareClass_multiple_ne_zero F J ε hclass
  have hweight : weight (F * classRoot J ε) ≤ weight G := by
    rw [← classWeight_square_mul, ← hfactor]
    exact classWeight_le_weight G ε
  have hshort : ShortMultiple F N (F * classRoot J ε) :=
    ⟨hroot, dvd_mul_right F _, hweight.trans_lt hG.1.2.2⟩
  have hmin := (hG.2 (F * classRoot J ε) hshort).1
  have hhalf := twice_totalWidth_squareClass_multiple_le B F J ε hclass
  rw [← hfactor] at hhalf
  omega

/-- The quantitative core of Proposition `prop:residual`. The preceding
support estimates supply `hwidth` and positivity of the cofactor width. -/
theorem residual_class_cost (F G J H : Poly) (B : Finset ℕ) (N : ℕ)
    (hG : Extremal F B N G)
    (hpositive : 0 < totalWidth B H)
    (hwidth : totalWidth B (F ^ 2 * J) + totalWidth B H ≤ 2 * totalWidth B G)
    (ε : ℕ →₀ ℕ) (hclass : parityClass (F ^ 2 * J) ε ≠ 0) :
    N ≤ classWeight (F ^ 2 * J) ε := by
  by_contra hnot
  have hroot := squareClass_multiple_ne_zero F J ε hclass
  have hshort : ShortMultiple F N (F * classRoot J ε) := by
    refine ⟨hroot, dvd_mul_right F _, ?_⟩
    rw [← classWeight_square_mul]
    exact Nat.lt_of_not_ge hnot
  have hmin := (hG.2 (F * classRoot J ε) hshort).1
  have hhalf := twice_totalWidth_squareClass_multiple_le B F J ε hclass
  omega

/-- The same cost statement for the function-valued indices used by the
capacity and protected-class lemmas. -/
theorem residual_class_cost_all (F G J H : Poly) (B : Finset ℕ) (N : ℕ)
    (hG : Extremal F B N G)
    (hpositive : 0 < totalWidth B H)
    (hwidth : totalWidth B (F ^ 2 * J) + totalWidth B H ≤ 2 * totalWidth B G)
    (ε : ℕ → ℕ) (hclass : 0 < classWeight (F ^ 2 * J) ε) :
    N ≤ classWeight (F ^ 2 * J) ε := by
  obtain ⟨η, _hη, heq⟩ := exists_parityIndex_of_classWeight_pos hclass
  rw [← heq] at hclass ⊢
  apply residual_class_cost F G J H B N hG hpositive hwidth η
  intro hz
  have hw := weight_parityClass (F ^ 2 * J) η
  rw [hz, weight_zero] at hw
  omega

end Pilz
