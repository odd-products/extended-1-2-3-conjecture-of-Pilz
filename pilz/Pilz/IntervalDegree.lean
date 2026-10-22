import Pilz.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Lean.Elab.Tactic.Omega

/-! Variables larger than the interval length cannot occur in its polynomial. -/

namespace Pilz

open MvPolynomial

theorem interval_degree_zero_of_lt {j p : ℕ} (hjp : j < p) :
    (interval j).degreeOf p = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  rw [degreeOf_le_iff]
  intro d hd
  have hpos : ∀ a ∈ Finset.Icc 1 j, 0 < a := fun _ ha => (Finset.mem_Icc.mp ha).1
  rw [interval_eq_polynomialOf, support_polynomialOf _ hpos] at hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  have hnot : ¬p ∣ a := by
    intro hp
    have hpa := Nat.le_of_dvd (hpos a ha) hp
    have haj := (Finset.mem_Icc.mp ha).2
    omega
  rw [Nat.factorization_eq_zero_of_not_dvd hnot]

end Pilz
