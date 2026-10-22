import Pilz.ComponentProfile

/-! The generic degree bound for the smooth interval polynomials. It avoids
expanding any finite table of monomials. -/

namespace Pilz

open MvPolynomial

theorem smoothInterval_degreeOf_two_le (T : Finset ℕ) (n d : ℕ)
    (hn : n < 2 ^ (d + 1)) : (smoothInterval T n).degreeOf 2 ≤ d := by
  classical
  rw [degreeOf_le_iff]
  intro e he
  have hpos : ∀ a ∈ smoothNumbers T n, 0 < a := by
    intro a ha
    exact ((mem_smoothNumbers T n a).mp ha).1
  rw [smoothInterval, support_polynomialOf _ hpos] at he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  have hap := hpos a ha
  have han : a ≤ n := ((mem_smoothNumbers T n a).mp ha).2.1
  have hpow : 2 ^ (a.factorization 2) ≤ a := Nat.ordProj_le 2 (Nat.ne_of_gt hap)
  have hlt : 2 ^ (a.factorization 2) < 2 ^ (d + 1) := hpow.trans_lt (han.trans_lt hn)
  have hv : a.factorization 2 < d + 1 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  omega

end Pilz
