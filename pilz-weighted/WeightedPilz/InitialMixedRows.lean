import WeightedPilz.LinearPairMixed
import WeightedPilz.TwelveCoreDecomposition
import WeightedPilz.Initial
import WeightedPilz.BinomialZeroSlices
import WeightedPilz.PowerGap

/-! The mixed distinguished/double-distinguished estimate at sixteen. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

private theorem degree_zero_of_vars_bound {P : Poly K} {T : Finset ℕ}
    (hP : P.vars ⊆ T) {j : ℕ} (hj : j ∉ T) : P.degreeOf j = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [degreeOf_le_iff]
  intro d hd
  exact Nat.le_of_eq (mem_support_notMem_vars_zero hd (fun hi => hj (hP hi)))

theorem arithmetic_linear_pair_mixed_power_weight (p e r : ℕ) [ExpChar K p]
    (c : ℕ → K) (hc : NonzeroWeights 16 c) (h2 : (2 : K) ≠ 0)
    (A : Poly K) (hAvars : A.vars ⊆ {2, 3}) (hAdist : 4 ≤ distance A)
    (a b : ℕ →₀ ℕ) (u v : K) (hv : v ≠ 0) :
    11 ≤ weight (monomial a u * (A + arithmeticFiveRow c * X 5 + arithmeticBinomial 7 c * X 7) ^ p ^ e +
      monomial b v * (A + arithmeticFiveRow c * X 5 + arithmeticBinomial 7 c * X 7) ^ (2 * p ^ r)) := by
  classical
  let L := arithmeticFiveRow c
  let D := arithmeticBinomial 7 c
  have hnz (m : ℕ) (hm : 1 ≤ m ∧ m ≤ 16) : c m ≠ 0 := hc m (Finset.mem_Icc.mpr hm)
  have h0x : (0 : ℕ →₀ ℕ) ≠ Finsupp.single 2 1 := by
    intro h
    have hh := congrArg (fun d : ℕ →₀ ℕ => d 2) h
    simpa using hh
  have h0y : (0 : ℕ →₀ ℕ) ≠ Finsupp.single 3 1 := by
    intro h
    have hh := congrArg (fun d : ℕ →₀ ℕ => d 3) h
    simpa using hh
  have hL0 : coeff (0 : ℕ →₀ ℕ) L = c 5 := by simp [L, arithmeticFiveRow]
  have hLx : coeff (Finsupp.single 2 1) L = c 10 := by
    simp [L, arithmeticFiveRow, coeff_C_mul, h0x]
  have hLy : coeff (Finsupp.single 3 1) L = c 15 := by
    simp [L, arithmeticFiveRow, coeff_C_mul, h0y]
  have hD0 : coeff (0 : ℕ →₀ ℕ) D = c 7 := by simp [D, arithmeticBinomial]
  have hDx : coeff (Finsupp.single 2 1) D = c 14 := by
    simp [D, arithmeticBinomial, coeff_C_mul, h0x]
  have hL : L ≠ 0 := by intro hz; apply hnz 5 (by omega); rw [← hL0, hz, coeff_zero]
  have hD : D ≠ 0 := by intro hz; apply hnz 7 (by omega); rw [← hD0, hz, coeff_zero]
  have hA : A ≠ 0 := by intro hz; simp only [hz, distance_zero] at hAdist; omega
  have hLvars : L.vars ⊆ {2, 3} := by
    unfold L arithmeticFiveRow
    apply (vars_add_subset _ _).trans
    apply Finset.union_subset
    · apply (vars_add_subset _ _).trans
      apply Finset.union_subset
      · simp
      · exact (vars_mul _ _).trans (by simp)
    · exact (vars_mul _ _).trans (by simp)
  have hDvars : D.vars ⊆ {2} := by
    unfold D arithmeticBinomial
    apply (vars_add_subset _ _).trans
    have hxvars : (C (c (2 * 7)) * X 2 : Poly K).vars ⊆ {2} :=
      (vars_mul _ _).trans (by simp)
    simpa using hxvars
  have hLi : L = interval 3 (fun m => c (5 * m)) := by
    have hs : Finset.Icc 1 3 = {1, 2, 3} := by decide
    have hthree := (by decide : Nat.Prime 3).factorization
    simp [L, arithmeticFiveRow, interval, polynomialOf, hs,
      Nat.prime_two.factorization, hthree, ← C_apply, ← C_mul_X_pow_eq_monomial] <;> ring
  have hDi : D = interval 2 (fun m => c (7 * m)) := by
    have hs : Finset.Icc 1 2 = {1, 2} := by decide
    simp [D, arithmeticBinomial, interval, polynomialOf, hs,
      Nat.prime_two.factorization, ← C_apply, ← C_mul_X_pow_eq_monomial] <;> ring
  have hLweights : NonzeroWeights 3 (fun m => c (5 * m)) := by
    intro m hm
    have := Finset.mem_Icc.mp hm
    apply hnz
    omega
  have hDweights : NonzeroWeights 2 (fun m => c (7 * m)) := by
    intro m hm
    have := Finset.mem_Icc.mp hm
    apply hnz
    omega
  have hLdist : distance L = 3 := by
    rw [hLi]
    exact distance_interval_eq_of_le_eight 3 (by decide) _ hLweights
  have hDdist : distance D = 2 := by
    rw [hDi]
    exact distance_interval_eq_of_le_eight 2 (by decide) _ hDweights
  have hLL : 4 ≤ weight (L ^ 2) := by
    have hh := power_gap_of_residue_variation L 2
      (d := 0) (e := Finsupp.single 2 1)
      (mem_support_iff.mpr (by simpa only [hL0] using hnz 5 (by omega)))
      (mem_support_iff.mpr (by simpa only [hLx] using hnz 10 (by omega)))
      (by simp) (n := 2) (by decide) h2
    simpa only [hLdist] using hh
  have hDD : 3 ≤ weight (D ^ 2) := by
    have hh := power_gap_of_residue_variation D 2
      (d := 0) (e := Finsupp.single 2 1)
      (mem_support_iff.mpr (by simpa only [hD0] using hnz 7 (by omega)))
      (mem_support_iff.mpr (by simpa only [hDx] using hnz 14 (by omega)))
      (by simp) (n := 2) (by decide) h2
    simpa only [hDdist] using hh
  have hLD : 4 ≤ weight (L * D) := by
    let T : Finset (ℕ →₀ ℕ) := {0, Finsupp.single 3 1}
    have hT : T ⊆ L.support := by
      intro d hd
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact mem_support_iff.mpr (by simpa only [hL0] using hnz 5 (by omega))
      · exact mem_support_iff.mpr (by simpa only [hLy] using hnz 15 (by omega))
    have hh := weight_mul_binomial_of_zero_slice L T hT 0 (Finsupp.single 2 1)
      (c 7) (c 14) (hnz 7 (by omega)) (hnz 14 (by omega)) 2 (by simp)
      (by intro d hd; simp only [T, Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl <;> simp)
    have heq : monomial (0 : ℕ →₀ ℕ) (c 7) + monomial (Finsupp.single 2 1) (c 14) = D := by
      simp only [D, arithmeticBinomial, C_mul_X_eq_monomial, ← C_apply,
        show 2 * 7 = 14 from rfl]
    rw [heq] at hh
    simpa [T, h0y] using hh
  have hAA : 4 ≤ weight (A ^ 2) := by
    simpa only [pow_two] using hAdist.trans (distance_le_weight_mul A A hA)
  have hAL : 4 ≤ weight (A * L) := hAdist.trans (distance_le_weight_mul A L hL)
  have hAD : 4 ≤ weight (A * D) := hAdist.trans (distance_le_weight_mul A D hD)
  exact linear_pair_mixed_power_weight 5 7 (by decide) A L D
    (degree_zero_of_vars_bound hAvars (by decide)) (degree_zero_of_vars_bound hAvars (by decide))
    (degree_zero_of_vars_bound hLvars (by decide)) (degree_zero_of_vars_bound hLvars (by decide))
    (degree_zero_of_vars_bound hDvars (by decide)) (degree_zero_of_vars_bound hDvars (by decide))
    h2 hAA hAL hAD hLL hLD hDD p e r a b u v hv

end WeightedPilz
