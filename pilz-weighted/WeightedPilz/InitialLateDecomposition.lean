import WeightedPilz.InitialLateBases
import WeightedPilz.Initial

/-! Exact integer-label decompositions of the later initial cores. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem initial_interval_2_expansion (c : ℕ → K) :
    interval 2 c = C (c 1) + C (c 2) * X 2 := by
  have hset : Finset.Icc 1 2 = {1, 2} := by decide
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := by
    exact (by decide : Nat.Prime 2).factorization
  simp [interval, polynomialOf, hset, h2,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

theorem initial_interval_3_expansion (c : ℕ → K) :
    interval 3 c = C (c 1) + C (c 2) * X 2 + C (c 3) * X 3 := by
  have hset : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := by
    exact (by decide : Nat.Prime 2).factorization
  have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 := by
    exact (by decide : Nat.Prime 3).factorization
  simp [interval, polynomialOf, hset, h2, h3,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

theorem initial_interval_4_expansion (c : ℕ → K) :
    interval 4 c = C (c 1) + C (c 2) * X 2 + C (c 3) * X 3 + C (c 4) * X 2 ^ 2 := by
  have hset : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := by
    exact (by decide : Nat.Prime 2).factorization
  have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 := by
    exact (by decide : Nat.Prime 3).factorization
  have h4 : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 2)
  simp [interval, polynomialOf, hset, h2, h3, h4,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

theorem intervalCore_18_late_decomposition (c : ℕ → K) :
    intervalCore 18 c = lateBase 18 c + interval 3 (fun a => c (5 * a)) * X 5 +
      interval 2 (fun a => c (7 * a)) * X 7 := by
  have hset : Finset.Icc 1 18 \ intervalFreshPrimes 18 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18} := by decide
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := by
    exact (by decide : Nat.Prime 2).factorization
  have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 := by
    exact (by decide : Nat.Prime 3).factorization
  have h4 : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 2)
  have h5 : (5 : ℕ).factorization = Finsupp.single 5 1 := by
    exact (by decide : Nat.Prime 5).factorization
  have h6 : (6 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 1 := by
    change (2 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h3]
  have h7 : (7 : ℕ).factorization = Finsupp.single 7 1 := by
    exact (by decide : Nat.Prime 7).factorization
  have h8 : (8 : ℕ).factorization = Finsupp.single 2 3 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 3)
  have h9 : (9 : ℕ).factorization = Finsupp.single 3 2 := by
    simpa using (by decide : Nat.Prime 3).factorization_pow (k := 2)
  have h10 : (10 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 5 1 := by
    change (2 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h5]
  have h12 : (12 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 3 1 := by
    change (4 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h4, h3]
  have h14 : (14 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 7 1 := by
    change (2 * 7 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h7]
  have h15 : (15 : ℕ).factorization = Finsupp.single 3 1 + Finsupp.single 5 1 := by
    change (3 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h3, h5]
  have h16 : (16 : ℕ).factorization = Finsupp.single 2 4 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 4)
  have h18 : (18 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 2 := by
    change (2 * 9 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h9]
  rw [lateBase_expansion, initial_interval_3_expansion,
    initial_interval_2_expansion]
  simp [intervalCore, polynomialOf, hset, h2, h3, h4, h5, h6, h7, h8, h9, h10, h12, h14, h15, h16, h18,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

theorem intervalCore_20_late_decomposition (c : ℕ → K) :
    intervalCore 20 c = lateBase 18 c + interval 4 (fun a => c (5 * a)) * X 5 +
      interval 2 (fun a => c (7 * a)) * X 7 := by
  have hset : Finset.Icc 1 20 \ intervalFreshPrimes 20 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20} := by decide
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := by
    exact (by decide : Nat.Prime 2).factorization
  have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 := by
    exact (by decide : Nat.Prime 3).factorization
  have h4 : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 2)
  have h5 : (5 : ℕ).factorization = Finsupp.single 5 1 := by
    exact (by decide : Nat.Prime 5).factorization
  have h6 : (6 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 1 := by
    change (2 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h3]
  have h7 : (7 : ℕ).factorization = Finsupp.single 7 1 := by
    exact (by decide : Nat.Prime 7).factorization
  have h8 : (8 : ℕ).factorization = Finsupp.single 2 3 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 3)
  have h9 : (9 : ℕ).factorization = Finsupp.single 3 2 := by
    simpa using (by decide : Nat.Prime 3).factorization_pow (k := 2)
  have h10 : (10 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 5 1 := by
    change (2 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h5]
  have h12 : (12 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 3 1 := by
    change (4 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h4, h3]
  have h14 : (14 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 7 1 := by
    change (2 * 7 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h7]
  have h15 : (15 : ℕ).factorization = Finsupp.single 3 1 + Finsupp.single 5 1 := by
    change (3 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h3, h5]
  have h16 : (16 : ℕ).factorization = Finsupp.single 2 4 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 4)
  have h18 : (18 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 2 := by
    change (2 * 9 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h9]
  have h20 : (20 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 5 1 := by
    change (4 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h4, h5]
  rw [lateBase_expansion, initial_interval_4_expansion,
    initial_interval_2_expansion]
  simp [intervalCore, polynomialOf, hset, h2, h3, h4, h5, h6, h7, h8, h9, h10, h12, h14, h15, h16, h18, h20,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

theorem intervalCore_21_late_decomposition (c : ℕ → K) :
    intervalCore 21 c = lateBase 18 c + interval 4 (fun a => c (5 * a)) * X 5 +
      interval 3 (fun a => c (7 * a)) * X 7 := by
  have hset : Finset.Icc 1 21 \ intervalFreshPrimes 21 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21} := by decide
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := by
    exact (by decide : Nat.Prime 2).factorization
  have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 := by
    exact (by decide : Nat.Prime 3).factorization
  have h4 : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 2)
  have h5 : (5 : ℕ).factorization = Finsupp.single 5 1 := by
    exact (by decide : Nat.Prime 5).factorization
  have h6 : (6 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 1 := by
    change (2 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h3]
  have h7 : (7 : ℕ).factorization = Finsupp.single 7 1 := by
    exact (by decide : Nat.Prime 7).factorization
  have h8 : (8 : ℕ).factorization = Finsupp.single 2 3 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 3)
  have h9 : (9 : ℕ).factorization = Finsupp.single 3 2 := by
    simpa using (by decide : Nat.Prime 3).factorization_pow (k := 2)
  have h10 : (10 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 5 1 := by
    change (2 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h5]
  have h12 : (12 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 3 1 := by
    change (4 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h4, h3]
  have h14 : (14 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 7 1 := by
    change (2 * 7 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h7]
  have h15 : (15 : ℕ).factorization = Finsupp.single 3 1 + Finsupp.single 5 1 := by
    change (3 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h3, h5]
  have h16 : (16 : ℕ).factorization = Finsupp.single 2 4 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 4)
  have h18 : (18 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 2 := by
    change (2 * 9 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h9]
  have h20 : (20 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 5 1 := by
    change (4 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h4, h5]
  have h21 : (21 : ℕ).factorization = Finsupp.single 3 1 + Finsupp.single 7 1 := by
    change (3 * 7 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h3, h7]
  rw [lateBase_expansion, initial_interval_4_expansion,
    initial_interval_3_expansion]
  simp [intervalCore, polynomialOf, hset, h2, h3, h4, h5, h6, h7, h8, h9, h10, h12, h14, h15, h16, h18, h20, h21,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

theorem intervalCore_22_late_decomposition (c : ℕ → K) :
    intervalCore 22 c = lateBase 18 c + interval 4 (fun a => c (5 * a)) * X 5 +
      interval 3 (fun a => c (7 * a)) * X 7 + interval 2 (fun a => c (11 * a)) * X 11 := by
  have hset : Finset.Icc 1 22 \ intervalFreshPrimes 22 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22} := by decide
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := by
    exact (by decide : Nat.Prime 2).factorization
  have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 := by
    exact (by decide : Nat.Prime 3).factorization
  have h4 : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 2)
  have h5 : (5 : ℕ).factorization = Finsupp.single 5 1 := by
    exact (by decide : Nat.Prime 5).factorization
  have h6 : (6 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 1 := by
    change (2 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h3]
  have h7 : (7 : ℕ).factorization = Finsupp.single 7 1 := by
    exact (by decide : Nat.Prime 7).factorization
  have h8 : (8 : ℕ).factorization = Finsupp.single 2 3 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 3)
  have h9 : (9 : ℕ).factorization = Finsupp.single 3 2 := by
    simpa using (by decide : Nat.Prime 3).factorization_pow (k := 2)
  have h10 : (10 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 5 1 := by
    change (2 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h5]
  have h11 : (11 : ℕ).factorization = Finsupp.single 11 1 := by
    exact (by decide : Nat.Prime 11).factorization
  have h12 : (12 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 3 1 := by
    change (4 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h4, h3]
  have h14 : (14 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 7 1 := by
    change (2 * 7 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h7]
  have h15 : (15 : ℕ).factorization = Finsupp.single 3 1 + Finsupp.single 5 1 := by
    change (3 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h3, h5]
  have h16 : (16 : ℕ).factorization = Finsupp.single 2 4 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 4)
  have h18 : (18 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 2 := by
    change (2 * 9 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h9]
  have h20 : (20 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 5 1 := by
    change (4 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h4, h5]
  have h21 : (21 : ℕ).factorization = Finsupp.single 3 1 + Finsupp.single 7 1 := by
    change (3 * 7 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h3, h7]
  have h22 : (22 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 11 1 := by
    change (2 * 11 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h11]
  rw [lateBase_expansion, initial_interval_4_expansion,
    initial_interval_3_expansion, initial_interval_2_expansion]
  simp [intervalCore, polynomialOf, hset, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14, h15, h16, h18, h20, h21, h22,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

theorem intervalCore_24_late_decomposition (c : ℕ → K) :
    intervalCore 24 c = lateBase 24 c + interval 4 (fun a => c (5 * a)) * X 5 +
      interval 3 (fun a => c (7 * a)) * X 7 + interval 2 (fun a => c (11 * a)) * X 11 := by
  have hset : Finset.Icc 1 24 \ intervalFreshPrimes 24 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24} := by decide
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := by
    exact (by decide : Nat.Prime 2).factorization
  have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 := by
    exact (by decide : Nat.Prime 3).factorization
  have h4 : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 2)
  have h5 : (5 : ℕ).factorization = Finsupp.single 5 1 := by
    exact (by decide : Nat.Prime 5).factorization
  have h6 : (6 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 1 := by
    change (2 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h3]
  have h7 : (7 : ℕ).factorization = Finsupp.single 7 1 := by
    exact (by decide : Nat.Prime 7).factorization
  have h8 : (8 : ℕ).factorization = Finsupp.single 2 3 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 3)
  have h9 : (9 : ℕ).factorization = Finsupp.single 3 2 := by
    simpa using (by decide : Nat.Prime 3).factorization_pow (k := 2)
  have h10 : (10 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 5 1 := by
    change (2 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h5]
  have h11 : (11 : ℕ).factorization = Finsupp.single 11 1 := by
    exact (by decide : Nat.Prime 11).factorization
  have h12 : (12 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 3 1 := by
    change (4 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h4, h3]
  have h14 : (14 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 7 1 := by
    change (2 * 7 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h7]
  have h15 : (15 : ℕ).factorization = Finsupp.single 3 1 + Finsupp.single 5 1 := by
    change (3 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h3, h5]
  have h16 : (16 : ℕ).factorization = Finsupp.single 2 4 := by
    simpa using (by decide : Nat.Prime 2).factorization_pow (k := 4)
  have h18 : (18 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 2 := by
    change (2 * 9 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h9]
  have h20 : (20 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 5 1 := by
    change (4 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h4, h5]
  have h21 : (21 : ℕ).factorization = Finsupp.single 3 1 + Finsupp.single 7 1 := by
    change (3 * 7 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h3, h7]
  have h22 : (22 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 11 1 := by
    change (2 * 11 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h11]
  have h24 : (24 : ℕ).factorization = Finsupp.single 2 3 + Finsupp.single 3 1 := by
    change (8 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h8, h3]
  rw [lateBase_expansion, initial_interval_4_expansion,
    initial_interval_3_expansion, initial_interval_2_expansion]
  simp [intervalCore, polynomialOf, hset, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14, h15, h16, h18, h20, h21, h22, h24,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

end WeightedPilz

