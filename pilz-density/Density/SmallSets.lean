import Density.Existence
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Exact elementary densities for the small divisibility chains. -/

noncomputable section
open scoped BigOperators

namespace PilzDensity

private theorem sum_powerset_singleton (a : ℕ) (f : Finset ℕ → ℝ) :
    ∑ J ∈ ({a} : Finset ℕ).powerset, f J = f ∅ + f {a} := by
  change ∑ J ∈ (insert a (∅ : Finset ℕ)).powerset, f J = _
  rw [Finset.sum_powerset_insert (Finset.notMem_empty a)]
  simp

private theorem density_formula_all (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    density A = ∑ J ∈ A.powerset, (-2 : ℝ) ^ (J.card - 1) *
      ((minCoeff J : ℝ) / ((J.lcm id : ℕ) : ℝ)) := by
  rw [density_formula A hA]
  rw [← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset A)]
  simp [minCoeff]

@[simp] theorem minCoeff_singleton (a : ℕ) : minCoeff {a} = a := by
  simp [minCoeff]

@[simp] theorem minCoeff_pair (a b : ℕ) : minCoeff {a, b} = min a b := by
  simp [minCoeff, Finset.min'_insert]

@[simp] theorem minCoeff_triple (a b c : ℕ) :
    minCoeff {a, b, c} = min a (min b c) := by
  simp [minCoeff, Finset.min'_insert]

theorem density_singleton (a : ℕ) (ha : 0 < a) : density {a} = 1 := by
  rw [density_formula_all _ (by simpa using ha)]
  simp [sum_powerset_singleton, minCoeff, ne_of_gt ha]

theorem density_pair (a q : ℕ) (ha : 0 < a) (hq : 2 ≤ q) :
    density {a, a * q} = 2 - 2 / (q : ℝ) := by
  have hqpos : 0 < q := by omega
  have hlt : a < a * q := by nlinarith
  have hne : a ≠ a * q := ne_of_lt hlt
  have hapos : 0 < a * q := Nat.mul_pos ha hqpos
  have har : (a : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hqpos
  rw [density_formula_all _ (by simpa using And.intro ha hapos)]
  simp [Finset.sum_powerset_insert, sum_powerset_singleton, minCoeff, hne,
    min_eq_left (le_of_lt hlt), Finset.lcm_insert, lcm_eq_nat_lcm,
    Nat.lcm_eq_right (dvd_mul_right a q), ne_of_gt ha, har, hqr]
  <;> field_simp [har, hqr]
  <;> ring

theorem density_triple (u v : ℕ) (hu : 2 ≤ u) (hv : 2 ≤ v) :
    density {1, u, u * v} =
      3 - 2 / (u : ℝ) - 2 / (v : ℝ) + 2 / ((u : ℝ) * (v : ℝ)) := by
  have hup : 0 < u := by omega
  have hvp : 0 < v := by omega
  have huv : u < u * v := by nlinarith
  have h1u : 1 ≠ u := by omega
  have h1uv : 1 ≠ u * v := by nlinarith
  have huuv : u ≠ u * v := ne_of_lt huv
  have hur : (u : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hup
  have hvr : (v : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hvp
  have h1ur : (1 : ℝ) ≤ u := by exact_mod_cast (by omega : 1 ≤ u)
  rw [density_formula_all _ (by simp; omega)]
  simp [Finset.sum_powerset_insert, sum_powerset_singleton, minCoeff, h1u, h1uv,
    huuv, min_eq_left h1ur,
    min_eq_left (by omega : 1 ≤ u * v), min_eq_left (le_of_lt huv),
    Finset.lcm_insert, lcm_eq_nat_lcm, Nat.lcm_eq_right (dvd_mul_right u v),
    ne_of_gt hup, hur, hvr]
  <;> field_simp [hur, hvr]
  <;> ring

theorem density_pair_ge_three_halves (a q : ℕ) (ha : 0 < a) (hq : 4 ≤ q) :
    (3 : ℝ) / 2 ≤ density {a, a * q} := by
  rw [density_pair a q ha (by omega)]
  have hqr : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hdiv : (2 : ℝ) / q ≤ 1 / 2 := (div_le_iff₀ hqpos).mpr (by linarith)
  linarith

theorem density_triple_ge_three_halves (u v : ℕ) (hu : 2 ≤ u) (hv : 2 ≤ v) :
    (3 : ℝ) / 2 ≤ density {1, u, u * v} := by
  rw [density_triple u v hu hv]
  have hur : (2 : ℝ) ≤ u := by exact_mod_cast hu
  have hvr : (2 : ℝ) ≤ v := by exact_mod_cast hv
  have hup : (0 : ℝ) < u := by linarith
  have hvp : (0 : ℝ) < v := by linarith
  have hui : (1 : ℝ) / u ≤ 1 / 2 := (div_le_iff₀ hup).mpr (by linarith)
  have hvi : (1 : ℝ) / v ≤ 1 / 2 := (div_le_iff₀ hvp).mpr (by linarith)
  have hprod : (1 / 2 : ℝ) * (1 / 2) ≤ (1 - 1 / u) * (1 - 1 / v) :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have heq : 3 - 2 / (u : ℝ) - 2 / (v : ℝ) + 2 / ((u : ℝ) * (v : ℝ)) =
      1 + 2 * (1 - 1 / (u : ℝ)) * (1 - 1 / (v : ℝ)) := by
    field_simp [ne_of_gt hup, ne_of_gt hvp]
    <;> ring
  rw [heq]
  nlinarith

theorem density_double (a : ℕ) (ha : 0 < a) : density {a, 2 * a} = 1 := by
  convert density_pair a 2 ha (by omega) using 1 <;> norm_num [Nat.mul_comm]

theorem density_exceptional (A : Finset ℕ) (hA : Exceptional A) : density A = 1 := by
  obtain ⟨a, ha, rfl | rfl⟩ := hA
  · exact density_singleton a ha
  · exact density_double a ha

theorem density_one_three : density {1, 3} = (4 : ℝ) / 3 := by
  convert density_pair 1 3 (by omega) (by omega) using 1 <;> norm_num

theorem one_three_not_exceptional : ¬ Exceptional {1, 3} := by
  rintro ⟨a, ha, heq | heq⟩
  · have h1 : 1 ∈ ({a} : Finset ℕ) := heq ▸ (by simp : 1 ∈ ({1, 3} : Finset ℕ))
    have h3 : 3 ∈ ({a} : Finset ℕ) := heq ▸ (by simp : 3 ∈ ({1, 3} : Finset ℕ))
    simp only [Finset.mem_singleton] at h1 h3
    omega
  · have h1 : 1 ∈ ({a, 2 * a} : Finset ℕ) := heq ▸ (by simp : 1 ∈ ({1, 3} : Finset ℕ))
    have h3 : 3 ∈ ({a, 2 * a} : Finset ℕ) := heq ▸ (by simp : 3 ∈ ({1, 3} : Finset ℕ))
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h3
    omega

end PilzDensity
