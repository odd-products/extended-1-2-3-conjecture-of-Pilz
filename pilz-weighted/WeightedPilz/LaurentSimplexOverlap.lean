import WeightedPilz.GenericInitialOverlap
import WeightedPilz.Laurent

/-! The simplex intersection statement for arbitrary integer translations,
including translations that leave the nonnegative exponent orthant. -/

noncomputable section
namespace WeightedPilz

variable {σ : Type*} [DecidableEq σ]

theorem translated_integer_simplex_dilate_inter_card_le_one (V W : Finset σ)
    (m q : ℕ) (hm : 0 < m) (hq : 2 ≤ q) (a b : σ →₀ ℤ) :
    (((exponentSimplex V).image (fun d => a + integerExponent (scaleExponent m d))) ∩
      ((exponentSimplex W).image
        (fun d => b + integerExponent (scaleExponent (m * q) d)))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).1
  obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).2
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).1
  obtain ⟨f', hf', hfe'⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).2
  have hee : e = e' := by
    ext i
    have h := congrArg (fun d : σ →₀ ℤ => d i) hfe.symm
    have h' := congrArg (fun d : σ →₀ ℤ => d i) hfe'.symm
    simp only [Finsupp.add_apply, integerExponent_apply, scaleExponent_apply,
      Nat.cast_mul] at h h'
    have hcrossZ : (m : ℤ) * e i + ((m : ℤ) * q) * f' i =
        (m : ℤ) * e' i + ((m : ℤ) * q) * f i := by omega
    have hcross : m * e i + (m * q) * f' i = m * e' i + (m * q) * f i := by
      exact_mod_cast hcrossZ
    have hmul : m * (e i + q * f' i) = m * (e' i + q * f i) := by
      calc
        _ = m * e i + (m * q) * f' i := by ring
        _ = m * e' i + (m * q) * f i := hcross
        _ = _ := by ring
    have hc := Nat.eq_of_mul_eq_mul_left hm hmul
    have hr := congrArg (fun n : ℕ => n % q) hc
    have hei : e i < q := by
      have := exponentSimplex_coordinate_le_one V he i
      omega
    have he'i : e' i < q := by
      have := exponentSimplex_coordinate_le_one V he' i
      omega
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hei,
      Nat.mod_eq_of_lt he'i] using hr
  rw [hee]

end WeightedPilz
