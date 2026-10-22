import Pilz.IntervalElimination
import Pilz.DispersedCapacity

/-! Outside the class of squares, an interval parity class has at most
`sqrt(n/2)` terms. Together with dispersed capacity this gives the refined
core-class estimate used in the paper's small-case tables. -/

noncomputable section

namespace Pilz

/-- A positive nonsquare contains at least twice the square contributed by
halving all its prime exponents. The nonzero parity vector witnesses this. -/
theorem twice_rootInteger_sq_le {a : ℕ} (ha : 0 < a) (ε : ℕ → ℕ)
    (hpar : ∀ i, a.factorization i % 2 = ε i) (hε : ε ≠ 0) :
    2 * (rootInteger a.factorization) ^ 2 ≤ a := by
  have hprime : ∀ p ∈ a.factorization.support, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have hrootpos := rootInteger_pos hprime
  have hne : a ≠ (rootInteger a.factorization) ^ 2 := by
    intro heq
    have hfac : a.factorization = 2 • halfExponent a.factorization := by
      calc
        a.factorization = ((rootInteger a.factorization) ^ 2).factorization :=
          congrArg Nat.factorization heq
        _ = 2 • halfExponent a.factorization := by
          rw [Nat.factorization_pow, rootInteger_factorization hprime]
    apply hε
    funext i
    have hi := congrArg (fun d : ℕ →₀ ℕ => d i) hfac
    simp only [two_smul, Finsupp.add_apply, halfExponent_apply] at hi
    have hpi := hpar i
    change ε i = 0
    omega
  obtain ⟨k, hk⟩ := rootInteger_sq_dvd ha
  have hk2 : 2 ≤ k := by
    by_contra hknot
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with rfl | rfl
    · simp at hk
      omega
    · simp at hk
      exact hne hk
  have hmul := Nat.mul_le_mul_left ((rootInteger a.factorization) ^ 2) hk2
  calc
    2 * (rootInteger a.factorization) ^ 2 = (rootInteger a.factorization) ^ 2 * 2 :=
      Nat.mul_comm _ _
    _ ≤ (rootInteger a.factorization) ^ 2 * k := hmul
    _ = a := hk.symm

private theorem interval_support_factorization_second {n : ℕ} {d : ℕ →₀ ℕ}
    (hd : d ∈ (interval n).support) :
    ∃ a ∈ Finset.Icc 1 n, a.factorization = d := by
  have hpos : ∀ a ∈ Finset.Icc 1 n, 0 < a :=
    fun _ ha => (Finset.mem_Icc.mp ha).1
  rw [interval_eq_polynomialOf, support_polynomialOf _ hpos] at hd
  exact Finset.mem_image.mp hd

theorem rootInteger_le_sqrt_half_of_paritySupport {n : ℕ} {ε : ℕ → ℕ}
    (hε : ε ≠ 0) {d : ℕ →₀ ℕ} (hd : d ∈ paritySupport (interval n) ε) :
    rootInteger d ≤ Nat.sqrt (n / 2) := by
  classical
  obtain ⟨hdI, hpar⟩ := Finset.mem_filter.mp hd
  obtain ⟨a, ha, rfl⟩ := interval_support_factorization_second hdI
  have htwo := twice_rootInteger_sq_le (Finset.mem_Icc.mp ha).1 ε hpar hε
  apply Nat.le_sqrt'.mpr
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  simpa only [Nat.mul_comm] using htwo.trans (Finset.mem_Icc.mp ha).2

/-- Every full parity class other than the square class has the smaller
`sqrt(n/2)` capacity. Invalid parity vectors have an empty class as usual. -/
theorem classWeight_interval_nonzero_le_sqrt_half (n : ℕ) (ε : ℕ → ℕ) (hε : ε ≠ 0) :
    classWeight (interval n) ε ≤ Nat.sqrt (n / 2) := by
  classical
  have hmaps : Set.MapsTo rootInteger (paritySupport (interval n) ε)
      (Finset.Icc 1 (Nat.sqrt (n / 2))) := by
    intro d hd
    obtain ⟨a, ha, hfac⟩ := interval_support_factorization_second
      (paritySupport_subset (interval n) ε hd)
    have hprime : ∀ p ∈ d.support, Nat.Prime p := by
      rw [← hfac]
      exact fun p hp => Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_Icc.mpr
      ⟨rootInteger_pos hprime, rootInteger_le_sqrt_half_of_paritySupport hε hd⟩
  have hcard := Finset.card_le_card_of_injOn rootInteger hmaps
    (rootInteger_injOn_interval_paritySupport n ε)
  simpa [classWeight] using hcard

theorem classWeight_core_nonzero_le_sqrt_half (n : ℕ) (ε : ℕ → ℕ) (hε : ε ≠ 0) :
    classWeight (core n) ε ≤ Nat.sqrt (n / 2) :=
  (classWeight_mono_support (core n) (interval n)
    (support_core_subset_interval n) ε).trans
    (classWeight_interval_nonzero_le_sqrt_half n ε hε)

/-- The dispersed bound specialized to the interval core. -/
theorem classWeight_core_mul_dispersed_add (n : ℕ) (D : Poly) (ε : ℕ → ℕ) :
    classWeight (core n * D) ε + ((parityIndices D).card - 1) *
      (Nat.sqrt n - Nat.sqrt (n / 2)) ≤ weight D * Nat.sqrt n :=
  classWeight_mul_dispersed_add (core n) D 0 (Nat.sqrt n) (Nat.sqrt (n / 2))
    (Nat.sqrt_le_sqrt (Nat.div_le_self n 2))
    (fun η => (classWeight_le_sigma (core n) η).trans (sigma_core_le_sqrt n))
    (classWeight_core_nonzero_le_sqrt_half n) ε

/-- At least two occupied multiplier classes save one largest-class budget. -/
theorem classWeight_core_mul_dispersed_two (n : ℕ) (D : Poly)
    (hclasses : 2 ≤ (parityIndices D).card) (ε : ℕ → ℕ) :
    classWeight (core n * D) ε ≤
      (weight D - 1) * Nat.sqrt n + Nat.sqrt (n / 2) :=
  classWeight_mul_dispersed_two (core n) D 0 (Nat.sqrt n) (Nat.sqrt (n / 2))
    (Nat.sqrt_le_sqrt (Nat.div_le_self n 2))
    (fun η => (classWeight_le_sigma (core n) η).trans (sigma_core_le_sqrt n))
    (classWeight_core_nonzero_le_sqrt_half n) hclasses ε

end Pilz
