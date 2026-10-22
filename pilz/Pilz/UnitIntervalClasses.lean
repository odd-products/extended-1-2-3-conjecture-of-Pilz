import Pilz.UnitClasses
import Pilz.IntervalSecondClass
import Mathlib.Data.Nat.Squarefree

/-! Squarefree integers in `(n/4,n]` give unit interval classes. The
normal-form unit-class budget is specialized here, with kernel-checked
finite counts covering every length used by the small-case proof. -/

noncomputable section

namespace Pilz

open MvPolynomial

/-- A bounded-divisor formulation whose finite certificates reduce entirely
inside the kernel. -/
def squarefreeByDivisors (a : ℕ) : Prop :=
  0 < a ∧ ∀ k ∈ Finset.Icc 2 a, ¬ k * k ∣ a

instance (a : ℕ) : Decidable (squarefreeByDivisors a) :=
  inferInstanceAs (Decidable (0 < a ∧ ∀ k ∈ Finset.Icc 2 a, ¬ k * k ∣ a))

theorem squarefreeByDivisors_iff (a : ℕ) : squarefreeByDivisors a ↔ Squarefree a := by
  constructor
  · rintro ⟨hapos, hdiv⟩
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hpp
    have hpdiv : p ∣ a := dvd_trans (dvd_mul_right p p) hpp
    exact hdiv p (Finset.mem_Icc.mpr ⟨hp.two_le, Nat.le_of_dvd hapos hpdiv⟩) hpp
  · intro hsq
    refine ⟨Nat.pos_of_ne_zero hsq.ne_zero, ?_⟩
    intro k hk hdiv
    have hkone : k = 1 := Nat.isUnit_iff.mp (hsq k hdiv)
    have hk2 := (Finset.mem_Icc.mp hk).1
    omega

def squarefreeUpperNumbers (n : ℕ) : Finset ℕ :=
  (Finset.Icc (n / 4 + 1) n).filter squarefreeByDivisors

def coreUnitNumbers (n : ℕ) : Finset ℕ := squarefreeUpperNumbers n \ freshPrimes n

theorem mem_squarefreeUpperNumbers (n a : ℕ) :
    a ∈ squarefreeUpperNumbers n ↔ n / 4 < a ∧ a ≤ n ∧ Squarefree a := by
  simp only [squarefreeUpperNumbers, Finset.mem_filter, Finset.mem_Icc]
  rw [squarefreeByDivisors_iff]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hsq⟩
    exact ⟨by omega, hhi, hsq⟩
  · rintro ⟨hlo, hhi, hsq⟩
    exact ⟨⟨by omega, hhi⟩, hsq⟩

theorem freshPrimes_subset_squarefreeUpperNumbers (n : ℕ) :
    freshPrimes n ⊆ squarefreeUpperNumbers n := by
  intro p hp
  obtain ⟨hpp, hpn, hhalf⟩ := (mem_freshPrimes_iff n p).mp hp
  apply (mem_squarefreeUpperNumbers n p).mpr
  have hquarter : n / 4 ≤ n / 2 := Nat.div_le_div_left (by decide : 2 ≤ 4) (by decide)
  exact ⟨hquarter.trans_lt hhalf, hpn, hpp.squarefree⟩

theorem card_coreUnitNumbers_add_fresh (n : ℕ) :
    (coreUnitNumbers n).card + (freshPrimes n).card = (squarefreeUpperNumbers n).card :=
  Finset.card_sdiff_add_card_eq_card (freshPrimes_subset_squarefreeUpperNumbers n)

private theorem interval_support_unit_factorization {n : ℕ} {d : ℕ →₀ ℕ}
    (hd : d ∈ (interval n).support) :
    ∃ a ∈ Finset.Icc 1 n, a.factorization = d := by
  have hpos : ∀ a ∈ Finset.Icc 1 n, 0 < a := fun _ ha => (Finset.mem_Icc.mp ha).1
  rw [interval_eq_polynomialOf, support_polynomialOf _ hpos] at hd
  exact Finset.mem_image.mp hd

/-- A squarefree number above `n/4` is the only interval integer in its
full exponent-parity class. -/
theorem eq_of_squarefree_upper_parity {n a b : ℕ}
    (ha : a ∈ squarefreeUpperNumbers n) (hb : b ∈ Finset.Icc 1 n)
    (hpar : ∀ i, b.factorization i % 2 = a.factorization i) : b = a := by
  obtain ⟨haQuarter, _han, haSq⟩ := (mem_squarefreeUpperNumbers n a).mp ha
  have hapos : 0 < a := by omega
  have hbpos : 0 < b := (Finset.mem_Icc.mp hb).1
  have hprime : ∀ p ∈ b.factorization.support, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have hrpos := rootInteger_pos hprime
  have hfac := exponent_parity_half b.factorization a.factorization hpar
  have hprod : a * (rootInteger b.factorization) ^ 2 = b := by
    apply Nat.factorization_inj
      (mul_ne_zero (ne_of_gt hapos) (pow_ne_zero _ (ne_of_gt hrpos))) (ne_of_gt hbpos)
    rw [Nat.factorization_mul (ne_of_gt hapos) (pow_ne_zero _ (ne_of_gt hrpos)),
      Nat.factorization_pow, rootInteger_factorization hprime]
    exact hfac
  have hrone : rootInteger b.factorization = 1 := by
    by_contra hne
    have hr2 : 2 ≤ rootInteger b.factorization := by omega
    have hrsq : 4 ≤ (rootInteger b.factorization) ^ 2 := by nlinarith
    have hmul := Nat.mul_le_mul_left a hrsq
    rw [hprod] at hmul
    have hbn := (Finset.mem_Icc.mp hb).2
    omega
  simpa [hrone] using hprod.symm

/-- Removing fresh primes does not disturb any remaining squarefree upper
unit class. -/
theorem parityClass_core_unit {n a : ℕ} (ha : a ∈ coreUnitNumbers n) :
    parityClass (core n) a.factorization = monomial a.factorization 1 := by
  classical
  obtain ⟨haUpper, haFresh⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨haQuarter, han, haSq⟩ := (mem_squarefreeUpperNumbers n a).mp haUpper
  have hapos : 0 < a := by omega
  have habits : ∀ i, a.factorization i < 2 := fun i => by
    have h := haSq.natFactorization_le_one i
    omega
  have hsupport : ∀ d ∈ (parityClass (core n) a.factorization).support,
      d = a.factorization := by
    intro d hd
    rw [support_parityClass] at hd
    obtain ⟨hdC, hpar⟩ := Finset.mem_filter.mp hd
    obtain ⟨b, hb, hbd⟩ := interval_support_unit_factorization
      (support_core_subset_interval n hdC)
    rw [← hbd] at hpar
    have hba := eq_of_squarefree_upper_parity haUpper hb hpar
    exact hbd.symm.trans (congrArg Nat.factorization hba)
  apply MvPolynomial.ext
  intro d
  by_cases hd : d = a.factorization
  · subst d
    rw [coeff_parityClass, if_pos (fun i => Nat.mod_eq_of_lt (habits i))]
    have hpos : ∀ b ∈ Finset.Icc 1 n \ freshPrimes n, 0 < b :=
      fun _ hb => (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hb).1).1
    rw [core, coeff_polynomialOf _ hpos hapos,
      if_pos (Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hapos, han⟩, haFresh⟩)]
    simp
  · have hzero : MvPolynomial.coeff d (parityClass (core n) a.factorization) = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      exact fun hmem => hd (hsupport d hmem)
    rw [hzero]
    simp [MvPolynomial.coeff_monomial, Ne.symm hd]

/-- The paper's `m ≥ u Q1(n)` inequality, for any positive interval length. -/
theorem normalForm_interval_single_class (n : ℕ) (hn : 0 < n)
    (hfresh : (freshPrimes n).Nonempty)
    (nf : NormalFormData (intervalFreshData n hn hfresh) n)
    (hclasses : (parityIndices nf.D).card = 1) :
    (squarefreeUpperNumbers n).card * weight nf.D ≤ weight nf.G := by
  classical
  let S := intervalFreshData n hn hfresh
  have hN : n ≤ weight S.C + S.vars.card := by
    rw [← S.weight_F, intervalFreshData_F n hn hfresh, weight_interval]
  let A := (coreUnitNumbers n).image Nat.factorization
  have hbits : ∀ μ ∈ A, ∀ i, μ i < 2 := by
    intro μ hμ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hμ
    have haSq := ((mem_squarefreeUpperNumbers n a).mp (Finset.mem_sdiff.mp ha).1).2.2
    intro i
    have h := haSq.natFactorization_le_one i
    omega
  have hunit : ∀ μ ∈ A, parityClass S.C μ = monomial μ 1 := by
    intro μ hμ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hμ
    exact parityClass_core_unit ha
  have hAcard : A.card = (coreUnitNumbers n).card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb heq
    have hapos : 0 < a := by
      have h := ((mem_squarefreeUpperNumbers n a).mp (Finset.mem_sdiff.mp ha).1).1
      omega
    have hbpos : 0 < b := by
      have h := ((mem_squarefreeUpperNumbers n b).mp (Finset.mem_sdiff.mp hb).1).1
      omega
    exact Nat.factorization_inj (ne_of_gt hapos) (ne_of_gt hbpos) heq
  have h := normalForm_unit_classes S n nf hN A hbits hunit hclasses
  change (A.card + (freshPrimes n).card) * weight nf.D ≤ weight nf.G at h
  rw [hAcard, card_coreUnitNumbers_add_fresh n] at h
  exact h

set_option maxRecDepth 100000 in
private theorem squarefree_upper_count_certificate : ∀ n : Fin 67,
    0 < n.val → n.val < 4 * (squarefreeUpperNumbers n.val).card := by decide

theorem squarefree_upper_count_small {n : ℕ} (hn : 0 < n) (hsmall : n ≤ 66) :
    n < 4 * (squarefreeUpperNumbers n).card :=
  squarefree_upper_count_certificate ⟨n, by omega⟩ hn

set_option maxRecDepth 100000 in
private theorem squarefree_upper_ten_certificate : ∀ n : Fin 30,
    26 ≤ n.val → 10 ≤ (squarefreeUpperNumbers n.val).card := by decide

theorem squarefree_upper_count_ten {n : ℕ} (hlo : 26 ≤ n) (hhi : n ≤ 29) :
    10 ≤ (squarefreeUpperNumbers n).card :=
  squarefree_upper_ten_certificate ⟨n, by omega⟩ hlo

theorem normalForm_interval_at_least_two_classes (n : ℕ) (hn : 0 < n)
    (hfresh : (freshPrimes n).Nonempty)
    (nf : NormalFormData (intervalFreshData n hn hfresh) n)
    (hsmall : n ≤ 66) (hu : 4 ≤ weight nf.D) :
    2 ≤ (parityIndices nf.D).card := by
  classical
  obtain ⟨η, hη, _⟩ := exists_nonzero_parityClass nf.D nf.D_ne_zero
  have hpos : 0 < (parityIndices nf.D).card := Finset.card_pos.mpr ⟨η, hη⟩
  by_contra hnot
  have hone : (parityIndices nf.D).card = 1 := by omega
  have hunit := normalForm_interval_single_class n hn hfresh nf hone
  have hcount := squarefree_upper_count_small hn hsmall
  have hmul := Nat.mul_le_mul_left (squarefreeUpperNumbers n).card hu
  have hshort := nf.extremal.1.2.2
  omega

theorem normalForm_interval_at_least_two_classes_26_29 (n : ℕ) (hn : 0 < n)
    (hfresh : (freshPrimes n).Nonempty)
    (nf : NormalFormData (intervalFreshData n hn hfresh) n)
    (hlo : 26 ≤ n) (hhi : n ≤ 29) (hu : 3 ≤ weight nf.D) :
    2 ≤ (parityIndices nf.D).card := by
  classical
  obtain ⟨η, hη, _⟩ := exists_nonzero_parityClass nf.D nf.D_ne_zero
  have hpos : 0 < (parityIndices nf.D).card := Finset.card_pos.mpr ⟨η, hη⟩
  by_contra hnot
  have hone : (parityIndices nf.D).card = 1 := by omega
  have hunit := normalForm_interval_single_class n hn hfresh nf hone
  have hcount := squarefree_upper_count_ten hlo hhi
  have hmul := Nat.mul_le_mul hcount hu
  have hshort := nf.extremal.1.2.2
  omega

end Pilz
