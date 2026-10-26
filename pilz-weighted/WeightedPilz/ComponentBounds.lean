import WeightedPilz.Components
import WeightedPilz.Endpoints
import Pilz.ComponentProfile

/-!
# Active-prime profiles for arbitrary nonzero weights

The arithmetic sets are reused, while every polynomial and support argument is
over the arbitrary field `K`. Each smooth component can have its own weights.
-/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators
open Pilz (primesUpTo primeCount smoothNumbers Smooth mem_smoothNumbers
  mem_primesUpTo card_primesUpTo primesUpTo_prime primeCount_mono
  roughNumbers roughCount roughIntervalCount mem_roughNumbers)

variable {K : Type*} [Field K]

def VariableOccurs (D : Poly K) (p : ℕ) : Prop := ∃ d ∈ D.support, 0 < d p

def Normalized (D : Poly K) : Prop := ∀ p, ∃ d ∈ D.support, d p = 0

def LargestPrime (D : Poly K) (q : ℕ) : Prop :=
  Nat.Prime q ∧ VariableOccurs D q ∧
    ∀ p, VariableOccurs D p → Nat.Prime p ∧ p ≤ q

theorem smoothNumbers_primesUpTo_eq_Icc {j q : ℕ} (hjq : j ≤ q) :
    smoothNumbers (primesUpTo q) j = Finset.Icc 1 j := by
  apply Finset.filter_eq_self.mpr
  intro a ha p hp
  exact (mem_primesUpTo q p).mpr
    ⟨(Nat.mem_primeFactors.mp hp).1,
      (Nat.le_of_mem_primeFactors hp).trans ((Finset.mem_Icc.mp ha).2.trans hjq)⟩

theorem smoothInterval_primesUpTo_eq_interval {j q : ℕ} (hjq : j ≤ q) (c : ℕ → K) :
    smoothInterval (primesUpTo q) j c = interval j c := by
  rw [smoothInterval, smoothNumbers_primesUpTo_eq_Icc hjq]
  rfl

theorem one_mem_smoothNumbers (T : Finset ℕ) {j : ℕ} (hj : 1 ≤ j) :
    1 ∈ smoothNumbers T j :=
  (mem_smoothNumbers T j 1).mpr ⟨le_rfl, hj, Pilz.smooth_one T⟩

theorem prime_mem_smoothNumbers (T : Finset ℕ) {j p : ℕ}
    (hp : Nat.Prime p) (hpT : p ∈ T) (hpj : p ≤ j) :
    p ∈ smoothNumbers T j := by
  have hsmooth : Smooth T p := by
    rw [Smooth, hp.factorization, Finsupp.support_single_ne_zero _ (show (1 : ℕ) ≠ 0 by decide)]
    exact Finset.singleton_subset_iff.mpr hpT
  exact (mem_smoothNumbers T j p).mpr ⟨hp.pos, hpj, hsmooth⟩

theorem smoothInterval_coeff_zero (T : Finset ℕ) (j : ℕ) (c : ℕ → K) (hj : 1 ≤ j) :
    MvPolynomial.coeff 0 (smoothInterval T j c) = c 1 := by
  have hpos : ∀ a ∈ smoothNumbers T j, 0 < a :=
    fun a ha => ((mem_smoothNumbers T j a).mp ha).1
  have hc := coeff_polynomialOf (smoothNumbers T j) c hpos (a := 1) (by decide)
  rw [if_pos (one_mem_smoothNumbers T hj)] at hc
  simpa only [Nat.factorization_one, smoothInterval] using hc

theorem smoothInterval_coeff_prime (T : Finset ℕ) (j p : ℕ) (c : ℕ → K)
    (hp : Nat.Prime p) (hpT : p ∈ T) (hpj : p ≤ j) :
    MvPolynomial.coeff (Finsupp.single p 1) (smoothInterval T j c) = c p := by
  have hpos : ∀ a ∈ smoothNumbers T j, 0 < a :=
    fun a ha => ((mem_smoothNumbers T j a).mp ha).1
  have hc := coeff_polynomialOf (smoothNumbers T j) c hpos hp.pos
  rw [if_pos (prime_mem_smoothNumbers T hp hpT hpj)] at hc
  simpa only [hp.factorization, smoothInterval] using hc

theorem weight_two_coordinate_slices (p : ℕ) (P : Poly K) (i j : ℕ) (hij : i ≠ j) :
    weight ((coordinateEquiv p P).coeff i) +
      weight ((coordinateEquiv p P).coeff j) ≤ weight P := by
  have h := weight_two_slices (renameEquiv K (Equiv.optionSubtypeNe p).symm P) i j hij
  rw [weight_renameEquiv] at h
  exact h

private theorem coordinate_coeff_ne_zero_of_mem (q : ℕ) (D : Poly K)
    (d : ℕ →₀ ℕ) (hd : d ∈ D.support) :
    (coordinateEquiv q D).coeff (d q) ≠ 0 := by
  intro hz
  have h := coordinate_coeff_coeff q D d
  rw [hz, MvPolynomial.coeff_zero] at h
  exact (MvPolynomial.mem_support_iff.mp hd) h.symm

theorem independent_two_slice_expansion (P D : Poly K) (q k : ℕ)
    (hP : ∀ d ∈ P.support, d q = 0)
    (hzero : ∃ d ∈ D.support, d q = 0)
    (hpos : ∃ d ∈ D.support, 0 < d q)
    (hbudget : k ≤ distance ((coordinateEquiv q P).coeff 0)) :
    2 * k ≤ weight (P * D) := by
  let A := (coordinateEquiv q P).coeff 0
  have hdeg : P.degreeOf q = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [degreeOf_le_iff]
    intro d hd
    exact (hP d hd).le
  have hconst : coordinateEquiv q P = Polynomial.C A := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hdeg]
  obtain ⟨d0, hd0, hd0q⟩ := hzero
  have hD0 := coordinate_coeff_ne_zero_of_mem q D d0 hd0
  rw [hd0q] at hD0
  obtain ⟨d, hd, hdp⟩ := hpos
  have hDb := coordinate_coeff_ne_zero_of_mem q D d hd
  have htwo := weight_two_coordinate_slices q (P * D) 0 (d q) (by omega)
  rw [map_mul, hconst, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul] at htwo
  have hzeroBudget := hbudget.trans (distance_le_weight_mul A _ hD0)
  have hposBudget := hbudget.trans (distance_le_weight_mul A _ hDb)
  omega

theorem component_profile_one (q : ℕ) (c : ℕ → K) (D : Poly K) (hc : c 1 ≠ 0) :
    weight (smoothInterval (primesUpTo q) 1 c * D) = weight D :=
  weight_smoothInterval_one_mul _ c D hc

/-- The active-prime branch uses only the nonzero constant and prime terms. -/
theorem component_profile_after (q j : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : ∀ a ∈ smoothNumbers (primesUpTo q) j, c a ≠ 0)
    (hq : Nat.Prime q) (hqj : q ≤ j) (hD : D ≠ 0) :
    1 + primeCount q ≤ weight (smoothInterval (primesUpTo q) j c * D) := by
  have hj : 1 ≤ j := hq.pos.trans_le hqj
  have hzero : MvPolynomial.coeff 0 (smoothInterval (primesUpTo q) j c) ≠ 0 := by
    rw [smoothInterval_coeff_zero _ _ _ hj]
    exact hc 1 (one_mem_smoothNumbers _ hj)
  have hpure : ∀ p ∈ primesUpTo q, ∃ k : ℕ, 0 < k ∧
      MvPolynomial.coeff (Finsupp.single p k) (smoothInterval (primesUpTo q) j c) ≠ 0 := by
    intro p hp
    obtain ⟨hpp, hpq⟩ := (mem_primesUpTo q p).mp hp
    refine ⟨1, by decide, ?_⟩
    rw [smoothInterval_coeff_prime _ _ _ c hpp hp (hpq.trans hqj)]
    exact hc p (prime_mem_smoothNumbers _ hpp hp (hpq.trans hqj))
  have h := pure_endpoints_weight_mul (primesUpTo q)
    (smoothInterval (primesUpTo q) j c) D hzero hpure hD
  simpa only [card_primesUpTo, Nat.add_comm] using h

/-- Before activation, two multiplier slices each pay the endpoint distance. -/
theorem component_profile_before (q j : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : ∀ a ∈ smoothNumbers (primesUpTo q) j, c a ≠ 0)
    (hj : 2 ≤ j) (hjq : j < q) (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    2 * (1 + primeCount j) ≤ weight (smoothInterval (primesUpTo q) j c * D) := by
  classical
  have hci : NonzeroWeights j c := by
    simpa only [smoothNumbers_primesUpTo_eq_Icc (Nat.le_of_lt hjq)] using hc
  rw [smoothInterval_primesUpTo_eq_interval (Nat.le_of_lt hjq)]
  let U := primesUpTo j
  let B := U.subtype (fun p => p ≠ q)
  let A := (coordinateEquiv q (interval j c)).coeff 0
  have hqU : q ∉ U := by
    intro hq
    have hle := ((mem_primesUpTo j q).mp hq).2
    omega
  have hfilter : U.filter (fun p => p ≠ q) = U := by
    apply Finset.filter_eq_self.mpr
    intro p hp hpq
    exact hqU (hpq ▸ hp)
  have hBcard : B.card = primeCount j := by
    rw [Finset.card_subtype, hfilter]
    rfl
  have hPzero : MvPolynomial.coeff 0 (interval j c) = c 1 := by
    have h := smoothInterval_coeff_zero U j c (by omega)
    rwa [smoothInterval_primesUpTo_eq_interval (q := j) le_rfl] at h
  have hA0 : MvPolynomial.coeff 0 A ≠ 0 := by
    change MvPolynomial.coeff 0 ((coordinateEquiv q (interval j c)).coeff 0) ≠ 0
    rw [coordinate_coeff_zero, hPzero]
    exact hci 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hApure : ∀ p ∈ B, ∃ k : ℕ, 0 < k ∧ MvPolynomial.coeff (Finsupp.single p k) A ≠ 0 := by
    intro p hp
    have hpU : p.val ∈ U := Finset.mem_subtype.mp hp
    obtain ⟨hpp, hpj⟩ := (mem_primesUpTo j p.val).mp hpU
    refine ⟨1, by decide, ?_⟩
    change MvPolynomial.coeff (Finsupp.single p 1) ((coordinateEquiv q (interval j c)).coeff 0) ≠ 0
    rw [coordinate_coeff_pure_of_ne q p.val p.property]
    have hcp := smoothInterval_coeff_prime U j p.val c hpp hpU hpj
    rw [smoothInterval_primesUpTo_eq_interval (q := j) le_rfl] at hcp
    rw [hcp]
    exact hci p.val (Finset.mem_Icc.mpr ⟨hpp.pos, hpj⟩)
  have hbudget : 1 + primeCount j ≤ distance A := by
    have h := pure_endpoints_distance B A hA0 hApure
    simpa only [hBcard, Nat.add_comm] using h
  have hPvars : (interval j c).vars ⊆ U := by
    have h := smoothInterval_vars_subset U j c
    rwa [smoothInterval_primesUpTo_eq_interval (q := j) le_rfl] at h
  have hPind : ∀ d ∈ (interval j c).support, d q = 0 := by
    intro d hd
    exact MvPolynomial.mem_support_notMem_vars_zero hd (fun hq => hqU (hPvars hq))
  exact independent_two_slice_expansion (interval j c) D q (1 + primeCount j)
    hPind (hnorm q) hlargest.2.1 hbudget

theorem largestPrime_vars_subset (D : Poly K) (q : ℕ) (hlargest : LargestPrime D q) :
    D.vars ⊆ primesUpTo q := by
  intro p hp
  obtain ⟨d, hd, hdp⟩ := (MvPolynomial.mem_vars p).mp hp
  have hocc : VariableOccurs D p :=
    ⟨d, hd, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hdp)⟩
  exact (mem_primesUpTo q p).mpr (hlargest.2.2 p hocc)

theorem component_profile_four (q j : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : ∀ a ∈ smoothNumbers (primesUpTo q) j, c a ≠ 0)
    (hq : 5 ≤ q) (hj : 2 ≤ j) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    4 ≤ weight (smoothInterval (primesUpTo q) j c * D) := by
  by_cases hjq : j < q
  · have h := component_profile_before q j c D hc hj hjq hnorm hlargest
    have hπ := primeCount_mono hj
    have hπ2 : primeCount 2 = 1 := by decide
    omega
  · have h := component_profile_after q j c D hc hlargest.1 (Nat.le_of_not_gt hjq) hD
    have hπ := primeCount_mono hq
    have hπ5 : primeCount 5 = 3 := by decide
    omega

theorem component_profile_eight (q j : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : ∀ a ∈ smoothNumbers (primesUpTo q) j, c a ≠ 0)
    (hq : 17 ≤ q) (hj : 2 ≤ j) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    4 + (if 3 ≤ j then 2 else 0) + (if 5 ≤ j then 2 else 0) ≤
      weight (smoothInterval (primesUpTo q) j c * D) := by
  by_cases hjq : j < q
  · have h := component_profile_before q j c D hc hj hjq hnorm hlargest
    by_cases hj5 : 5 ≤ j
    · have hπ := primeCount_mono hj5
      have hπ5 : primeCount 5 = 3 := by decide
      have hj3 : 3 ≤ j := by omega
      simp only [if_pos hj3, if_pos hj5]
      omega
    · by_cases hj3 : 3 ≤ j
      · have hπ := primeCount_mono hj3
        have hπ3 : primeCount 3 = 2 := by decide
        simp only [if_pos hj3, if_neg hj5]
        omega
      · have hπ := primeCount_mono hj
        have hπ2 : primeCount 2 = 1 := by decide
        simp only [if_neg hj3, if_neg hj5]
        omega
  · have h := component_profile_after q j c D hc hlargest.1 (Nat.le_of_not_gt hjq) hD
    have hπ := primeCount_mono hq
    have hπ17 : primeCount 17 = 7 := by decide
    have hcost : 4 + (if 3 ≤ j then 2 else 0) + (if 5 ≤ j then 2 else 0) ≤ 8 := by
      by_cases h3 : 3 ≤ j <;> by_cases h5 : 5 ≤ j <;> simp [h3, h5]
    omega

private theorem sum_indicator_const (R : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    (c : ℕ) : (∑ b ∈ R, if p b then c else 0) = c * (R.filter p).card := by
  rw [← Finset.sum_filter]
  simp [Nat.mul_comm]

private def profileFourCost (u j : ℕ) : ℕ :=
  (if j = 1 then u else 0) + (if 2 ≤ j then 4 else 0)

private def profileEightCost (u j : ℕ) : ℕ :=
  (if j = 1 then u else 0) + (if 2 ≤ j then 4 else 0) +
    (if 3 ≤ j then 2 else 0) + (if 5 ≤ j then 2 else 0)

/-- The four-term budget, with a separate inherited weight function in every row. -/
theorem component_budget_four (q n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hq : 5 ≤ q) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    weight D * roughIntervalCount (primesUpTo q) n +
      4 * roughCount (primesUpTo q) (n / 2) ≤ weight (interval n c * D) := by
  classical
  have hDvars := largestPrime_vars_subset D q hlargest
  calc
    _ = ∑ b ∈ roughNumbers (primesUpTo q) n, profileFourCost (weight D) (n / b) := by
      simp only [profileFourCost, Finset.sum_add_distrib, sum_indicator_const]
      rw [Pilz.card_roughNumbers_index_one, Pilz.card_roughNumbers_index_ge _ _ 2 (by decide)]
    _ ≤ ∑ b ∈ roughNumbers (primesUpTo q) n,
        weight (smoothInterval (primesUpTo q) (n / b) (fun a => c (b * a)) * D) := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers (primesUpTo q) n b).mp hb
      have hidx : 1 ≤ n / b := (Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn)
      have hcb := component_weights_nonzero (primesUpTo q) n b c hc hb
      by_cases h1 : n / b = 1
      · have hc1 : c (b * 1) ≠ 0 := hcb 1 (one_mem_smoothNumbers _ hidx)
        simp only [profileFourCost, h1, if_pos, Nat.not_ofNat_le_one, if_false, add_zero]
        exact (component_profile_one q _ D hc1).ge
      · have h2 : 2 ≤ n / b := by omega
        have h := component_profile_four q (n / b) _ D hcb hq h2 hD hnorm hlargest
        simpa only [profileFourCost, if_neg h1, if_pos h2, zero_add] using h
    _ = weight (interval n c * D) :=
      (weight_interval_mul_eq_sum_rough_components _ n c D (primesUpTo_prime q) hDvars).symm

theorem component_budget_four_paper (q n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hq : 5 ≤ q) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) (hu : 4 ≤ weight D) :
    4 * roughCount (primesUpTo q) n +
      (weight D - 4) * roughIntervalCount (primesUpTo q) n ≤ weight (interval n c * D) := by
  have hsplit : roughIntervalCount (primesUpTo q) n + roughCount (primesUpTo q) (n / 2) =
      roughCount (primesUpTo q) n :=
    Nat.sub_add_cancel (Pilz.roughCount_mono _ (Nat.div_le_self n 2))
  have huEq : weight D - 4 + 4 = weight D := Nat.sub_add_cancel hu
  have heq : 4 * roughCount (primesUpTo q) n +
      (weight D - 4) * roughIntervalCount (primesUpTo q) n =
      weight D * roughIntervalCount (primesUpTo q) n +
        4 * roughCount (primesUpTo q) (n / 2) := by
    rw [← hsplit]
    calc
      _ = (weight D - 4 + 4) * roughIntervalCount (primesUpTo q) n +
          4 * roughCount (primesUpTo q) (n / 2) := by ring
      _ = _ := by rw [huEq]
  rw [heq]
  exact component_budget_four q n c D hc hq hD hnorm hlargest

/-- The eight-term budget with exact arithmetic component-index counts. -/
theorem component_budget_eight (q n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hq : 17 ≤ q) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    weight D * roughIntervalCount (primesUpTo q) n +
      4 * roughCount (primesUpTo q) (n / 2) +
      2 * roughCount (primesUpTo q) (n / 3) +
      2 * roughCount (primesUpTo q) (n / 5) ≤ weight (interval n c * D) := by
  classical
  have hDvars := largestPrime_vars_subset D q hlargest
  calc
    _ = ∑ b ∈ roughNumbers (primesUpTo q) n, profileEightCost (weight D) (n / b) := by
      simp only [profileEightCost, Finset.sum_add_distrib, sum_indicator_const]
      rw [Pilz.card_roughNumbers_index_one, Pilz.card_roughNumbers_index_ge _ _ 2 (by decide),
        Pilz.card_roughNumbers_index_ge _ _ 3 (by decide),
        Pilz.card_roughNumbers_index_ge _ _ 5 (by decide)]
    _ ≤ ∑ b ∈ roughNumbers (primesUpTo q) n,
        weight (smoothInterval (primesUpTo q) (n / b) (fun a => c (b * a)) * D) := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers (primesUpTo q) n b).mp hb
      have hidx : 1 ≤ n / b := (Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn)
      have hcb := component_weights_nonzero (primesUpTo q) n b c hc hb
      by_cases h1 : n / b = 1
      · have hc1 : c (b * 1) ≠ 0 := hcb 1 (one_mem_smoothNumbers _ hidx)
        simp only [profileEightCost, h1, if_pos, Nat.not_ofNat_le_one, if_false, add_zero]
        exact (component_profile_one q _ D hc1).ge
      · have h2 : 2 ≤ n / b := by omega
        have h := component_profile_eight q (n / b) _ D hcb hq h2 hD hnorm hlargest
        simpa only [profileEightCost, if_neg h1, if_pos h2, zero_add] using h
    _ = weight (interval n c * D) :=
      (weight_interval_mul_eq_sum_rough_components _ n c D (primesUpTo_prime q) hDvars).symm

end WeightedPilz
