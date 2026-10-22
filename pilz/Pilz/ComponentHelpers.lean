import Pilz.ComponentProfile

/-! Generic smooth-component estimates for small sets of support primes. -/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

/-- Below every allowed prime the smooth interval consists only of one. -/
theorem smoothInterval_eq_one_below (T : Finset ℕ) (j : ℕ) (hj : 1 ≤ j)
    (hbelow : ∀ p ∈ T, j < p) : smoothInterval T j = 1 := by
  classical
  have hnums : smoothNumbers T j = {1} := by
    ext c
    constructor
    · intro hc
      obtain ⟨hcpos, hcj, hcs⟩ := (mem_smoothNumbers T j c).mp hc
      have hc1 : c = 1 := by
        by_contra hc1
        obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd hc1
        have hmem : p ∈ c.factorization.support := Finsupp.mem_support_iff.mpr
          (ne_of_gt (hp.factorization_pos_of_dvd (ne_of_gt hcpos) hpc))
        have hpT : p ∈ T := hcs hmem
        exact (Nat.not_le_of_gt (hbelow p hpT)) ((Nat.le_of_dvd hcpos hpc).trans hcj)
      exact Finset.mem_singleton.mpr hc1
    · intro hc
      have hc1 := Finset.mem_singleton.mp hc
      subst c
      exact (mem_smoothNumbers T j 1).mpr ⟨le_rfl, hj, smooth_one T⟩
  rw [smoothInterval, hnums, polynomialOf_singleton, monomialOf_one]

/-- Variables larger than the index do not occur in a smooth component. -/
theorem smoothInterval_independent_above (T : Finset ℕ) (j q : ℕ) (hjq : j < q) :
    ∀ d ∈ (smoothInterval T j).support, d q = 0 := by
  intro d hd
  have hpos : ∀ a ∈ smoothNumbers T j, 0 < a :=
    fun a ha => ((mem_smoothNumbers T j a).mp ha).1
  rw [smoothInterval, support_polynomialOf _ hpos] at hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  exact Nat.factorization_eq_zero_of_lt (((mem_smoothNumbers T j a).mp ha).2.1.trans_lt hjq)

/-- Each activated prime supplies its pure endpoint, in any smooth set T. -/
theorem smooth_component_endpoints (T S : Finset ℕ) (j : ℕ) (D : Poly)
    (hj : 1 ≤ j) (hD : D ≠ 0) (hST : S ⊆ T)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hactive : ∀ p ∈ S, p ≤ j) :
    S.card + 1 ≤ weight (smoothInterval T j * D) := by
  have h0 : coeff 0 (smoothInterval T j) ≠ 0 := by
    rw [smoothInterval_coeff_zero T j hj]
    exact one_ne_zero
  have hpure : ∀ p ∈ S, ∃ k : ℕ, 0 < k ∧
      coeff (Finsupp.single p k) (smoothInterval T j) ≠ 0 := by
    intro p hp
    refine ⟨1, by decide, ?_⟩
    rw [smoothInterval_coeff_prime T j p (hprime p hp) (hST hp) (hactive p hp)]
    exact one_ne_zero
  exact pure_endpoints_weight_mul S (smoothInterval T j) D h0 hpure hD

/-- Two independent multiplier slices each pay the two-endpoint budget. -/
theorem independent_two_slice_expansion_two (P D : Poly) (p q : ℕ) (hpq : p ≠ q)
    (hP : ∀ d ∈ P.support, d q = 0)
    (h0 : coeff 0 P = 1) (hp : coeff (Finsupp.single p 1) P = 1)
    (hzero : ∃ d ∈ D.support, d q = 0)
    (hpos : ∃ d ∈ D.support, 0 < d q) : 4 ≤ weight (P * D) := by
  let A := (coordinateEquiv q P).coeff 0
  let t : {i : ℕ // i ≠ q} := ⟨p, hpq⟩
  have hA0 : coeff 0 A ≠ 0 := by
    change coeff 0 ((coordinateEquiv q P).coeff 0) ≠ 0
    rw [coordinate_coeff_zero, h0]
    exact one_ne_zero
  have hAt : coeff (Finsupp.single t 1) A ≠ 0 := by
    change coeff (Finsupp.single (⟨p, hpq⟩ : {i : ℕ // i ≠ q}) 1)
      ((coordinateEquiv q P).coeff 0) ≠ 0
    rw [coordinate_coeff_pure_of_ne q p hpq, hp]
    exact one_ne_zero
  have hbudget : 2 ≤ distance A := by
    have h := pure_endpoints_distance {t} A hA0 (by
      intro r hr
      have heq : r = t := Finset.mem_singleton.mp hr
      subst r
      exact ⟨1, by decide, hAt⟩)
    simpa only [Finset.card_singleton] using h
  exact independent_two_slice_expansion P D q 2 hP hzero hpos hbudget

/-- Sum any genuine uniform component estimate over an arbitrary prime set. -/
theorem uniform_component_budget_set (T : Finset ℕ) (n c : ℕ) (D : Poly)
    (hT : ∀ p ∈ T, Nat.Prime p) (hD : D.vars ⊆ T)
    (hprofile : ∀ j : ℕ, 1 ≤ j → c ≤ weight (smoothInterval T j * D)) :
    c * roughCount T n ≤ weight (interval n * D) := by
  classical
  calc
    _ = ∑ _b ∈ roughNumbers T n, c := by simp [roughCount, Nat.mul_comm]
    _ ≤ ∑ b ∈ roughNumbers T n, weight (smoothInterval T (n / b) * D) := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers T n b).mp hb
      apply hprofile
      apply (Nat.le_div_iff_mul_le hbpos).mpr
      simpa using hbn
    _ = _ := (weight_interval_mul_eq_sum_rough_components T n D hT hD).symm

end Pilz
