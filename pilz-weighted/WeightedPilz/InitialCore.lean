import WeightedPilz.IntervalFresh
import WeightedPilz.IntervalEndpoints

/-! Endpoint estimates for the cores of the initial weighted intervals. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem coeff_intervalCore (n : ℕ) (c : ℕ → K) {a : ℕ} (ha : 0 < a) :
    coeff a.factorization (intervalCore n c) =
      if a ∈ Finset.Icc 1 n \ intervalFreshPrimes n then c a else 0 := by
  apply coeff_polynomialOf _ c _ ha
  intro b hb
  exact (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hb).1).1

theorem coeff_intervalCore_ne_zero (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) {a : ℕ}
    (ha : a ∈ Finset.Icc 1 n \ intervalFreshPrimes n) :
    coeff a.factorization (intervalCore n c) ≠ 0 := by
  have hpos := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).1
  rw [coeff_intervalCore n c hpos, if_pos ha]
  exact hc a (Finset.mem_sdiff.mp ha).1

/-- Four corners in two consecutive rows force two terms at each endpoint. -/
theorem linear_rectangle_distance {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ K) (p q : σ) (hqp : q ≠ p)
    (hdeg : P.degreeOf p ≤ 1)
    (h0 : coeff 0 P ≠ 0)
    (hp : coeff (Finsupp.single p 1) P ≠ 0)
    (hq : coeff (Finsupp.single q 1) P ≠ 0)
    (hpq : coeff (Finsupp.single p 1 + Finsupp.single q 1) P ≠ 0) :
    4 ≤ distance P := by
  classical
  let Q := coordinateEquiv p P
  let q' : {q : σ // q ≠ p} := ⟨q, hqp⟩
  have h00 : coeff 0 (Q.coeff 0) ≠ 0 := by
    simpa only [Q, coordinate_coeff_zero] using h0
  have h10 : coeff 0 (Q.coeff 1) ≠ 0 := by
    simpa only [Q, coordinate_coeff_pure_self] using hp
  have h01 : coeff (Finsupp.single q' 1) (Q.coeff 0) ≠ 0 := by
    simpa only [Q, q', coordinate_coeff_pure_of_ne] using hq
  have h11 : coeff (Finsupp.single q' 1) (Q.coeff 1) ≠ 0 := by
    have heq := coordinate_coeff_coeff p P (Finsupp.single p 1 + Finsupp.single q 1)
    simp only [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hqp.symm, add_zero, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single, Equiv.optionSubtypeNe_symm_self,
      Equiv.optionSubtypeNe_symm_of_ne hqp, Finsupp.some_add,
      Finsupp.some_single_none, Finsupp.some_single_some, zero_add] at heq
    exact heq.symm ▸ hpq
  have hrow (i : ℕ) (hzero : coeff 0 (Q.coeff i) ≠ 0)
      (hone : coeff (Finsupp.single q' 1) (Q.coeff i) ≠ 0) :
      2 ≤ distance (Q.coeff i) := by
    have h := pure_endpoints_distance {q'} (Q.coeff i) hzero (by
      intro z hz
      have hzq : z = q' := Finset.mem_singleton.mp hz
      subst z
      exact ⟨1, by decide, hone⟩)
    simpa using h
  have ht : Q.natTrailingDegree = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero.mpr
    right
    intro hz
    exact h00 (by rw [hz, coeff_zero])
  have hd : Q.natDegree = 1 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · simpa only [Q, natDegree_coordinateEquiv] using hdeg
    · intro hz
      exact h10 (by rw [hz, coeff_zero])
  have hend := endpoint_distance p P (show Q.natTrailingDegree < Q.natDegree by omega)
  change distance Q.trailingCoeff + distance Q.leadingCoeff ≤ distance P at hend
  rw [Polynomial.trailingCoeff, Polynomial.leadingCoeff, ht, hd] at hend
  have hA := hrow 0 h00 h01
  have hB := hrow 1 h10 h11
  omega

theorem intervalCore_distance_four (n : ℕ) (hn : 6 ≤ n) (hn8 : n ≤ 8)
    (c : ℕ → K) (hc : NonzeroWeights n c) : 4 ≤ distance (intervalCore n c) := by
  have hmem : ∀ a ∈ ({1, 2, 3, 6} : Finset ℕ),
      a ∈ Finset.Icc 1 n \ intervalFreshPrimes n := by
    intro a ha
    interval_cases n <;> norm_num [Finset.mem_sdiff, Pilz.mem_freshPrimes_iff,
      Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at ha ⊢ <;>
      rcases ha with rfl | rfl | rfl | rfl <;> norm_num <;> decide
  have hfac3 : (3 : ℕ).factorization = Finsupp.single 3 1 :=
    (by decide : Nat.Prime 3).factorization
  have hfac2 : (2 : ℕ).factorization = Finsupp.single 2 1 :=
    (by decide : Nat.Prime 2).factorization
  have hfac6 : (6 : ℕ).factorization = Finsupp.single 3 1 + Finsupp.single 2 1 := by
    change (3 * 2 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), hfac3, hfac2]
  apply linear_rectangle_distance (intervalCore n c) 3 2 (by decide)
  · apply degreeOf_le_iff.mpr
    intro d hd
    rw [intervalCore_support n c hc] at hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    have hab := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1)
    by_contra hgt
    have hpow : 3 ^ 2 ∣ a :=
      ((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
    have hle := Nat.le_of_dvd (by omega : 0 < a) hpow
    norm_num at hle
    omega
  · simpa only [Nat.factorization_one] using
      coeff_intervalCore_ne_zero n c hc (hmem 1 (by simp))
  · simpa only [hfac3] using coeff_intervalCore_ne_zero n c hc (hmem 3 (by simp))
  · simpa only [hfac2] using coeff_intervalCore_ne_zero n c hc (hmem 2 (by simp))
  · simpa only [hfac6] using coeff_intervalCore_ne_zero n c hc (hmem 6 (by simp))

end WeightedPilz
