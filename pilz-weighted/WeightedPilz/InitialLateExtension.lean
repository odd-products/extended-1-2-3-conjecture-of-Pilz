import WeightedPilz.RepeatedEndpoints
import WeightedPilz.LinearExtensionOps

/-! Endpoint and coprimality tools for the later initial cores in the original variables. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem coordinateEquiv_rename_val (p : ℕ)
    (P : MvPolynomial {q : ℕ // q ≠ p} K) :
    coordinateEquiv p (rename Subtype.val P) = Polynomial.C P := by
  have hh : ((coordinateEquiv (K := K) p).toRingHom.comp
      (rename (Subtype.val : {q : ℕ // q ≠ p} → ℕ)).toRingHom) = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coordinateEquiv, optionEquivLeft_C]
    · intro q
      simp [coordinateEquiv, Equiv.optionSubtypeNe_symm_of_ne q.property,
        optionEquivLeft_X_some]
  exact RingHom.congr_fun hh P

theorem coordinate_constant_of_degree_zero (p : ℕ) (A : Poly K)
    (hA : A.degreeOf p = 0) :
    coordinateEquiv p A = Polynomial.C ((coordinateEquiv p A).coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  rwa [natDegree_coordinateEquiv]

theorem linear_core_power_mul_endpoints (p : ℕ) (A B M : Poly K) (hB : B ≠ 0)
    (hAdegree : A.degreeOf p = 0) (hBdegree : B.degreeOf p = 0)
    (hMdegree : M.degreeOf p = 0) {k : ℕ} (hk : 0 < k) :
    weight (A ^ k * M) + weight (B ^ k * M) ≤
      weight ((A + B * X p) ^ k * M) := by
  let E := coordinateEquiv (K := K) p
  let a := (E A).coeff 0
  let b := (E B).coeff 0
  let m := (E M).coeff 0
  have hB0 : b ≠ 0 := by
    intro hz
    apply hB
    rw [← coordinate_zero_recover p B hBdegree]
    change rename Subtype.val b = 0
    rw [hz, map_zero]
  let Q : Polynomial (MvPolynomial {q : ℕ // q ≠ p} K) :=
    Polynomial.C a + Polynomial.C b * Polynomial.X
  have hdeg : Q.natDegree = 1 := by
    simpa only [Q, add_comm] using Polynomial.natDegree_linear hB0 (b := a)
  have hlc : Q.leadingCoeff = b := by
    simpa only [Q, add_comm] using Polynomial.leadingCoeff_linear hB0 (b := a)
  have htop : (Q ^ k).coeff k = b ^ k := by
    simpa only [hdeg, mul_one, hlc] using Polynomial.coeff_pow_mul_natDegree Q k
  have hzero : (Q ^ k).coeff 0 = a ^ k := by
    change Polynomial.constantCoeff (Q ^ k) = _
    rw [map_pow]
    simp [Q]
  have hlow : (Q ^ k * Polynomial.C m).coeff 0 = a ^ k * m := by
    rw [Polynomial.coeff_mul_C, hzero]
  have hhigh : (Q ^ k * Polynomial.C m).coeff k = b ^ k * m := by
    rw [Polynomial.coeff_mul_C, htop]
  have hE : E ((A + B * X p) ^ k * M) = Q ^ k * Polynomial.C m := by
    rw [map_mul, map_pow, map_add, map_mul,
      coordinate_constant_of_degree_zero p A hAdegree,
      coordinate_constant_of_degree_zero p B hBdegree,
      coordinate_constant_of_degree_zero p M hMdegree]
    have hX : E (X p) = Polynomial.X := by
      simp [E, coordinateEquiv, optionEquivLeft_X_none]
    rw [hX]
  have h := weight_two_coordinate_slices p ((A + B * X p) ^ k * M) 0 k (Nat.ne_of_lt hk)
  change weight ((E _).coeff 0) + weight ((E _).coeff k) ≤ _ at h
  rw [hE, hlow, hhigh] at h
  have hw (R : Poly K) (hR : R.degreeOf p = 0) :
      weight (R ^ k * M) = weight (((E R).coeff 0) ^ k * m) := by
    calc
      weight (R ^ k * M) =
          weight (rename Subtype.val (((E R).coeff 0) ^ k * m)) := by
        congr 1
        rw [map_mul, map_pow, coordinate_zero_recover p R hR,
          coordinate_zero_recover p M hMdegree]
      _ = _ := weight_rename_of_injective Subtype.val Subtype.val_injective _
  rw [hw A hAdegree, hw B hBdegree]
  exact h

theorem linear_core_power_endpoints (p : ℕ) (A B : Poly K) (hB : B ≠ 0)
    (hAdegree : A.degreeOf p = 0) (hBdegree : B.degreeOf p = 0)
    {k : ℕ} (hk : 0 < k) :
    weight (A ^ k) + weight (B ^ k) ≤ weight ((A + B * X p) ^ k) := by
  simpa using linear_core_power_mul_endpoints p A B 1 hB hAdegree hBdegree
    (by simpa only [map_one] using degreeOf_C (1 : K) p) hk

theorem isRelPrime_of_coordinate_coprime_coeff (p : ℕ) (R D : Poly K)
    (hD : D ≠ 0) (hDdegree : D.degreeOf p = 0) (i : ℕ)
    (hi : IsRelPrime ((coordinateEquiv p R).coeff i) ((coordinateEquiv p D).coeff 0)) :
    IsRelPrime R D := by
  let E := coordinateEquiv (K := K) p
  have hD0 : (E D).coeff 0 ≠ 0 := by
    intro hz
    apply hD
    rw [← coordinate_zero_recover p D hDdegree, hz, map_zero]
  have hcop := isRelPrime_constant_of_coprime_coeff (E R) ((E D).coeff 0) hD0 i hi
  intro d hdR hdD
  have hunit := hcop (map_dvd E hdR) (by
    have hmap := map_dvd E hdD
    change E d ∣ coordinateEquiv p D at hmap
    rw [coordinate_constant_of_degree_zero p D hDdegree] at hmap
    exact hmap)
  have hback := hunit.map E.symm.toMonoidHom
  change IsUnit (E.symm (E d)) at hback
  simpa only [AlgEquiv.symm_apply_apply] using hback

theorem isRelPrime_of_coordinate_unit_coeff (p : ℕ) (R D : Poly K)
    (hD : D ≠ 0) (hDdegree : D.degreeOf p = 0) (i : ℕ)
    (hi : IsUnit ((coordinateEquiv p R).coeff i)) : IsRelPrime R D := by
  apply isRelPrime_of_coordinate_coprime_coeff p R D hD hDdegree i
  intro d hd _
  exact isUnit_of_dvd_unit hd hi

theorem coordinate_zero_isRelPrime (p : ℕ) (A B : Poly K)
    (hAdegree : A.degreeOf p = 0) (hBdegree : B.degreeOf p = 0)
    (hcop : IsRelPrime A B) :
    IsRelPrime ((coordinateEquiv p A).coeff 0) ((coordinateEquiv p B).coeff 0) := by
  intro d hdA hdB
  have hA : rename Subtype.val d ∣ A := by
    rw [← coordinate_zero_recover p A hAdegree]
    exact map_dvd (rename Subtype.val) hdA
  have hB : rename Subtype.val d ∣ B := by
    rw [← coordinate_zero_recover p B hBdegree]
    exact map_dvd (rename Subtype.val) hdB
  have hu := (hcop hA hB).map (coordinateEquiv p).toMonoidHom
  change IsUnit (coordinateEquiv p (rename Subtype.val d)) at hu
  rw [coordinateEquiv_rename_val] at hu
  exact Polynomial.isUnit_C.mp hu

theorem linear_core_isRelPrime_of_top (p : ℕ) (A B D : Poly K) (hD : D ≠ 0)
    (hAdegree : A.degreeOf p = 0) (hBdegree : B.degreeOf p = 0)
    (hDdegree : D.degreeOf p = 0) (hcop : IsRelPrime B D) :
    IsRelPrime (A + B * X p) D := by
  apply isRelPrime_of_coordinate_coprime_coeff p _ D hD hDdegree 1
  have hX : coordinateEquiv (K := K) p (X p) = Polynomial.X := by
    simp [coordinateEquiv, optionEquivLeft_X_none]
  rw [map_add, map_mul, coordinate_constant_of_degree_zero p A hAdegree,
    coordinate_constant_of_degree_zero p B hBdegree, hX]
  simpa using coordinate_zero_isRelPrime p B D hBdegree hDdegree hcop

end WeightedPilz
