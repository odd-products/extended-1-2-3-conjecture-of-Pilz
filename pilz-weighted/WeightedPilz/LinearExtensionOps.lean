import WeightedPilz.InitialExtension
import WeightedPilz.Completion

/-! Endpoint estimates for adjoining one variable with a polynomial coefficient. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K]

theorem isRelPrime_constant_of_coprime_coeff {A : Type*} [CommRing A] [IsDomain A]
    (R : Polynomial A) (D : A) (hD : D ≠ 0) (i : ℕ)
    (hi : IsRelPrime (R.coeff i) D) : IsRelPrime R (Polynomial.C D) := by
  intro Q hQR hQD
  have hdeg : Q.natDegree = 0 := by
    have hle := Polynomial.natDegree_le_of_dvd hQD
      (show Polynomial.C D ≠ 0 by simpa using hD)
    simpa only [Polynomial.natDegree_C, Nat.le_zero] using hle
  have hQ := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hcoeff : Q.coeff 0 ∣ R.coeff i := by
    obtain ⟨T, hT⟩ := hQR
    refine ⟨T.coeff i, ?_⟩
    rw [hT, hQ, Polynomial.coeff_C_mul, Polynomial.coeff_C_zero]
  have hconst : Q.coeff 0 ∣ D := by
    obtain ⟨T, hT⟩ := hQD
    refine ⟨T.coeff 0, ?_⟩
    have hT' : Polynomial.C D = Polynomial.C (Q.coeff 0) * T := by
      rw [← hQ]
      exact hT
    have h := congrArg (fun P : Polynomial A => P.coeff 0) hT'
    simpa only [Polynomial.coeff_C_mul, Polynomial.coeff_C_zero] using h
  rw [hQ]
  exact (hi hcoeff hconst).map Polynomial.C

def linearExtension (R D : MvPolynomial σ K) : MvPolynomial (Option σ) K :=
  rename some R + rename some D * X none

@[simp] theorem optionEquiv_linearExtension (R D : MvPolynomial σ K) :
    optionEquivLeft K σ (linearExtension R D) =
      Polynomial.C R + Polynomial.C D * Polynomial.X := by
  simp [linearExtension, optionEquivLeft_rename_some, optionEquivLeft_X_none]

theorem linearExtension_eq_symm (R D : MvPolynomial σ K) :
    linearExtension R D = (optionEquivLeft K σ).symm
      (Polynomial.C R + Polynomial.C D * Polynomial.X) := by
  apply (optionEquivLeft K σ).injective
  rw [optionEquiv_linearExtension, AlgEquiv.apply_symm_apply]

theorem linearExtension_power_mul_endpoints (R D : MvPolynomial σ K) (hD : D ≠ 0)
    (M : MvPolynomial σ K) {n : ℕ} (hn : 0 < n) :
    weight (R ^ n * M) + weight (D ^ n * M) ≤
      weight (linearExtension R D ^ n * rename some M) := by
  let Q : Polynomial (MvPolynomial σ K) := Polynomial.C R + Polynomial.C D * Polynomial.X
  have hdeg : Q.natDegree = 1 := by
    simpa only [Q, add_comm] using Polynomial.natDegree_linear hD (b := R)
  have hlc : Q.leadingCoeff = D := by
    simpa only [Q, add_comm] using Polynomial.leadingCoeff_linear hD (b := R)
  have htop : (Q ^ n).coeff n = D ^ n := by
    simpa only [hdeg, mul_one, hlc] using Polynomial.coeff_pow_mul_natDegree Q n
  have hzero : (Q ^ n).coeff 0 = R ^ n := by
    change Polynomial.constantCoeff (Q ^ n) = _
    rw [map_pow]
    simp [Q]
  have hlow : (Q ^ n * Polynomial.C M).coeff 0 = R ^ n * M := by
    rw [Polynomial.coeff_mul_C, hzero]
  have hhigh : (Q ^ n * Polynomial.C M).coeff n = D ^ n * M := by
    rw [Polynomial.coeff_mul_C, htop]
  have hE : optionEquivLeft K σ (linearExtension R D ^ n * rename some M) =
      Q ^ n * Polynomial.C M := by
    rw [map_mul, map_pow, optionEquiv_linearExtension, optionEquivLeft_rename_some]
  have h := weight_two_slices (linearExtension R D ^ n * rename some M) 0 n (Nat.ne_of_lt hn)
  rw [hE, hlow, hhigh] at h
  exact h

theorem linearExtension_power_endpoints (R D : MvPolynomial σ K) (hD : D ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    weight (R ^ n) + weight (D ^ n) ≤ weight (linearExtension R D ^ n) := by
  simpa using linearExtension_power_mul_endpoints R D hD 1 hn

theorem linearExtension_distance_endpoints (R D : MvPolynomial σ K)
    (hR : R ≠ 0) (hD : D ≠ 0) :
    distance R + distance D ≤ distance (linearExtension R D) := by
  let Q : Polynomial (MvPolynomial σ K) := Polynomial.C R + Polynomial.C D * Polynomial.X
  have hdeg : Q.natDegree = 1 := by
    simpa only [Q, add_comm] using Polynomial.natDegree_linear hD (b := R)
  have hlc : Q.leadingCoeff = D := by
    simpa only [Q, add_comm] using Polynomial.leadingCoeff_linear hD (b := R)
  have ht : Q.natTrailingDegree = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero.mpr
    right
    simpa [Q] using hR
  have htc : Q.trailingCoeff = R := by simp [Polynomial.trailingCoeff, ht, Q]
  have h := endpoint_distance_option (linearExtension R D) (by
    rw [optionEquiv_linearExtension]
    change Q.natTrailingDegree < Q.natDegree
    rw [ht, hdeg]
    decide)
  rw [optionEquiv_linearExtension] at h
  change distance Q.trailingCoeff + distance Q.leadingCoeff ≤ _ at h
  rwa [htc, hlc] at h

theorem isRelPrime_of_option_unit_coeff (R : MvPolynomial (Option σ) K)
    (D : MvPolynomial σ K) (hD : D ≠ 0) (i : ℕ)
    (hi : IsUnit ((optionEquivLeft K σ R).coeff i)) :
    IsRelPrime R (rename some D) := by
  have hcop := isRelPrime_constant_of_unit_coeff (optionEquivLeft K σ R) D hD i hi
  intro d hdR hdD
  have hunit := hcop (map_dvd (optionEquivLeft K σ) hdR) (by
      simpa only [optionEquivLeft_rename_some] using map_dvd (optionEquivLeft K σ) hdD)
  have hback := hunit.map (optionEquivLeft K σ).symm.toMonoidHom
  change IsUnit ((optionEquivLeft K σ).symm ((optionEquivLeft K σ) d)) at hback
  simpa only [AlgEquiv.symm_apply_apply] using hback

theorem isRelPrime_of_option_coprime_coeff (R : MvPolynomial (Option σ) K)
    (D : MvPolynomial σ K) (hD : D ≠ 0) (i : ℕ)
    (hi : IsRelPrime ((optionEquivLeft K σ R).coeff i) D) :
    IsRelPrime R (rename some D) := by
  have hcop := isRelPrime_constant_of_coprime_coeff (optionEquivLeft K σ R) D hD i hi
  intro d hdR hdD
  have hunit := hcop (map_dvd (optionEquivLeft K σ) hdR) (by
      simpa only [optionEquivLeft_rename_some] using map_dvd (optionEquivLeft K σ) hdD)
  have hback := hunit.map (optionEquivLeft K σ).symm.toMonoidHom
  change IsUnit ((optionEquivLeft K σ).symm ((optionEquivLeft K σ) d)) at hback
  simpa only [AlgEquiv.symm_apply_apply] using hback

theorem linearExtension_isRelPrime_of_base (R D V : MvPolynomial σ K) (hV : V ≠ 0)
    (hcop : IsRelPrime R V) : IsRelPrime (linearExtension R D) (rename some V) := by
  apply isRelPrime_of_option_coprime_coeff _ V hV 0
  simpa [optionEquiv_linearExtension] using hcop

theorem linearExtension_isRelPrime_of_top (R D V : MvPolynomial σ K) (hV : V ≠ 0)
    (hcop : IsRelPrime D V) : IsRelPrime (linearExtension R D) (rename some V) := by
  apply isRelPrime_of_option_coprime_coeff _ V hV 1
  simpa [optionEquiv_linearExtension] using hcop

end WeightedPilz
