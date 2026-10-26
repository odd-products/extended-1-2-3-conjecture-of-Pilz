import Pilz.TwoRowGeneral
import WeightedPilz.RowWeights
import Mathlib.Algebra.Algebra.ZMod

/-! The two-row obstruction over an arbitrary field of characteristic two.
The coefficient ratio must be a scalar; its value need not be one. -/

noncomputable section
namespace WeightedPilz

open Polynomial
variable {K σ : Type*} [Field K] [CharP K 2]

theorem binomial_coefficient_ratio_constant
    (P : (FractionRing (MvPolynomial σ K))[X])
    (b₀ b₁ : FractionRing (MvPolynomial σ K)) (u v i j : ℕ)
    (h0 : P.coeff 0 ≠ 0) (hd : 0 < P.natDegree)
    (hb₁ : b₁ ≠ 0) (huv : u < v)
    (hdiv : P ∣ monomial u b₀ + monomial v b₁)
    (hij : i < j) (hjd : j < P.natDegree)
    (hci : P.coeff i ≠ 0) (hcj : P.coeff j ≠ 0) :
    ∃ a : K, a ≠ 0 ∧
      (P.coeff i) ^ (P.natDegree - j) * P.leadingCoeff ^ (j - i) =
        algebraMap K (FractionRing (MvPolynomial σ K)) a *
          (P.coeff j) ^ (P.natDegree - i) := by
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  letI : CharP (FractionRing (MvPolynomial σ K)) 2 :=
    IsFractionRing.charP_of_isFractionRing (MvPolynomial σ K) 2
  have hP : P ≠ 0 := fun hz => h0 (by simp [hz])
  have hlc := leadingCoeff_ne_zero.mpr hP
  have halg := Pilz.TwoRow.binomial_coefficient_ratio_algebraic_field P b₀ b₁ u v i j
    h0 hd hb₁ huv hdiv hij hjd hci hcj
  have hne : (P.coeff i) ^ (P.natDegree - j) * P.leadingCoeff ^ (j - i) /
      (P.coeff j) ^ (P.natDegree - i) ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero _ hci) (pow_ne_zero _ hlc)) (pow_ne_zero _ hcj)
  obtain ⟨a, ha, heq⟩ := Pilz.TwoRowConstants.algebraic_fraction_constant _
    (halg.tower_top K) hne
  exact ⟨a, ha.ne_zero, (div_eq_iff (pow_ne_zero _ hcj)).mp heq.symm⟩

theorem three_le_rows_of_no_scalar_identity
    (P : (MvPolynomial σ K)[X]) (i j : ℕ)
    (h0 : P.coeff 0 ≠ 0) (hij : i < j) (hjd : j < P.natDegree)
    (hci : P.coeff i ≠ 0) (hcj : P.coeff j ≠ 0)
    (hobs : ∀ a : K, a ≠ 0 →
      (P.coeff i) ^ (P.natDegree - j) * P.leadingCoeff ^ (j - i) ≠
        MvPolynomial.C a * (P.coeff j) ^ (P.natDegree - i))
    (H : (MvPolynomial σ K)[X]) (hH : H ≠ 0) :
    3 ≤ (P * H).support.card := by
  let R := MvPolynomial σ K
  let L := FractionRing R
  let f := algebraMap R L
  have hf : Function.Injective f := IsFractionRing.injective R L
  have hP : P ≠ 0 := fun hz => h0 (by simp [hz])
  have hQ := mul_ne_zero hP hH
  by_contra hcard
  obtain ⟨u, v, b₀, b₁, huv, hb₁, hdiv⟩ :=
    Pilz.TwoRow.exists_binomial_multiple_of_support_le_two P (P * H) hQ
      (dvd_mul_right _ _) (by omega)
  have hdeg : (P.map f).natDegree = P.natDegree := natDegree_map_eq_of_injective hf P
  have h0' : (P.map f).coeff 0 ≠ 0 := by
    rw [coeff_map]
    exact fun hz => h0 (hf (by simpa using hz))
  have hci' : (P.map f).coeff i ≠ 0 := by
    rw [coeff_map]
    exact fun hz => hci (hf (by simpa using hz))
  have hcj' : (P.map f).coeff j ≠ 0 := by
    rw [coeff_map]
    exact fun hz => hcj (hf (by simpa using hz))
  have hb₁' : f b₁ ≠ 0 := fun hz => hb₁ (hf (by simpa using hz))
  have hdiv' : P.map f ∣ monomial u (f b₀) + monomial v (f b₁) := by
    have hm := Polynomial.map_dvd f hdiv
    dsimp [f, R, L] at hm ⊢
    simpa only [Polynomial.map_add, Polynomial.map_monomial] using hm
  obtain ⟨a, ha, heq⟩ := binomial_coefficient_ratio_constant (P.map f)
    (f b₀) (f b₁) u v i j h0' (by rw [hdeg]; omega) hb₁' huv hdiv'
    hij (by rwa [hdeg]) hci' hcj'
  apply hobs a ha
  apply hf
  have hscalar : f (MvPolynomial.C a) = algebraMap K L a :=
    (IsScalarTower.algebraMap_apply K R L a).symm
  simpa only [coeff_map, hdeg, leadingCoeff_map' hf, map_mul, map_pow, hscalar] using heq

theorem top_three_le_rows_of_no_scalar_identity
    (P : (MvPolynomial σ K)[X]) (hd : 2 ≤ P.natDegree)
    (h0 : P.coeff 0 ≠ 0) (hlow : P.coeff (P.natDegree - 2) ≠ 0)
    (hmid : P.coeff (P.natDegree - 1) ≠ 0)
    (hobs : ∀ a : K, a ≠ 0 →
      P.coeff (P.natDegree - 2) * P.leadingCoeff ≠
        MvPolynomial.C a * P.coeff (P.natDegree - 1) ^ 2)
    (H : (MvPolynomial σ K)[X]) (hH : H ≠ 0) :
    3 ≤ (P * H).support.card := by
  have h1 : P.natDegree - (P.natDegree - 1) = 1 := by omega
  have h2 : (P.natDegree - 1) - (P.natDegree - 2) = 1 := by omega
  have h3 : P.natDegree - (P.natDegree - 2) = 2 := by omega
  apply three_le_rows_of_no_scalar_identity P (P.natDegree - 2) (P.natDegree - 1) h0
    (by omega) (by omega) hlow hmid ?_ H hH
  simpa only [h1, h2, h3, pow_one] using hobs

theorem top_three_endpoint_distance [DecidableEq σ] (p : σ)
    (P : MvPolynomial σ K)
    (hd : 2 ≤ (coordinateEquiv p P).natDegree)
    (h0 : (coordinateEquiv p P).coeff 0 ≠ 0)
    (hlow : (coordinateEquiv p P).coeff ((coordinateEquiv p P).natDegree - 2) ≠ 0)
    (hmid : (coordinateEquiv p P).coeff ((coordinateEquiv p P).natDegree - 1) ≠ 0)
    (hobs : ∀ a : K, a ≠ 0 →
      (coordinateEquiv p P).coeff ((coordinateEquiv p P).natDegree - 2) *
        (coordinateEquiv p P).leadingCoeff ≠
      MvPolynomial.C a * (coordinateEquiv p P).coeff ((coordinateEquiv p P).natDegree - 1) ^ 2) :
    distance ((coordinateEquiv p P).coeff 0) +
      distance ((coordinateEquiv p P).coeff (coordinateEquiv p P).natDegree) + 1 ≤ distance P := by
  have htrail : (coordinateEquiv p P).natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr h0)
  have hspan : (coordinateEquiv p P).natTrailingDegree < (coordinateEquiv p P).natDegree := by
    omega
  have hend := endpoint_distance_of_three_rows p P hspan (by
    intro H hH
    rw [map_mul]
    exact top_three_le_rows_of_no_scalar_identity (coordinateEquiv p P) hd h0 hlow hmid hobs
      (coordinateEquiv p H) (coordinateEquiv_ne_zero p hH))
  simpa only [Polynomial.trailingCoeff, htrail, Polynomial.leadingCoeff] using hend

end WeightedPilz

