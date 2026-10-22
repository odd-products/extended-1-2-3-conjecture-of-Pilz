import Pilz.TwoRow
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

noncomputable section

namespace Pilz.TwoRow

open Polynomial

theorem esymm_scale {K : Type*} [CommSemiring K] (s : Multiset K) (r : K) (k : ℕ) :
    (s.map (fun x => r * x)).esymm k = r ^ k * s.esymm k := by
  rw [Multiset.esymm, Multiset.esymm, ← Multiset.sum_map_mul_left,
    Multiset.powersetCard_map, Multiset.map_map, Multiset.map_congr rfl]
  intro x hx
  dsimp only [Function.comp_apply]
  rw [(Multiset.mem_powersetCard.mp hx).right.symm,
    ← Multiset.prod_replicate, ← Multiset.map_const]
  nth_rw 3 [← Multiset.map_id' x]
  rw [← Multiset.prod_map_mul, Multiset.map_congr rfl]
  intro z _hz
  rfl

theorem algebraic_esymm {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (s : Multiset K) (hs : ∀ x ∈ s, IsAlgebraic (ZMod 2) x) (k : ℕ) :
    IsAlgebraic (ZMod 2) (s.esymm k) := by
  apply IsIntegral.isAlgebraic
  unfold Multiset.esymm
  apply IsIntegral.multiset_sum
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  apply IsIntegral.multiset_prod
  intro y hy
  exact (hs y (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).left hy)).isIntegral

/-- The cancellation of the common root scale in the coefficient quotient. -/
theorem scaled_coefficient_ratio {K : Type*} [Field K]
    (l r x y : K) (A B : ℕ) (hl : l ≠ 0) (hr : r ≠ 0) (hy : y ≠ 0) :
    (l * r ^ (A + B) * x) ^ A * l ^ B / (l * r ^ A * y) ^ (A + B) =
      x ^ A / y ^ (A + B) := by
  simp only [mul_pow, pow_add, ← pow_mul]
  rw [Nat.mul_comm B A]
  field_simp [hl, hr, hy]
  <;> ring

section AlgebraicallyClosed

variable {K : Type*} [Field K] [CharP K 2] [IsAlgClosed K] [Algebra (ZMod 2) K]

/-- Vieta's formula after dividing every root by a fixed nonzero scale. -/
theorem coeff_eq_root_scale (P : K[X]) (ρ : K) (hρ : ρ ≠ 0) (k : ℕ)
    (hk : k ≤ P.natDegree) :
    P.coeff k = P.leadingCoeff * ρ ^ (P.natDegree - k) *
      (P.roots.map (fun α => α / ρ)).esymm (P.natDegree - k) := by
  have hroots : (P.roots.map (fun α => α / ρ)).map (fun x => ρ * x) = P.roots := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id' P.roots]
    apply Multiset.map_congr rfl
    intro α _hα
    simp [Function.comp_def, mul_div_cancel₀ _ hρ]
  have hV := Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits P) hk
  rw [← hroots, esymm_scale] at hV
  simpa only [CharTwo.neg_eq, one_pow, mul_one, mul_assoc] using hV

/-- The general root-ratio argument: any coefficient quotient occurring in
the paper's two-row lemma is algebraic over the prime field. -/
theorem binomial_coefficient_ratio_algebraic
    (P : K[X]) (b₀ b₁ : K) (u v i j : ℕ)
    (h0 : P.coeff 0 ≠ 0) (hd : 0 < P.natDegree)
    (hb₁ : b₁ ≠ 0) (huv : u < v)
    (hdiv : P ∣ monomial u b₀ + monomial v b₁)
    (hij : i < j) (hjd : j < P.natDegree)
    (hci : P.coeff i ≠ 0) (hcj : P.coeff j ≠ 0) :
    IsAlgebraic (ZMod 2)
      ((P.coeff i) ^ (P.natDegree - j) * P.leadingCoeff ^ (j - i) /
        (P.coeff j) ^ (P.natDegree - i)) := by
  have hP : P ≠ 0 := fun hz => h0 (by simp [hz])
  obtain ⟨ρ, hρroot⟩ := IsAlgClosed.exists_root P
    (Polynomial.degree_ne_of_natDegree_ne (Nat.ne_of_gt hd))
  have hρ : ρ ≠ 0 := by
    intro hz
    apply h0
    simpa only [Polynomial.IsRoot, hz, ← Polynomial.coeff_zero_eq_eval_zero] using hρroot
  let s := P.roots.map (fun α => α / ρ)
  have hs : ∀ x ∈ s, IsAlgebraic (ZMod 2) x := by
    intro x hx
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp hx
    have hαroot : eval α P = 0 := Polynomial.isRoot_of_mem_roots hα
    have hα : α ≠ 0 := by
      intro hz
      apply h0
      simpa only [hz, ← Polynomial.coeff_zero_eq_eval_zero] using hαroot
    have hαeval : b₀ * α ^ u + b₁ * α ^ v = 0 := by
      simpa using eval_eq_zero_of_dvd_of_eval_eq_zero hdiv hαroot
    have hρeval : b₀ * ρ ^ u + b₁ * ρ ^ v = 0 := by
      simpa using eval_eq_zero_of_dvd_of_eval_eq_zero hdiv hρroot
    exact root_ratio_algebraic α ρ (v - u) hρ (by omega)
      (equal_pow_of_binomial_roots α ρ b₀ b₁ u v hα hρ hb₁ huv hαeval hρeval)
  have hi := coeff_eq_root_scale P ρ hρ i (by omega)
  have hj := coeff_eq_root_scale P ρ hρ j (by omega)
  change P.coeff i = P.leadingCoeff * ρ ^ (P.natDegree - i) *
    s.esymm (P.natDegree - i) at hi
  change P.coeff j = P.leadingCoeff * ρ ^ (P.natDegree - j) *
    s.esymm (P.natDegree - j) at hj
  have hy : s.esymm (P.natDegree - j) ≠ 0 := by
    intro hz
    apply hcj
    rw [hj, hz, mul_zero]
  have hdiff : P.natDegree - i = (P.natDegree - j) + (j - i) := by omega
  have heq : (P.coeff i) ^ (P.natDegree - j) * P.leadingCoeff ^ (j - i) /
      (P.coeff j) ^ (P.natDegree - i) =
      s.esymm (P.natDegree - i) ^ (P.natDegree - j) /
        s.esymm (P.natDegree - j) ^ (P.natDegree - i) := by
    rw [hi, hj]
    conv_lhs => rw [hdiff]
    conv_rhs => rw [hdiff]
    exact scaled_coefficient_ratio P.leadingCoeff ρ
      (s.esymm ((P.natDegree - j) + (j - i))) (s.esymm (P.natDegree - j))
      (P.natDegree - j) (j - i) (Polynomial.leadingCoeff_ne_zero.mpr hP) hρ hy
  rw [heq]
  simpa only [div_eq_mul_inv] using
    ((algebraic_esymm s hs (P.natDegree - i)).pow (P.natDegree - j)).mul
      (((algebraic_esymm s hs (P.natDegree - j)).pow (P.natDegree - i)).inv)

end AlgebraicallyClosed

/-- Descend the root-ratio calculation from an algebraic closure. -/
theorem binomial_coefficient_ratio_algebraic_field
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (P : K[X]) (b₀ b₁ : K) (u v i j : ℕ)
    (h0 : P.coeff 0 ≠ 0) (hd : 0 < P.natDegree)
    (hb₁ : b₁ ≠ 0) (huv : u < v)
    (hdiv : P ∣ monomial u b₀ + monomial v b₁)
    (hij : i < j) (hjd : j < P.natDegree)
    (hci : P.coeff i ≠ 0) (hcj : P.coeff j ≠ 0) :
    IsAlgebraic (ZMod 2)
      ((P.coeff i) ^ (P.natDegree - j) * P.leadingCoeff ^ (j - i) /
        (P.coeff j) ^ (P.natDegree - i)) := by
  let Ω := AlgebraicClosure K
  let f := algebraMap K Ω
  have hf : Function.Injective f := RingHom.injective f
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
    dsimp [f] at hm ⊢
    simpa only [Polynomial.map_add, Polynomial.map_monomial] using hm
  have h := binomial_coefficient_ratio_algebraic (P.map f) (f b₀) (f b₁) u v i j
    h0' (by rwa [hdeg]) hb₁' huv hdiv' hij (by rwa [hdeg]) hci' hcj'
  have hmap : IsAlgebraic (ZMod 2)
      (f ((P.coeff i) ^ (P.natDegree - j) * P.leadingCoeff ^ (j - i) /
        (P.coeff j) ^ (P.natDegree - i))) := by
    simpa only [coeff_map, hdeg, leadingCoeff_map' hf,
      map_div₀, map_mul, map_pow] using h
  exact (isAlgebraic_algebraMap_iff (R := ZMod 2) hf).mp hmap

/-- The general coefficient identity in the manuscript's two-row lemma. -/
theorem general_binomial_identity {σ : Type*}
    (P : (FractionRing (MvPolynomial σ (ZMod 2)))[X])
    (b₀ b₁ : FractionRing (MvPolynomial σ (ZMod 2))) (u v i j : ℕ)
    (h0 : P.coeff 0 ≠ 0) (hd : 0 < P.natDegree)
    (hb₁ : b₁ ≠ 0) (huv : u < v)
    (hdiv : P ∣ monomial u b₀ + monomial v b₁)
    (hij : i < j) (hjd : j < P.natDegree)
    (hci : P.coeff i ≠ 0) (hcj : P.coeff j ≠ 0) :
    (P.coeff i) ^ (P.natDegree - j) * P.leadingCoeff ^ (j - i) =
      (P.coeff j) ^ (P.natDegree - i) := by
  letI : CharP (FractionRing (MvPolynomial σ (ZMod 2))) 2 :=
    IsFractionRing.charP_of_isFractionRing (MvPolynomial σ (ZMod 2)) 2
  have hP : P ≠ 0 := fun hz => h0 (by simp [hz])
  have hlc := leadingCoeff_ne_zero.mpr hP
  have halg := binomial_coefficient_ratio_algebraic_field P b₀ b₁ u v i j
    h0 hd hb₁ huv hdiv hij hjd hci hcj
  have hne : (P.coeff i) ^ (P.natDegree - j) * P.leadingCoeff ^ (j - i) /
      (P.coeff j) ^ (P.natDegree - i) ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero _ hci) (pow_ne_zero _ hlc)) (pow_ne_zero _ hcj)
  have heq := TwoRowConstants.algebraic_fraction_eq_one _ halg hne
  exact (div_eq_one_iff_eq (pow_ne_zero _ hcj)).mp heq

/-- Failure of the general coefficient identity forces at least three rows. -/
theorem general_three_le_rows {σ : Type*}
    (P : (MvPolynomial σ (ZMod 2))[X]) (i j : ℕ)
    (h0 : P.coeff 0 ≠ 0) (hij : i < j) (hjd : j < P.natDegree)
    (hci : P.coeff i ≠ 0) (hcj : P.coeff j ≠ 0)
    (hobs : (P.coeff i) ^ (P.natDegree - j) * P.leadingCoeff ^ (j - i) ≠
      (P.coeff j) ^ (P.natDegree - i))
    (H : (MvPolynomial σ (ZMod 2))[X]) (hH : H ≠ 0) :
    3 ≤ (P * H).support.card := by
  let R := MvPolynomial σ (ZMod 2)
  let K := FractionRing R
  let f := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  have hP : P ≠ 0 := fun hz => h0 (by simp [hz])
  have hQ := mul_ne_zero hP hH
  by_contra hcard
  obtain ⟨u, v, b₀, b₁, huv, hb₁, hdiv⟩ :=
    exists_binomial_multiple_of_support_le_two P (P * H) hQ (dvd_mul_right _ _) (by omega)
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
    dsimp [f, R, K] at hm ⊢
    simpa only [Polynomial.map_add, Polynomial.map_monomial] using hm
  have heq := general_binomial_identity (P.map f) (f b₀) (f b₁) u v i j
    h0' (by rw [hdeg]; omega) hb₁' huv hdiv' hij (by rwa [hdeg]) hci' hcj'
  apply hobs
  apply hf
  simpa only [coeff_map, hdeg, leadingCoeff_map' hf, map_mul, map_pow] using heq

/-- The top-three-coefficient specialization used by the `B_n` table. -/
theorem top_three_le_rows {σ : Type*}
    (P : (MvPolynomial σ (ZMod 2))[X]) (hd : 2 ≤ P.natDegree)
    (h0 : P.coeff 0 ≠ 0) (hlow : P.coeff (P.natDegree - 2) ≠ 0)
    (hmid : P.coeff (P.natDegree - 1) ≠ 0)
    (hobs : P.coeff (P.natDegree - 2) * P.leadingCoeff ≠
      P.coeff (P.natDegree - 1) ^ 2)
    (H : (MvPolynomial σ (ZMod 2))[X]) (hH : H ≠ 0) :
    3 ≤ (P * H).support.card := by
  have h1 : P.natDegree - (P.natDegree - 1) = 1 := by omega
  have h2 : (P.natDegree - 1) - (P.natDegree - 2) = 1 := by omega
  have h3 : P.natDegree - (P.natDegree - 2) = 2 := by omega
  apply general_three_le_rows P (P.natDegree - 2) (P.natDegree - 1) h0
    (by omega) (by omega) hlow hmid ?_ H hH
  simpa only [h1, h2, h3, pow_one] using hobs

end Pilz.TwoRow
