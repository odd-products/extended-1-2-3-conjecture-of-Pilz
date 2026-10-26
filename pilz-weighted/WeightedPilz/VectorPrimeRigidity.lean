import WeightedPilz.PrimeLaurentRigidity
import WeightedPilz.VectorPolynomial
import WeightedPilz.RankOneCoefficients

/-! Vector-valued Laurent equality at a prime index. Scalar interval lower
bounds are explicit dependencies until the field theorem is assembled. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def vectorToLaurent (Q : (ℕ →₀ ℕ) →₀ V) : (ℕ →₀ ℤ) →₀ V :=
  Finsupp.mapDomain integerExponent Q

theorem vectorToLaurent_exponents_nonnegative (Q : (ℕ →₀ ℕ) →₀ V)
    {d : ℕ →₀ ℤ} (hd : d ∈ (vectorToLaurent Q).support) : ∀ i, 0 ≤ d i := by
  rw [vectorToLaurent, Finsupp.mapDomain_support_of_injective integerExponent_injective] at hd
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hd
  intro i
  exact Int.natCast_nonneg (a i)

theorem laurent_single_pow_exponent_mem_support (P : Poly K)
    (h0 : coeff 0 P ≠ 0) (n : ℕ) (d : ℕ →₀ ℤ) :
    d ∈ (AddMonoidAlgebra.single d (1 : K) * (toLaurent P) ^ n).support := by
  have h0pow : coeff 0 (P ^ n) ≠ 0 := by
    rw [← constantCoeff_eq, map_pow, constantCoeff_eq]
    exact pow_ne_zero n h0
  have hzero : (0 : ℕ →₀ ℤ) ∈ (toLaurent (P ^ n)).support := by
    rw [support_toLaurent]
    exact Finset.mem_image.mpr ⟨0, MvPolynomial.mem_support_iff.mpr h0pow, by simp⟩
  rw [← map_pow, AddMonoidAlgebra.support_single_mul _ 1 (by simp) d]
  exact Finset.mem_map.mpr ⟨0, hzero, by simp⟩

/-- The exact vector-valued Laurent classification from
`cor:prime-rigidity` / `cor:vector-prime-rigidity`. The monomial coefficient
has been absorbed into the nonzero vector. -/
theorem vector_prime_laurent_rigidity_of_interval_bounds
    (p ℓ : ℕ) [ExpChar K p] (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ)
    (c : ℕ → K) (hc : NonzeroWeights ℓ c)
    (hprev : IntervalBound (ℓ - 1) c) (hfield : IntervalBound ℓ c)
    (H : (ℕ →₀ ℤ) →₀ V)
    (hw : (vectorMul (toLaurent (interval ℓ c)) H).support.card = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℤ) (v : V), v ≠ 0 ∧
      vectorMul (toLaurent (interval ℓ c)) H =
        coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) *
          (toLaurent (interval ℓ c)) ^ p ^ e) ∧
      H = coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) *
          (toLaurent (interval ℓ c)) ^ (p ^ e - 1)) ∧
      ((∀ a ∈ (vectorMul (toLaurent (interval ℓ c)) H).support, ∀ i, 0 ≤ a i) →
        ∀ i, 0 ≤ d i) := by
  classical
  let P := interval ℓ c
  let G := vectorMul (toLaurent P) H
  have hP : P ≠ 0 := interval_ne_zero c (by omega) hc
  have hG : G ≠ 0 := by
    intro hz
    change G.support.card = ℓ at hw
    rw [hz, Finsupp.support_zero, Finset.card_empty] at hw
    omega
  have hscalar : ∀ h : LaurentPoly ℕ K, h ≠ 0 →
      ℓ ≤ (toLaurent P * h).support.card :=
    fun h hh ↦ laurent_bound_of_polynomial_bound P ℓ hfield h hh
  have hrank := vectorMul_coefficientRank_bound (toLaurent P) ℓ hscalar H hG
  rw [hw] at hrank
  obtain ⟨v, hv, g, hg, hgsupport, hgform⟩ :=
    exists_mapRange_factor_of_coefficientRank_le_one (K := K) G hG (by
      change Module.finrank K (coefficientSpan (K := K) (vectorMul (toLaurent P) H)) ≤ 1
      omega)
  have hgform' : G = coefficientEmbed v g := hgform
  obtain ⟨φ, hφ⟩ := exists_normalized_dual (K := K) v hv
  let h : LaurentPoly ℕ K := coefficientMap φ H
  have hHform : H = coefficientEmbed v h :=
    vectorMul_factor_of_output_factor (toLaurent P) (toLaurent_mul_left_injective P hP)
      H v φ hφ g hgform'
  have hGform : G = coefficientEmbed v (toLaurent P * h) := by
    change vectorMul (toLaurent P) H = _
    rw [hHform, vectorMul_coefficientEmbed]
  have hh : h ≠ 0 := by
    intro hz
    apply hG
    rw [hGform, hz, mul_zero, map_zero]
  have hweight : (toLaurent P * h).support.card = ℓ := by
    change G.support.card = ℓ at hw
    rwa [hGform, support_coefficientEmbed v hv] at hw
  obtain ⟨e, d, a, ha, houtput, hcofactor⟩ :=
    prime_interval_laurent_rigidity_of_predecessor_bound p ℓ hℓ hthree c hc hprev h hh hweight
  have hav : a • v ≠ 0 := smul_ne_zero ha hv
  have hfinal : G = coefficientEmbed (a • v)
      (AddMonoidAlgebra.single d (1 : K) * (toLaurent P) ^ p ^ e) := by
    rw [hGform, houtput, coefficientEmbed_single_mul]
  refine ⟨e, d, a • v, hav, hfinal, ?_, ?_⟩
  · rw [hHform, hcofactor, coefficientEmbed_single_mul]
  · intro hnonnegative
    apply hnonnegative d
    change d ∈ G.support
    rw [hfinal, support_coefficientEmbed _ hav]
    apply laurent_single_pow_exponent_mem_support P
    have hc1 : c 1 ≠ 0 := hc 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    have hconst := coeff_interval ℓ c (a := 1) (by omega)
    simp only [Nat.factorization_one, if_pos (show 1 ≤ ℓ by omega)] at hconst
    rw [hconst]
    exact hc1

/-- Polynomial outputs force nonnegative exponents in the Laurent monomial. -/
theorem vector_prime_polynomial_output_rigidity_of_interval_bounds
    (p ℓ : ℕ) [ExpChar K p] (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ)
    (c : ℕ → K) (hc : NonzeroWeights ℓ c)
    (hprev : IntervalBound (ℓ - 1) c) (hfield : IntervalBound ℓ c)
    (H : (ℕ →₀ ℤ) →₀ V) (Q : (ℕ →₀ ℕ) →₀ V)
    (hQ : vectorMul (toLaurent (interval ℓ c)) H = vectorToLaurent Q)
    (hw : (vectorMul (toLaurent (interval ℓ c)) H).support.card = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℤ) (v : V), v ≠ 0 ∧ (∀ i, 0 ≤ d i) ∧
      vectorMul (toLaurent (interval ℓ c)) H =
        coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) *
          (toLaurent (interval ℓ c)) ^ p ^ e) ∧
      H = coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) *
          (toLaurent (interval ℓ c)) ^ (p ^ e - 1)) := by
  obtain ⟨e, d, v, hv, hg, hh, hnonneg⟩ :=
    vector_prime_laurent_rigidity_of_interval_bounds p ℓ hℓ hthree c hc hprev hfield H hw
  refine ⟨e, d, v, hv, hnonneg ?_, hg, hh⟩
  intro a ha
  rw [hQ] at ha
  exact vectorToLaurent_exponents_nonnegative Q ha

end WeightedPilz
