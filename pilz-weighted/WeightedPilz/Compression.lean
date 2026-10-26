import WeightedPilz.Fresh
import WeightedPilz.SupportShift
import WeightedPilz.CoefficientExtension
import Mathlib.Algebra.MvPolynomial.Variables

/-!
The balanced changes of fresh variables used in `thm:compression`.
The map sends `x_i` to `s*x_i` and `x_j` to `x_j+(1-s)*x_i`.
At `s=1-t` this is exactly the manuscript's `T_t D_t`, preserving
the completed polynomial and hence its principal ideal.

The finite profile maximization and coefficient extraction are proved in
the subsequent compression modules; `ScalarCompression.lean` assembles the
full scalar support compression theorem over the original field.
-/

noncomputable section

namespace WeightedPilz.Compression

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [DecidableEq σ]

section Ring
variable [CommRing K]

/-- The balanced upper change of two variables. -/
def balancedMap (i j : σ) (s : K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval (fun k ↦ if k = i then C s * X i
    else if k = j then X j + C (1 - s) * X i else X k)

@[simp] theorem balancedMap_X_left (i j : σ) (s : K) :
    balancedMap i j s (X i) = C s * X i := by simp [balancedMap]

@[simp] theorem balancedMap_X_right (i j : σ) (hij : i ≠ j) (s : K) :
    balancedMap i j s (X j) = X j + C (1 - s) * X i := by
  simp [balancedMap, Ne.symm hij]

theorem balancedMap_X_other (i j k : σ) (hki : k ≠ i) (hkj : k ≠ j) (s : K) :
    balancedMap i j s (X k) = X k := by simp [balancedMap, hki, hkj]

@[simp] theorem balancedMap_C (i j : σ) (s c : K) :
    balancedMap i j s (C c) = C c := by simp [balancedMap]

theorem balancedMap_comp (i j : σ) (hij : i ≠ j) (s u : K) :
    (balancedMap i j s).comp (balancedMap i j u) = balancedMap i j (s * u) := by
  apply MvPolynomial.algHom_ext
  intro k
  by_cases hki : k = i
  · subst k
    simp [AlgHom.comp_apply, map_mul, mul_comm, mul_left_comm]
  · by_cases hkj : k = j
    · subst k
      simp only [AlgHom.comp_apply, balancedMap_X_right i j hij, map_add, map_mul,
        balancedMap_C, balancedMap_X_left, map_sub, map_one]
      ring
    · simp [AlgHom.comp_apply, balancedMap_X_other i j k hki hkj]

@[simp] theorem balancedMap_one (i j : σ) :
    balancedMap i j (1 : K) = AlgHom.id K (MvPolynomial σ K) := by
  apply MvPolynomial.algHom_ext
  intro k
  by_cases hki : k = i
  · subst k
    simp
  · by_cases hkj : k = j
    · subst k
      simp [balancedMap, hki]
    · simp [balancedMap, hki, hkj]

end Ring

section Field
variable [Field K]

/-- Every nonzero scaling parameter gives an actual polynomial automorphism. -/
def balancedEquiv (i j : σ) (hij : i ≠ j) (s : K) (hs : s ≠ 0) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (balancedMap i j s) (balancedMap i j s⁻¹)
    (by rw [balancedMap_comp i j hij, mul_inv_cancel₀ hs, balancedMap_one])
    (by rw [balancedMap_comp i j hij, inv_mul_cancel₀ hs, balancedMap_one])

theorem balancedMap_injective (i j : σ) (hij : i ≠ j) (s : K) (hs : s ≠ 0) :
    Function.Injective (balancedMap i j s) :=
  (balancedEquiv i j hij s hs).injective

end Field

section Ring
variable [CommRing K]

/-- A polynomial independent of both changed variables is fixed. -/
theorem balancedMap_eq_self (i j : σ) (s : K) (Q : MvPolynomial σ K)
    (hi : i ∉ Q.vars) (hj : j ∉ Q.vars) : balancedMap i j s Q = Q := by
  change (balancedMap i j s).toRingHom Q = (RingHom.id (MvPolynomial σ K)) Q
  apply MvPolynomial.hom_congr_vars
  · ext c
    simp
  · intro k hk _
    have hki : k ≠ i := fun h ↦ hi (h ▸ hk)
    have hkj : k ≠ j := fun h ↦ hj (h ▸ hk)
    exact balancedMap_X_other i j k hki hkj s
  · rfl

/-- The sum of the two changed fresh variables is fixed. -/
theorem balancedMap_pair (i j : σ) (hij : i ≠ j) (s : K) :
    balancedMap i j s (X i + X j) = X i + X j := by
  simp only [map_add, balancedMap_X_left, balancedMap_X_right i j hij, map_sub, map_one]
  ring

/-- A sum of fresh variables is fixed whenever it contains both changed ones. -/
theorem balancedMap_sum (V : Finset σ) (i j : σ) (hi : i ∈ V) (hj : j ∈ V)
    (hij : i ≠ j) (s : K) :
    balancedMap i j s (∑ k ∈ V, X k) = ∑ k ∈ V, X k := by
  have hj' : j ∈ V.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hdecomp : (∑ k ∈ V, (X k : MvPolynomial σ K)) =
      (X i + X j) + ∑ k ∈ (V.erase i).erase j, X k := by
    rw [← Finset.add_sum_erase V (fun k ↦ (X k : MvPolynomial σ K)) hi,
      ← Finset.add_sum_erase (V.erase i) (fun k ↦ (X k : MvPolynomial σ K)) hj']
    exact (add_assoc _ _ _).symm
  rw [hdecomp, map_add, balancedMap_pair i j hij, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  exact balancedMap_X_other i j k hki hkj s

/-- Balanced substitution commutes with coefficient homomorphisms. -/
theorem map_balancedMap {L : Type*} [CommRing L] (f : K →+* L)
    (i j : σ) (s : K) (Q : MvPolynomial σ K) :
    MvPolynomial.map f (balancedMap i j s Q) =
      balancedMap i j (f s) (MvPolynomial.map f Q) := by
  have heq : (MvPolynomial.map f).comp (balancedMap i j s).toRingHom =
      (balancedMap i j (f s)).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro k
      by_cases hki : k = i
      · subst k
        simp
      · by_cases hkj : k = j
        · subst k
          simp [balancedMap, hki]
        · simp [balancedMap, hki, hkj]
  exact RingHom.congr_fun heq Q

end Ring

section PairExpansion
variable [CommRing K]

/-- The exponent vector outside the two variables being shifted. -/
def pairBase (i j : σ) (e : σ →₀ ℕ) : σ →₀ ℕ := (e.erase i).erase j

@[simp] theorem pairBase_left (i j : σ) (e : σ →₀ ℕ) : pairBase i j e i = 0 := by
  simp [pairBase, Finsupp.erase_apply]

@[simp] theorem pairBase_right (i j : σ) (e : σ →₀ ℕ) : pairBase i j e j = 0 := by
  simp [pairBase]

theorem pairBase_reconstruct (i j : σ) (hij : i ≠ j) (e : σ →₀ ℕ) :
    pairBase i j e + Finsupp.single i (e i) + Finsupp.single j (e j) = e := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [pairBase, hij]
  · by_cases hkj : k = j
    · subst k
      simp [pairBase, Ne.symm hij]
    · simp [pairBase, hki, hkj]

theorem balancedMap_monomial_fixed (i j : σ) (s : K) (e : σ →₀ ℕ) (c : K)
    (hi : e i = 0) (hj : e j = 0) :
    balancedMap i j s (monomial e c) = monomial e c := by
  by_cases hc : c = 0
  · simp [hc]
  · apply balancedMap_eq_self
    · simpa [MvPolynomial.vars_monomial hc, Finsupp.mem_support_iff] using hi
    · simpa [MvPolynomial.vars_monomial hc, Finsupp.mem_support_iff] using hj

/-- Exact binomial expansion of a pair block. This formula retains every
coefficient in arbitrary characteristic, including vanished binomial terms. -/
theorem balancedMap_monomial_pair (i j : σ) (hij : i ≠ j) (s : K)
    (e : σ →₀ ℕ) (hi : e i = 0) (hj : e j = 0) (a b : ℕ) (c : K) :
    balancedMap i j s (monomial (e + Finsupp.single i a + Finsupp.single j b) c) =
      ∑ k ∈ Finset.range (b + 1),
        monomial (e + Finsupp.single i (a + k) + Finsupp.single j (b - k))
          (c * s ^ a * (1 - s) ^ k * (b.choose k : K)) := by
  simp only [monomial_add_single, map_mul, map_pow,
    balancedMap_monomial_fixed i j s e c hi hj, balancedMap_X_left,
    balancedMap_X_right i j hij]
  rw [add_comm (X j), add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show monomial e c = C c * monomial e (1 : K) by rw [C_mul_monomial, mul_one]]
  rw [show monomial e (c * s ^ a * (1 - s) ^ k * (b.choose k : K)) =
    C (c * s ^ a * (1 - s) ^ k * (b.choose k : K)) * monomial e (1 : K) by
      rw [C_mul_monomial, mul_one]]
  simp only [mul_pow, map_mul, map_pow, map_natCast, pow_add]
  ring

/-- The binomial formula for an arbitrary monomial, without an independence
assumption on its exponent vector. -/
theorem balancedMap_monomial (i j : σ) (hij : i ≠ j) (s : K)
    (e : σ →₀ ℕ) (c : K) :
    balancedMap i j s (monomial e c) =
      ∑ k ∈ Finset.range (e j + 1),
        monomial (pairBase i j e + Finsupp.single i (e i + k) +
          Finsupp.single j (e j - k))
          (c * s ^ (e i) * (1 - s) ^ k * ((e j).choose k : K)) := by
  conv_lhs => rw [← pairBase_reconstruct i j hij e]
  exact balancedMap_monomial_pair i j hij s _ (pairBase_left i j e)
    (pairBase_right i j e) (e i) (e j) c

end PairExpansion

section Parameter
variable [Field K]

/-- Perform the balanced substitution with the formal parameter `s=1-t`.
The parameter stays in the coefficient polynomial ring. -/
def formalBalanced (i j : σ) (G : MvPolynomial σ K) :
    MvPolynomial σ (Polynomial K) :=
  balancedMap i j (1 - Polynomial.X) (MvPolynomial.map Polynomial.C G)

/-- At parameter zero the balanced substitution is the identity. -/
theorem formalBalanced_specialize_zero (i j : σ) (G : MvPolynomial σ K) :
    MvPolynomial.map (Polynomial.evalRingHom (0 : K)) (formalBalanced i j G) = G := by
  unfold formalBalanced
  rw [map_balancedMap]
  simp only [map_sub, map_one, Polynomial.coe_evalRingHom, Polynomial.eval_X,
    sub_zero, balancedMap_one, AlgHom.id_apply]
  rw [MvPolynomial.map_map]
  have hc : (Polynomial.evalRingHom (0 : K)).comp Polynomial.C = RingHom.id K := by
    ext c
    simp
  rw [hc, MvPolynomial.map_id]

theorem formalBalanced_ne_zero (i j : σ) (G : MvPolynomial σ K) (hG : G ≠ 0) :
    formalBalanced i j G ≠ 0 := by
  intro hz
  have h := formalBalanced_specialize_zero i j G
  rw [hz, map_zero] at h
  exact hG h.symm

/-- Extract one coefficient of the formal parameter, leaving all monomial
coordinates in the original variables intact. -/
def parameterCoeff (m : ℕ) (Q : MvPolynomial σ (Polynomial K)) : MvPolynomial σ K :=
  coeffProject (Polynomial.lcoeff K m) Q

@[simp] theorem coeff_parameterCoeff (m : ℕ) (Q : MvPolynomial σ (Polynomial K))
    (e : σ →₀ ℕ) : coeff e (parameterCoeff m Q) = (coeff e Q).coeff m := rfl

/-- Common upper parameter degree across the finite monomial support. -/
def parameterDegree (Q : MvPolynomial σ (Polynomial K)) : ℕ :=
  Q.support.sup (fun e ↦ (coeff e Q).natDegree)

theorem coeff_natDegree_le_parameterDegree (Q : MvPolynomial σ (Polynomial K))
    (e : σ →₀ ℕ) : (coeff e Q).natDegree ≤ parameterDegree Q := by
  by_cases he : e ∈ Q.support
  · exact Finset.le_sup (f := fun e ↦ (coeff e Q).natDegree) he
  · rw [MvPolynomial.notMem_support_iff.mp he, Polynomial.natDegree_zero]
    exact Nat.zero_le _

/-- A nonzero parameter polynomial vector has a nonzero highest coefficient. -/
theorem highest_parameterCoeff_ne_zero (Q : MvPolynomial σ (Polynomial K)) (hQ : Q ≠ 0) :
    parameterCoeff (parameterDegree Q) Q ≠ 0 := by
  obtain ⟨e, he, hD⟩ := Finset.sup_mem_of_nonempty (f := fun e ↦ (coeff e Q).natDegree)
    (MvPolynomial.support_nonempty.mpr hQ)
  intro hz
  have h := congrArg (MvPolynomial.coeff e) hz
  simp only [coeff_parameterCoeff, MvPolynomial.coeff_zero] at h
  change (coeff e Q).natDegree = parameterDegree Q at hD
  rw [← hD, Polynomial.coeff_natDegree] at h
  exact (Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp he)) h

/-- Parameter extraction commutes with the original-field polynomial factor. -/
theorem parameterCoeff_mul_map (m : ℕ) (P : MvPolynomial σ K)
    (H : MvPolynomial σ (Polynomial K)) :
    parameterCoeff m (MvPolynomial.map Polynomial.C P * H) = P * parameterCoeff m H :=
  coeffProject_mul_map (Polynomial.lcoeff K m) P H

/-- Every nonzero multiple over the parameter-polynomial ring has a nonzero
highest-parameter coefficient that is still a multiple over the original field. -/
theorem highest_parameterCoeff_multiple (P : MvPolynomial σ K)
    (Q : MvPolynomial σ (Polynomial K)) (hQ : Q ≠ 0)
    (hdiv : MvPolynomial.map Polynomial.C P ∣ Q) :
    parameterCoeff (parameterDegree Q) Q ≠ 0 ∧
      P ∣ parameterCoeff (parameterDegree Q) Q := by
  refine ⟨highest_parameterCoeff_ne_zero Q hQ, ?_⟩
  obtain ⟨H, hH⟩ := hdiv
  rw [hH, parameterCoeff_mul_map]
  exact dvd_mul_right _ _

end Parameter

section Field
variable [Field K]

/-- Freshness is expressed at support level in `FreshData`; it implies absence
from the multivariate polynomial's variable set. -/
theorem FreshData.not_mem_vars_core (S : WeightedPilz.FreshData σ K)
    {i : σ} (hi : i ∈ S.vars) : i ∉ S.C.vars := by
  intro h
  obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars i).1 h
  exact (Finsupp.mem_support_iff.mp hdi) (S.independent i hi d hd)

/-- The balanced substitution fixes the actual completed polynomial. -/
theorem balancedMap_F (S : WeightedPilz.FreshData σ K) (i j : σ)
    (hi : i ∈ S.vars) (hj : j ∈ S.vars) (hij : i ≠ j) (s : K) :
    balancedMap i j s S.F = S.F := by
  unfold WeightedPilz.FreshData.F
  rw [map_add, balancedMap_eq_self i j s S.C
    (FreshData.not_mem_vars_core S hi) (FreshData.not_mem_vars_core S hj)]
  rw [WeightedPilz.FreshData.freshSum, balancedMap_sum S.vars i j hi hj hij]

/-- The formal balanced substitution fixes the completed polynomial after
coefficient extension to `K[t]`. -/
theorem formalBalanced_F (S : WeightedPilz.FreshData σ K) (i j : σ)
    (hi : i ∈ S.vars) (hj : j ∈ S.vars) (hij : i ≠ j) :
    formalBalanced i j S.F = MvPolynomial.map Polynomial.C S.F := by
  have hiC : i ∉ (MvPolynomial.map Polynomial.C S.C).vars :=
    fun h ↦ FreshData.not_mem_vars_core S hi (MvPolynomial.vars_map S.C Polynomial.C h)
  have hjC : j ∉ (MvPolynomial.map Polynomial.C S.C).vars :=
    fun h ↦ FreshData.not_mem_vars_core S hj (MvPolynomial.vars_map S.C Polynomial.C h)
  unfold formalBalanced WeightedPilz.FreshData.F WeightedPilz.FreshData.freshSum
  rw [map_add, map_sum]
  simp only [MvPolynomial.map_X]
  rw [map_add, balancedMap_eq_self i j (1 - Polynomial.X) _ hiC hjC,
    balancedMap_sum S.vars i j hi hj hij]

/-- Exact product identity for the formal substitution, with the original
completed polynomial as the fixed factor. -/
theorem formalBalanced_mul_F (S : WeightedPilz.FreshData σ K) (i j : σ)
    (hi : i ∈ S.vars) (hj : j ∈ S.vars) (hij : i ≠ j) (H : MvPolynomial σ K) :
    formalBalanced i j (S.F * H) =
      MvPolynomial.map Polynomial.C S.F * formalBalanced i j H := by
  unfold formalBalanced
  rw [map_mul, map_mul]
  exact congrArg (fun Q ↦ Q * balancedMap i j (1 - Polynomial.X)
    (MvPolynomial.map Polynomial.C H)) (formalBalanced_F S i j hi hj hij)

/-- The highest parameter coefficient of the admissibility deformation is a
nonzero multiple over the original field, before applying the support shift. -/
theorem formalBalanced_highest_multiple (S : WeightedPilz.FreshData σ K) (i j : σ)
    (hi : i ∈ S.vars) (hj : j ∈ S.vars) (hij : i ≠ j)
    (G : MvPolynomial σ K) (hG : G ≠ 0) (hdiv : S.F ∣ G) :
    parameterCoeff (parameterDegree (formalBalanced i j G)) (formalBalanced i j G) ≠ 0 ∧
      S.F ∣ parameterCoeff (parameterDegree (formalBalanced i j G)) (formalBalanced i j G) := by
  apply highest_parameterCoeff_multiple S.F _ (formalBalanced_ne_zero i j G hG)
  obtain ⟨H, rfl⟩ := hdiv
  rw [formalBalanced_mul_F S i j hi hj hij]
  exact dvd_mul_right _ _

/-- Admissibility's algebraic component: a nonzero multiple remains a nonzero
multiple after the balanced substitution. -/
theorem balancedMap_multiple (S : WeightedPilz.FreshData σ K) (i j : σ)
    (hi : i ∈ S.vars) (hj : j ∈ S.vars) (hij : i ≠ j) (s : K) (hs : s ≠ 0)
    (G : MvPolynomial σ K) (hG : G ≠ 0) (hdiv : S.F ∣ G) :
    balancedMap i j s G ≠ 0 ∧ S.F ∣ balancedMap i j s G := by
  constructor
  · intro hz
    apply hG
    exact balancedMap_injective i j hij s hs (by simpa only [map_zero] using hz)
  · obtain ⟨H, rfl⟩ := hdiv
    rw [map_mul, balancedMap_F S i j hi hj hij]
    exact dvd_mul_right _ _

end Field

end WeightedPilz.Compression
