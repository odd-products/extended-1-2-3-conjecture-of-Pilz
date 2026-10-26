import WeightedPilz.CompressionAction
import WeightedPilz.CompressionTransition

/-! Admissibility of the simultaneous pair-block pivot operation, proved by
extracting the highest coefficient of the genuine balanced substitution. -/

noncomputable section

namespace WeightedPilz.Compression

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [DecidableEq σ] [Field K]

def pairDeformation (S : Finset (σ →₀ ℕ)) (i j : σ) (G : MvPolynomial σ K)
    (q : (σ →₀ ℕ) × ℕ) (a : Fin (q.2 + 1)) : Polynomial K :=
  SupportShift.deform (pairIndices S i j q.1 q.2)
    (SupportShift.shiftMatrix (K := K) q.2)
    (fun k ↦ Polynomial.C (coeff (pairExponent i j q.1 q.2 k) G) *
      (1 - Polynomial.X) ^ k.val) a

theorem formalBalanced_eq_pairDeformation (S : Finset (σ →₀ ℕ))
    (i j : σ) (hij : i ≠ j) (G : MvPolynomial σ K) (hG : G.support ⊆ S) :
    formalBalanced i j G = ∑ q ∈ pairKeys S i j,
      ∑ a : Fin (q.2 + 1), monomial (pairExponent i j q.1 q.2 a)
        (pairDeformation S i j G q a) := by
  conv_lhs => rw [eq_sum_pairIndices S i j hij G hG]
  rw [formalBalanced_sum]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hqi, hqj⟩ := pairKeys_base_zero S i j hq
  exact formalBalanced_pair_block i j hij q.1 hqi hqj q.2 _ _

theorem coeff_formalBalanced_pairExponent (S : Finset (σ →₀ ℕ))
    (i j : σ) (hij : i ≠ j) (G : MvPolynomial σ K) (hG : G.support ⊆ S)
    {q : (σ →₀ ℕ) × ℕ} (hq : q ∈ pairKeys S i j) (a : Fin (q.2 + 1)) :
    coeff (pairExponent i j q.1 q.2 a) (formalBalanced i j G) =
      pairDeformation S i j G q a := by
  rw [formalBalanced_eq_pairDeformation S i j hij G hG]
  exact coeff_sum_pairBlocks (pairKeys S i j) i j hij
    (fun q hq ↦ pairKeys_base_zero S i j hq) (pairDeformation S i j G) hq a

theorem pairDeformation_natDegree_le (S : Finset (σ →₀ ℕ))
    (i j : σ) (hij : i ≠ j) (G : MvPolynomial σ K) (hG : G.support ⊆ S)
    {q : (σ →₀ ℕ) × ℕ} (hq : q ∈ pairKeys S i j) (a : Fin (q.2 + 1)) :
    (pairDeformation S i j G q a).natDegree ≤ parameterDegree (formalBalanced i j G) := by
  rw [← coeff_formalBalanced_pairExponent S i j hij G hG hq a]
  exact coeff_natDegree_le_parameterDegree _ _

/-- The highest coefficient of the simultaneous balanced substitution is
supported on the simultaneously shifted coordinate set. -/
theorem highest_formalBalanced_support_subset (S : Finset (σ →₀ ℕ))
    (i j : σ) (hij : i ≠ j) (G : MvPolynomial σ K) (hG : G.support ⊆ S) :
    (parameterCoeff (parameterDegree (formalBalanced i j G))
      (formalBalanced i j G)).support ⊆ pairShift (K := K) S i j := by
  intro m hm
  have hm0 : m ∈ (formalBalanced i j G).support :=
    support_coeffProject_subset (Polynomial.lcoeff K _) _ hm
  rw [formalBalanced_eq_pairDeformation S i j hij G hG] at hm0
  obtain ⟨q, hq, hmq⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm0)
  obtain ⟨a, ha, hma⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmq)
  have hme := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hma)
  subst m
  have hc : (pairDeformation S i j G q a).coeff
      (parameterDegree (formalBalanced i j G)) ≠ 0 := by
    have h := MvPolynomial.mem_support_iff.mp hm
    simpa only [coeff_parameterCoeff,
      coeff_formalBalanced_pairExponent S i j hij G hG hq a] using h
  have ha' : a ∈ SupportShift.shiftedSupport (K := K) q.2
      (pairIndices S i j q.1 q.2) :=
    SupportShift.shift_highest_coeff (pairIndices S i j q.1 q.2)
      (fun k ↦ Polynomial.C (coeff (pairExponent i j q.1 q.2 k) G) *
        (1 - Polynomial.X) ^ k.val) (parameterDegree (formalBalanced i j G))
      (fun k ↦ pairDeformation_natDegree_le S i j hij G hG hq k) a hc
  exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_image.mpr ⟨a, ha', rfl⟩⟩

/-- Every admissible coordinate support stays admissible after all its pair
blocks are pivot-shifted. The witness stays over the original field. -/
theorem pairShift_admissible (F : WeightedPilz.FreshData σ K)
    (S : Finset (σ →₀ ℕ)) (i j : σ) (hi : i ∈ F.vars) (hj : j ∈ F.vars)
    (hij : i ≠ j) (hS : admissible F.F S) :
    admissible F.F (pairShift (K := K) S i j) := by
  obtain ⟨G, hG, hdiv, hGS⟩ := hS
  obtain ⟨hne, hdvd⟩ := formalBalanced_highest_multiple F i j hi hj hij G hG hdiv
  exact ⟨_, hne, hdvd, highest_formalBalanced_support_subset S i j hij G hGS⟩

/-- The scalar-compression version for an arbitrary fresh-independent base
polynomial, including the zero polynomial. -/
theorem pairShift_admissible_of_fresh (V : Finset σ) (C₀ : MvPolynomial σ K)
    (hind : ∀ k ∈ V, k ∉ C₀.vars)
    (S : Finset (σ →₀ ℕ)) (i j : σ) (hi : i ∈ V) (hj : j ∈ V)
    (hij : i ≠ j) (hS : admissible (C₀ + ∑ k ∈ V, X k) S) :
    admissible (C₀ + ∑ k ∈ V, X k) (pairShift (K := K) S i j) := by
  obtain ⟨G, hG, hdiv, hGS⟩ := hS
  obtain ⟨hne, hdvd⟩ := formalBalanced_highest_multiple_of_fixed
    (C₀ + ∑ k ∈ V, X k) i j
    (formalBalanced_core_sum V C₀ i j hi hj hij (hind i hi) (hind j hj)) G hG hdiv
  exact ⟨_, hne, hdvd, highest_formalBalanced_support_subset S i j hij G hGS⟩

end WeightedPilz.Compression
