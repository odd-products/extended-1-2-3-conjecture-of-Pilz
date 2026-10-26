import WeightedPilz.Compression

/-!
Pair-block support operations for scalar compression. The coefficient-level
stability conclusions apply over the original field and its formal parameter
ring, with no assumption that the field is infinite.
-/

noncomputable section

namespace WeightedPilz.Compression

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [DecidableEq σ]

/-- The monomial coordinate indexed by its first exponent in a pair block. -/
def pairExponent (i j : σ) (b : σ →₀ ℕ) (d : ℕ) (a : Fin (d + 1)) : σ →₀ ℕ :=
  b + Finsupp.single i a.val + Finsupp.single j (d - a.val)

/-- Occupied first exponents in one pair block of a finite support. -/
def pairIndices (S : Finset (σ →₀ ℕ)) (i j : σ) (b : σ →₀ ℕ) (d : ℕ) :
    Finset (Fin (d + 1)) :=
  Finset.univ.filter (fun a ↦ pairExponent i j b d a ∈ S)

@[simp] theorem mem_pairIndices (S : Finset (σ →₀ ℕ)) (i j : σ)
    (b : σ →₀ ℕ) (d : ℕ) (a : Fin (d + 1)) :
    a ∈ pairIndices S i j b d ↔ pairExponent i j b d a ∈ S := by
  simp [pairIndices]

/-- The explicit characteristic-sensitive condition for a support to be
preserved by a pair transvection and by its balanced version. -/
def PairStable [CommRing K] (S : Finset (σ →₀ ℕ)) (i j : σ) : Prop :=
  ∀ e ∈ S, ∀ k ≤ e j, ((e j).choose k : K) ≠ 0 →
    pairBase i j e + Finsupp.single i (e i + k) + Finsupp.single j (e j - k) ∈ S

section Field
variable [Field K]

/-- A support is fixed blockwise by the pivot operation. -/
def PairBlocksFixed (S : Finset (σ →₀ ℕ)) (i j : σ) : Prop :=
  ∀ b d, b i = 0 → b j = 0 →
    SupportShift.shiftedSupport (K := K) d (pairIndices S i j b d) =
    pairIndices S i j b d

theorem pairStable_of_pairBlocksFixed (S : Finset (σ →₀ ℕ)) (i j : σ)
    (hij : i ≠ j) (hfixed : PairBlocksFixed (K := K) S i j) :
    PairStable (K := K) S i j := by
  intro e he k hk hc
  let d := e i + e j
  let a : Fin (d + 1) := ⟨e i, by dsimp [d]; omega⟩
  let q : Fin (d + 1) := ⟨e i + k, by dsimp [d]; omega⟩
  let b := pairBase i j e
  let A := pairIndices S i j b d
  have ha : a ∈ A := by
    apply (mem_pairIndices S i j b d a).2
    simpa only [pairExponent, b, d, a, Nat.add_sub_cancel_left,
      pairBase_reconstruct i j hij e] using he
  have haq : a ≤ q := by change e i ≤ e i + k; omega
  have hcoeff : SupportShift.shiftMatrix (K := K) d a q ≠ 0 := by
    simpa [SupportShift.shiftMatrix, haq, d, a, q] using hc
  have hq : q ∈ A := by
    by_contra hn
    exact hcoeff (SupportShift.columns_supported_of_pivots_eq A
      (SupportShift.shiftMatrix (K := K) d) (by simp)
      (SupportShift.shiftMatrix_below d)
      (hfixed b d (pairBase_left i j e) (pairBase_right i j e)) a ha q hn)
  have hmem := (mem_pairIndices S i j b d q).1 hq
  have hd : e i + e j - (e i + k) = e j - k := by omega
  simpa [pairExponent, b, d, q, hd] using hmem

end Field

section Ring
variable [CommRing K]

theorem pairStable_map {L : Type*} [CommRing L] (f : K →+* L)
    (S : Finset (σ →₀ ℕ)) (i j : σ) (hstable : PairStable (K := K) S i j) :
    PairStable (K := L) S i j := by
  intro e he k hk hc
  apply hstable e he k hk
  intro hz
  apply hc
  simpa only [map_natCast, map_zero] using congrArg f hz

theorem balancedMap_monomial_support_subset (S : Finset (σ →₀ ℕ))
    (i j : σ) (hij : i ≠ j) (hstable : PairStable (K := K) S i j)
    (s : K) (e : σ →₀ ℕ) (he : e ∈ S) (c : K) :
    (balancedMap i j s (monomial e c)).support ⊆ S := by
  rw [balancedMap_monomial i j hij]
  intro m hm
  obtain ⟨k, hk, hm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have hme := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
  subst m
  have hc : c * s ^ e i * (1 - s) ^ k * ((e j).choose k : K) ≠ 0 := by
    simpa only [MvPolynomial.coeff_monomial, if_pos rfl] using
      (MvPolynomial.mem_support_iff.mp hm)
  exact hstable e he k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)
    (fun hz ↦ hc (by rw [hz, mul_zero]))

/-- Fixed pair blocks preserve the whole coordinate span, for every scaling
parameter in the coefficient ring. -/
theorem balancedMap_support_subset (S : Finset (σ →₀ ℕ))
    (i j : σ) (hij : i ≠ j) (hstable : PairStable (K := K) S i j)
    (s : K) (Q : MvPolynomial σ K) (hQ : Q.support ⊆ S) :
    (balancedMap i j s Q).support ⊆ S := by
  have hmap : balancedMap i j s Q =
      ∑ e ∈ Q.support, balancedMap i j s (monomial e (coeff e Q)) := by
    rw [← map_sum, ← Q.as_sum]
  rw [hmap]
  intro m hm
  obtain ⟨e, he, hm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  exact balancedMap_monomial_support_subset S i j hij hstable s e (hQ he) _ hm

end Ring

section Parameter
variable [Field K]

theorem formalBalanced_support_subset (S : Finset (σ →₀ ℕ))
    (i j : σ) (hij : i ≠ j) (hstable : PairStable (K := K) S i j)
    (Q : MvPolynomial σ K) (hQ : Q.support ⊆ S) :
    (formalBalanced i j Q).support ⊆ S := by
  apply balancedMap_support_subset S i j hij (pairStable_map Polynomial.C S i j hstable)
  exact Finset.Subset.trans (MvPolynomial.support_map_subset Polynomial.C Q) hQ

/-- The closure interface used by the aggregate-coordinate extraction step. -/
theorem parameterCoeff_formalBalanced_support_subset (S : Finset (σ →₀ ℕ))
    (i j : σ) (hij : i ≠ j) (hstable : PairStable (K := K) S i j)
    (Q : MvPolynomial σ K) (hQ : Q.support ⊆ S) (m : ℕ) :
    (parameterCoeff m (formalBalanced i j Q)).support ⊆ S :=
  Finset.Subset.trans (support_coeffProject_subset (Polynomial.lcoeff K m) _)
    (formalBalanced_support_subset S i j hij hstable Q hQ)

end Parameter

end WeightedPilz.Compression
