import WeightedPilz.CompressionProfiles
import WeightedPilz.CompressionDecomposition
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite pair shifts preserve profile counts and raise the compression potential. -/
noncomputable section
namespace WeightedPilz.Compression
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

def shiftedPairBlock (S : Finset (σ →₀ ℕ)) (i j : σ) (k : (σ →₀ ℕ) × ℕ) :
    Finset (σ →₀ ℕ) :=
  (SupportShift.shiftedSupport (K := K) k.2 (pairIndices S i j k.1 k.2)).image
    (pairExponent i j k.1 k.2)

def pairShift (S : Finset (σ →₀ ℕ)) (i j : σ) : Finset (σ →₀ ℕ) :=
  (pairKeys S i j).biUnion (shiftedPairBlock (K := K) S i j)

theorem shiftedPairBlocks_pairwiseDisjoint (S : Finset (σ →₀ ℕ))
    (i j : σ) (hij : i ≠ j) :
    (pairKeys S i j).toSet.PairwiseDisjoint (shiftedPairBlock (K := K) S i j) := by
  intro k hk l hl hkl
  apply Finset.disjoint_left.mpr
  intro e hek hel
  obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp hek
  obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp hel
  obtain ⟨hki, hkj⟩ := pairKeys_base_zero S i j hk
  obtain ⟨hli, hlj⟩ := pairKeys_base_zero S i j hl
  have hke : pairKey i j e = k := by
    rw [← hea]
    exact pairKey_pairExponent i j hij k.1 hki hkj k.2 a
  have hle : pairKey i j e = l := by
    rw [← heb]
    exact pairKey_pairExponent i j hij l.1 hli hlj l.2 b
  exact hkl (hke.symm.trans hle)

theorem sum_pairShift (S : Finset (σ →₀ ℕ)) (i j : σ) (hij : i ≠ j)
    (f : (σ →₀ ℕ) → ℕ) :
    (∑ e ∈ pairShift (K := K) S i j, f e) =
      ∑ k ∈ pairKeys S i j,
        ∑ a ∈ SupportShift.shiftedSupport (K := K) k.2 (pairIndices S i j k.1 k.2),
          f (pairExponent i j k.1 k.2 a) := by
  rw [pairShift, Finset.sum_biUnion (shiftedPairBlocks_pairwiseDisjoint S i j hij)]
  apply Finset.sum_congr rfl
  intro k hk
  exact Finset.sum_image (fun a ha b hb hab => pairExponent_injective i j hij k.1 k.2 hab)

theorem sum_pairBlocks (S : Finset (σ →₀ ℕ)) (i j : σ) (hij : i ≠ j)
    (f : (σ →₀ ℕ) → ℕ) :
    (∑ e ∈ S, f e) = ∑ k ∈ pairKeys S i j, ∑ a ∈ pairIndices S i j k.1 k.2,
      f (pairExponent i j k.1 k.2 a) := by
  conv_lhs => rw [← pairBlocks_biUnion S i j hij]
  rw [Finset.sum_biUnion (pairBlocks_pairwiseDisjoint S i j hij)]
  apply Finset.sum_congr rfl
  intro k hk
  exact Finset.sum_image (fun a ha b hb hab => pairExponent_injective i j hij k.1 k.2 hab)

theorem pairShift_card (S : Finset (σ →₀ ℕ)) (i j : σ) (hij : i ≠ j) :
    (pairShift (K := K) S i j).card = S.card := by
  rw [pairShift, Finset.card_biUnion (shiftedPairBlocks_pairwiseDisjoint S i j hij),
    card_eq_sum_pairIndices S i j hij]
  apply Finset.sum_congr rfl
  intro k hk
  rw [shiftedPairBlock, Finset.card_image_of_injective _
    (pairExponent_injective i j hij k.1 k.2), SupportShift.shiftedSupport_card]

theorem profile_pairExponent (V : Finset σ) (i j : σ) (hi : i ∈ V) (hj : j ∈ V)
    (b : σ →₀ ℕ) (d : ℕ) (a : Fin (d + 1)) :
    profile V (pairExponent i j b d a) = (baseExponent V b, freshDegree V b + d) := by
  classical
  apply Prod.ext
  · change baseExponent V (pairExponent i j b d a) = _
    ext q
    by_cases hq : q ∈ V
    · simp [baseExponent, Finsupp.filter_apply, hq]
    · have hqi : q ≠ i := fun h => hq (h.symm ▸ hi)
      have hqj : q ≠ j := fun h => hq (h.symm ▸ hj)
      simp [baseExponent, Finsupp.filter_apply, pairExponent, hq, hqi, hqj]
  · change freshDegree V (pairExponent i j b d a) = _
    simp only [freshDegree, pairExponent, Finsupp.add_apply, Finset.sum_add_distrib]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq, hi, hj, if_true]
    have ha := a.isLt
    omega

theorem pairShift_sameProfiles (V : Finset σ) (S : Finset (σ →₀ ℕ))
    (i j : σ) (hi : i ∈ V) (hj : j ∈ V) (hij : i ≠ j) :
    SameProfiles V S (pairShift (K := K) S i j) := by
  classical
  intro p
  have hcount : ∀ T : Finset (σ →₀ ℕ), profileCount V T p =
      ∑ e ∈ T, if profile V e = p then 1 else 0 := by
    intro T
    simp [profileCount]
  rw [hcount, hcount, sum_pairBlocks S i j hij, sum_pairShift S i j hij]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [profile_pairExponent V i j hi hj]
  simp only [Finset.sum_const, smul_eq_mul, SupportShift.shiftedSupport_card]

def pivotWeight (j : σ) (i : σ) : ℕ := if i = j then 0 else 1

theorem pivot_pairExponent (V : Finset σ) (i j : σ) (hi : i ∈ V)
    (hij : i ≠ j) (b : σ →₀ ℕ) (d : ℕ) (a : Fin (d + 1)) :
    (∑ q ∈ V, pivotWeight j q * pairExponent i j b d a q) =
      (∑ q ∈ V, pivotWeight j q * b q) + a.val := by
  classical
  simp only [pairExponent, Finsupp.add_apply, Nat.mul_add, Finset.sum_add_distrib]
  have hfirst : (∑ q ∈ V, pivotWeight j q * Finsupp.single i a.val q) = a.val := by
    simp [pivotWeight, Finsupp.single_apply, hi, hij]
  have hsecond : (∑ q ∈ V, pivotWeight j q * Finsupp.single j (d - a.val) q) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    by_cases hqj : q = j <;> simp [pivotWeight, Finsupp.single_apply, hqj]
  rw [hfirst, hsecond, add_zero]

theorem pivot_potential_pairShift_le (V : Finset σ) (S : Finset (σ →₀ ℕ))
    (i j : σ) (hi : i ∈ V) (hij : i ≠ j) :
    potential V (pivotWeight j) S ≤ potential V (pivotWeight j) (pairShift (K := K) S i j) := by
  classical
  unfold potential
  rw [sum_pairBlocks S i j hij, sum_pairShift S i j hij]
  apply Finset.sum_le_sum
  intro k hk
  simp only [pivot_pairExponent V i j hi hij, Finset.sum_add_distrib,
    Finset.sum_const, smul_eq_mul, SupportShift.shiftedSupport_card]
  apply Nat.add_le_add_left
  by_cases h : SupportShift.shiftedSupport (K := K) k.2 (pairIndices S i j k.1 k.2) =
      pairIndices S i j k.1 k.2
  · rw [h]
  · exact (SupportShift.shiftedSupport_sum_lt _ h).le

theorem pivot_potential_pairShift_lt (V : Finset σ) (S : Finset (σ →₀ ℕ))
    (i j : σ) (hi : i ∈ V) (hij : i ≠ j) (k : (σ →₀ ℕ) × ℕ)
    (hk : k ∈ pairKeys S i j)
    (hne : SupportShift.shiftedSupport (K := K) k.2 (pairIndices S i j k.1 k.2) ≠
      pairIndices S i j k.1 k.2) :
    potential V (pivotWeight j) S < potential V (pivotWeight j) (pairShift (K := K) S i j) := by
  classical
  unfold potential
  rw [sum_pairBlocks S i j hij, sum_pairShift S i j hij]
  apply Finset.sum_lt_sum
  · intro l hl
    simp only [pivot_pairExponent V i j hi hij, Finset.sum_add_distrib,
      Finset.sum_const, smul_eq_mul, SupportShift.shiftedSupport_card]
    apply Nat.add_le_add_left
    by_cases h : SupportShift.shiftedSupport (K := K) l.2 (pairIndices S i j l.1 l.2) =
        pairIndices S i j l.1 l.2
    · rw [h]
    · exact (SupportShift.shiftedSupport_sum_lt _ h).le
  · refine ⟨k, hk, ?_⟩
    simp only [pivot_pairExponent V i j hi hij, Finset.sum_add_distrib,
      Finset.sum_const, smul_eq_mul, SupportShift.shiftedSupport_card]
    exact Nat.add_lt_add_left (SupportShift.shiftedSupport_sum_lt _ hne) _

/-- Maximality forces every canonical block toward the selected pivot to be
fixed. The nonzero-multiple admissibility is supplied by the formal balanced
deformation, separately from this finite combinatorial argument. -/
theorem pairBlocksFixed_of_maximal (V : Finset σ) (witness S : Finset (σ →₀ ℕ))
    (P : MvPolynomial σ K) (i j : σ) (hi : i ∈ V) (hj : j ∈ V) (hij : i ≠ j)
    (hS : SameProfiles V witness S)
    (hmax : ∀ T, SameProfiles V witness T → admissible P T →
      potential V (pivotWeight j) T ≤ potential V (pivotWeight j) S)
    (hadm : admissible P (pairShift (K := K) S i j)) :
    PairBlocksFixed (K := K) S i j := by
  have hprof : SameProfiles V witness (pairShift (K := K) S i j) :=
    fun p => (hS p).trans (pairShift_sameProfiles V S i j hi hj hij p)
  have hle := hmax _ hprof hadm
  intro b d hbi hbj
  by_cases hk : (b, d) ∈ pairKeys S i j
  · by_contra hne
    exact (Nat.not_lt_of_ge hle)
      (pivot_potential_pairShift_lt V S i j hi hij (b, d) hk hne)
  · have hempty : pairIndices S i j b d = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro a ha
      have he := (mem_pairIndices S i j b d a).mp ha
      have hkey := pairKey_mem_pairKeys S i j he
      rw [pairKey_pairExponent i j hij b hbi hbj] at hkey
      exact hk hkey
    rw [hempty]
    apply Finset.card_eq_zero.mp
    rw [SupportShift.shiftedSupport_card]
    rfl

end WeightedPilz.Compression
