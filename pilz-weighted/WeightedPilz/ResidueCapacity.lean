import WeightedPilz.Dilation
import WeightedPilz.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Full exponent residues and cancellation capacities

These are the support-counting ingredients of `thm:residue-descent`.
Counts are natural numbers; inequalities with potentially negative gains
are stated with all negative terms moved to the opposite side.
-/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

local instance residueCapacityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {σ R : Type*} [CommSemiring R]

def residueIndices (q : ℕ) (P : MvPolynomial σ R) : Finset (σ →₀ ℕ) :=
  P.support.image (residueExponent q)

def residueWeight (q : ℕ) (P : MvPolynomial σ R) (α : σ →₀ ℕ) : ℕ :=
  weight (residuePart q P α)

/-- The maximum number of terms in one full residue class: manuscript `σ_q`. -/
def residueSigma (q : ℕ) (P : MvPolynomial σ R) : ℕ :=
  (residueIndices q P).sup (residueWeight q P)

theorem residuePart_ne_zero_of_mem_indices (q : ℕ) (P : MvPolynomial σ R)
    {α : σ →₀ ℕ} (hα : α ∈ residueIndices q P) : residuePart q P α ≠ 0 := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hα
  intro hz
  have hm : d ∈ (residuePart q P (residueExponent q d)).support :=
    Finset.mem_filter.mpr ⟨hd, rfl⟩
  simp [hz] at hm

theorem mem_residueIndices_of_part_ne_zero (q : ℕ) (P : MvPolynomial σ R)
    {α : σ →₀ ℕ} (h : residuePart q P α ≠ 0) : α ∈ residueIndices q P := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr h
  obtain ⟨hd, heq⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_image.mpr ⟨d, hd, heq⟩

theorem residue_support_biUnion (q : ℕ) (P : MvPolynomial σ R) :
    (residueIndices q P).biUnion (fun α => (residuePart q P α).support) = P.support := by
  ext d
  constructor
  · intro hd
    obtain ⟨α, _, hd⟩ := Finset.mem_biUnion.mp hd
    exact support_residuePart_subset q P α hd
  · intro hd
    apply Finset.mem_biUnion.mpr
    exact ⟨residueExponent q d, Finset.mem_image.mpr ⟨d, hd, rfl⟩,
      Finset.mem_filter.mpr ⟨hd, rfl⟩⟩

theorem sum_residueWeights (q : ℕ) (P : MvPolynomial σ R) :
    (∑ α ∈ residueIndices q P, residueWeight q P α) = weight P := by
  have hdis : (residueIndices q P : Set (σ →₀ ℕ)).PairwiseDisjoint
      (fun α => (residuePart q P α).support) := by
    intro α _ β _ hne
    exact residuePart_support_disjoint q P α β hne
  have hc := Finset.card_biUnion hdis
  rw [residue_support_biUnion] at hc
  exact hc.symm

theorem sum_residueWeights_le (q : ℕ) (P : MvPolynomial σ R)
    (A : Finset (σ →₀ ℕ)) : (∑ α ∈ A, residueWeight q P α) ≤ weight P := by
  have hdis : (A : Set (σ →₀ ℕ)).PairwiseDisjoint
      (fun α => (residuePart q P α).support) := by
    intro α _ β _ hne
    exact residuePart_support_disjoint q P α β hne
  have hsubset : A.biUnion (fun α => (residuePart q P α).support) ⊆ P.support := by
    intro d hd
    obtain ⟨α, _, hd⟩ := Finset.mem_biUnion.mp hd
    exact support_residuePart_subset q P α hd
  have hc := Finset.card_le_card hsubset
  rwa [Finset.card_biUnion hdis] at hc

theorem residueWeight_le_sigma (q : ℕ) (P : MvPolynomial σ R) (α : σ →₀ ℕ) :
    residueWeight q P α ≤ residueSigma q P := by
  by_cases hz : residuePart q P α = 0
  · simp [residueWeight, hz]
  · exact Finset.le_sup (f := residueWeight q P) (mem_residueIndices_of_part_ne_zero q P hz)

theorem residueSigma_le_weight (q : ℕ) (P : MvPolynomial σ R) :
    residueSigma q P ≤ weight P := by
  apply Finset.sup_le
  intro α _
  exact weight_residuePart_le q P α

theorem residueExponent_add_right_cancel (q : ℕ) (a b d : σ →₀ ℕ)
    (h : residueExponent q (a + d) = residueExponent q (b + d)) :
    residueExponent q a = residueExponent q b := by
  ext i
  have hi := congrArg (fun e : σ →₀ ℕ => e i) h
  simp only [residueExponent_apply, Finsupp.add_apply] at hi ⊢
  exact Nat.ModEq.add_right_cancel' (d i) hi

/-- For a fixed second term, output terms in one residue class use at most
one residue class of the first factor. -/
theorem shifted_residue_filter_card_le (q : ℕ) (P : MvPolynomial σ R)
    (α d : σ →₀ ℕ) :
    (P.support.filter (fun c => residueExponent q (c + d) = α)).card ≤ residueSigma q P := by
  let A := P.support.filter (fun c => residueExponent q (c + d) = α)
  by_cases hA : A.Nonempty
  · obtain ⟨c, hc⟩ := hA
    have hsub : A ⊆ (residuePart q P (residueExponent q c)).support := by
      intro b hb
      obtain ⟨hbP, hbα⟩ := Finset.mem_filter.mp hb
      have hcα := (Finset.mem_filter.mp hc).2
      exact Finset.mem_filter.mpr ⟨hbP,
        residueExponent_add_right_cancel q b c d (hbα.trans hcα.symm)⟩
    exact (Finset.card_le_card hsub).trans (residueWeight_le_sigma q P _)
  · have hz : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ _
    simp [hz]

theorem residueSupport_mul_subset (q : ℕ) (P Q : MvPolynomial σ R) (α : σ →₀ ℕ) :
    (residuePart q (P * Q) α).support ⊆ Q.support.biUnion (fun d =>
      (P.support.filter (fun c => residueExponent q (c + d) = α)).image (fun c => c + d)) := by
  intro e he
  obtain ⟨he, hres⟩ := Finset.mem_filter.mp he
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q he)
  apply Finset.mem_biUnion.mpr
  refine ⟨d, hd, Finset.mem_image.mpr ⟨c, ?_, hcd⟩⟩
  exact Finset.mem_filter.mpr ⟨hc, hcd ▸ hres⟩

/-- The coefficient-space cancellation capacity used for each `C^j A_j`. -/
theorem residueWeight_mul_le (q : ℕ) (P Q : MvPolynomial σ R) (α : σ →₀ ℕ) :
    residueWeight q (P * Q) α ≤ residueSigma q P * weight Q := by
  have hsub := residueSupport_mul_subset q P Q α
  have hc := Finset.card_biUnion_le_card_mul Q.support
    (fun d => (P.support.filter (fun c => residueExponent q (c + d) = α)).image (fun c => c + d))
    (residueSigma q P) (fun d _ => Finset.card_image_le.trans
      (shifted_residue_filter_card_le q P α d))
  exact (Finset.card_le_card hsub).trans (by simpa [weight, Nat.mul_comm] using hc)

theorem residueWeight_add_le (q : ℕ) (P Q : MvPolynomial σ R) (α : σ →₀ ℕ) :
    residueWeight q (P + Q) α ≤ residueWeight q P α + residueWeight q Q α := by
  rw [residueWeight, residuePart_add]
  exact (Finset.card_le_card MvPolynomial.support_add).trans (Finset.card_union_le _ _)

theorem residueWeight_sum_le {ι : Type*} (q : ℕ) (A : Finset ι)
    (P : ι → MvPolynomial σ R) (α : σ →₀ ℕ) :
    residueWeight q (∑ j ∈ A, P j) α ≤ ∑ j ∈ A, residueWeight q (P j) α := by
  induction A using Finset.induction_on with
  | empty =>
    have hz : residuePart q (0 : MvPolynomial σ R) α = 0 := by
      ext d
      simp [coeff_residuePart]
    simp [residueWeight, hz, weight]
  | @insert j A hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (residueWeight_add_le q (P j) (∑ k ∈ A, P k) α).trans (Nat.add_le_add_left ih _)

/-- A sum of comparison terms has capacity at most the sum of their capacities. -/
theorem residueWeight_sum_mul_le {ι : Type*} (q : ℕ) (A : Finset ι)
    (P Q : ι → MvPolynomial σ R) (α : σ →₀ ℕ) :
    residueWeight q (∑ j ∈ A, P j * Q j) α ≤
      ∑ j ∈ A, residueSigma q (P j) * weight (Q j) := by
  exact (residueWeight_sum_le q A (fun j => P j * Q j) α).trans
    (Finset.sum_le_sum (fun j _ => residueWeight_mul_le q (P j) (Q j) α))

theorem weight_le_weight_add_add (P Q : MvPolynomial σ R) :
    weight P ≤ weight (P + Q) + weight Q := by
  have h := weight_add_cancellation P Q
  have hi : (P.support ∩ Q.support).card ≤ weight Q :=
    Finset.card_le_card Finset.inter_subset_right
  omega

theorem residueWeight_le_add (q : ℕ) (P Q : MvPolynomial σ R) (α : σ →₀ ℕ) :
    residueWeight q P α ≤ residueWeight q (P + Q) α + residueWeight q Q α := by
  unfold residueWeight
  rw [residuePart_add]
  exact weight_le_weight_add_add _ _

theorem support_inter_card_le_residue_sum (q : ℕ) (U B : MvPolynomial σ R) :
    (U.support ∩ B.support).card ≤ ∑ α ∈ residueIndices q U, residueWeight q B α := by
  have hsub : U.support ∩ B.support ⊆
      (residueIndices q U).biUnion (fun α => (residuePart q B α).support) := by
    intro d hd
    obtain ⟨hU, hB⟩ := Finset.mem_inter.mp hd
    exact Finset.mem_biUnion.mpr ⟨residueExponent q d,
      Finset.mem_image.mpr ⟨d, hU, rfl⟩, Finset.mem_filter.mpr ⟨hB, rfl⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- The precise residue capacity inequalities, with no truncated negative
gain. The cost premise is supplied by strict Frobenius width descent. -/
theorem residue_correction_capacity (q N : ℕ) (U B : MvPolynomial σ R)
    (hcost : ∀ α ∈ residueIndices q U, N ≤ residueWeight q U α) :
    weight B + (residueIndices q U).card * N ≤
        weight (U + B) + 2 * ∑ α ∈ residueIndices q U, residueWeight q B α ∧
      (∑ α ∈ residueIndices q U, (N - residueWeight q B α)) ≤ weight (U + B) := by
  have hN : (residueIndices q U).card * N ≤ weight U := by
    rw [← sum_residueWeights q U]
    simpa using Finset.sum_le_sum hcost
  have hcancel := weight_add_cancellation U B
  have hoverlap := support_inter_card_le_residue_sum q U B
  constructor
  · omega
  · have hpoint : ∀ α ∈ residueIndices q U,
        N - residueWeight q B α ≤ residueWeight q (U + B) α := by
      intro α hα
      have hc := hcost α hα
      have ht := residueWeight_le_add q U B α
      omega
    exact (Finset.sum_le_sum hpoint).trans (sum_residueWeights_le q (U + B) _)

/-- Uniform capacities `M` give the manuscript's two aggregate bounds. -/
theorem residue_correction_uniform_capacity (q N M : ℕ) (U B : MvPolynomial σ R)
    (hcost : ∀ α ∈ residueIndices q U, N ≤ residueWeight q U α)
    (hcap : ∀ α ∈ residueIndices q U, residueWeight q B α ≤ M) :
    weight B + (residueIndices q U).card * N ≤
        weight (U + B) + 2 * (residueIndices q U).card * M ∧
      (residueIndices q U).card * (N - M) ≤ weight (U + B) := by
  obtain ⟨hfirst, hsecond⟩ := residue_correction_capacity q N U B hcost
  have hsum : (∑ α ∈ residueIndices q U, residueWeight q B α) ≤
      (residueIndices q U).card * M := by
    simpa using Finset.sum_le_sum hcap
  constructor
  · calc
      _ ≤ weight (U + B) + 2 * ∑ α ∈ residueIndices q U, residueWeight q B α := hfirst
      _ ≤ _ := by simpa only [Nat.mul_assoc] using Nat.add_le_add_left (Nat.mul_le_mul_left 2 hsum) _
  · have hle : (residueIndices q U).card * (N - M) ≤
        ∑ α ∈ residueIndices q U, (N - residueWeight q B α) := by
      have hpoint : ∀ α ∈ residueIndices q U, N - M ≤ N - residueWeight q B α := by
        intro α hα
        exact Nat.sub_le_sub_left (hcap α hα) N
      simpa using Finset.sum_le_sum hpoint
    exact hle.trans hsecond

end WeightedPilz
