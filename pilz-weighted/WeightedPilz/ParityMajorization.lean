import WeightedPilz.ResidueCapacity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring

/-! Two-level full-residue capacities, retaining the input class distribution. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {σ R : Type*} [CommSemiring R]

private theorem residue_add_of_left_zero (q : ℕ) (c d : σ →₀ ℕ)
    (hc : residueExponent q c = 0) : residueExponent q (c + d) = residueExponent q d := by
  ext i
  have hi := congrArg (fun f : σ →₀ ℕ => f i) hc
  simp only [residueExponent_apply, Finsupp.zero_apply] at hi
  simp only [residueExponent_apply, Finsupp.add_apply, Nat.add_mod, hi, zero_add, Nat.mod_mod]

private theorem shifted_filter_two_level (q : ℕ) (P : MvPolynomial σ R)
    (s t : ℕ) (hts : t ≤ s) (hzero : residueWeight q P 0 ≤ s)
    (hother : ∀ β, β ≠ 0 → residueWeight q P β ≤ t)
    (α d : σ →₀ ℕ) :
    (P.support.filter (fun c => residueExponent q (c + d) = α)).card ≤
      if residueExponent q d = α then s else t := by
  classical
  let A := P.support.filter (fun c => residueExponent q (c + d) = α)
  by_cases hA : A.Nonempty
  · obtain ⟨c, hc⟩ := hA
    have hcres := (Finset.mem_filter.mp hc).2
    have hsub : A ⊆ (residuePart q P (residueExponent q c)).support := by
      intro b hb
      obtain ⟨hbP, hbα⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr ⟨hbP,
        residueExponent_add_right_cancel q b c d (hbα.trans hcres.symm)⟩
    have hcard := Finset.card_le_card hsub
    by_cases hd : residueExponent q d = α
    · rw [if_pos hd]
      by_cases hc0 : residueExponent q c = 0
      · exact hcard.trans (by simpa [residueWeight, hc0] using hzero)
      · exact hcard.trans ((hother _ hc0).trans hts)
    · rw [if_neg hd]
      apply hcard.trans (hother _ _)
      intro hc0
      exact hd ((residue_add_of_left_zero q c d hc0).symm.trans hcres)
  · have hz : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ _
    simp [hz]

/-- Each output class receives the large-class budget only from the matching
input residue. Every other input term receives the second-class budget. -/
theorem residueWeight_mul_two_level (q : ℕ) (P Q : MvPolynomial σ R)
    (s t : ℕ) (hts : t ≤ s) (hzero : residueWeight q P 0 ≤ s)
    (hother : ∀ β, β ≠ 0 → residueWeight q P β ≤ t) (α : σ →₀ ℕ) :
    residueWeight q (P * Q) α ≤ s * residueWeight q Q α +
      t * (weight Q - residueWeight q Q α) := by
  classical
  have hsub := residueSupport_mul_subset q P Q α
  have hfirst := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hsum : (∑d∈Q.support,
      ((P.support.filter (fun c => residueExponent q (c + d) = α)).image (fun c => c + d)).card) ≤
      ∑d∈Q.support, if residueExponent q d = α then s else t := by
    apply Finset.sum_le_sum
    intro d hd
    exact Finset.card_image_le.trans (shifted_filter_two_level q P s t hts hzero hother α d)
  have hcount := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Q.support) (fun d => residueExponent q d = α)
  have hcomp : (Q.support.filter (fun d => ¬ residueExponent q d = α)).card =
      weight Q - residueWeight q Q α := by
    change (Q.support.filter (fun d => ¬ residueExponent q d = α)).card =
      Q.support.card - (Q.support.filter (fun d => residueExponent q d = α)).card
    omega
  have hbudget := hfirst.trans hsum
  simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at hbudget
  rw [hcomp] at hbudget
  simpa only [residueWeight, weight, support_residuePart, Nat.mul_comm] using hbudget

/-- Two occupied input classes make every individual class strictly smaller
than the entire input support. -/
theorem residueWeight_lt_of_two_classes (q : ℕ) (Q : MvPolynomial σ R)
    (hclasses : 2 ≤ (residueIndices q Q).card) (α : σ →₀ ℕ) :
    residueWeight q Q α < weight Q := by
  classical
  obtain ⟨β, hβ, hβα⟩ := Finset.exists_mem_ne (show 1 < (residueIndices q Q).card by omega) α
  obtain ⟨d, hd, hres⟩ := Finset.mem_image.mp hβ
  apply Finset.card_lt_card
  exact Finset.filter_ssubset.mpr ⟨d, hd, fun h => hβα (hres.symm.trans h)⟩

private theorem two_level_mono {u l k s t : ℕ} (hlk : l ≤ k) (hku : k ≤ u) (hts : t ≤ s) :
    s * l + t * (u - l) ≤ s * k + t * (u - k) := by
  have hlu := hlk.trans hku
  have hsplitl : l + (u - l) = u := by omega
  have hsplitk : k + (u - k) = u := by omega
  have hsplitst : s = (s - t) + t := by omega
  calc
    s * l + t * (u - l) = (s - t) * l + t * u := by
      calc
        _ = ((s - t) + t) * l + t * (u - l) := by rw [← hsplitst]
        _ = (s - t) * l + t * (l + (u - l)) := by ring
        _ = _ := by rw [hsplitl]
    _ ≤ (s - t) * k + t * u := Nat.add_le_add_right (Nat.mul_le_mul_left _ hlk) _
    _ = s * k + t * (u - k) := by
      calc
        _ = (s - t) * k + t * (k + (u - k)) := by rw [hsplitk]
        _ = ((s - t) + t) * k + t * (u - k) := by ring
        _ = _ := by rw [← hsplitst]

/-- The mixed-input estimate `(u-1)s+t` of `fin-majorization`. -/
theorem residueWeight_mul_mixed (q : ℕ) (P Q : MvPolynomial σ R)
    (s t : ℕ) (hts : t ≤ s) (hzero : residueWeight q P 0 ≤ s)
    (hother : ∀ β, β ≠ 0 → residueWeight q P β ≤ t)
    (hclasses : 2 ≤ (residueIndices q Q).card) (α : σ →₀ ℕ) :
    residueWeight q (P * Q) α ≤ (weight Q - 1) * s + t := by
  have hl := residueWeight_lt_of_two_classes q Q hclasses α
  have hu : 1 ≤ weight Q := by omega
  have hmono := two_level_mono (s := s) (t := t) (show residueWeight q Q α ≤ weight Q - 1 by omega)
    (Nat.sub_le (weight Q) 1) hts
  have h := (residueWeight_mul_two_level q P Q s t hts hzero hother α).trans hmono
  have hsub : weight Q - (weight Q - 1) = 1 := by omega
  simpa only [hsub, Nat.mul_one, Nat.mul_comm] using h

/-- With four terms in at least two classes, the absence of a three-term class
forces the stronger `2s+2t` capacity, covering every pattern except `(3,1)`. -/
theorem residueWeight_mul_four_not_three_one (q : ℕ) (P Q : MvPolynomial σ R)
    (s t : ℕ) (hts : t ≤ s) (hzero : residueWeight q P 0 ≤ s)
    (hother : ∀ β, β ≠ 0 → residueWeight q P β ≤ t)
    (hQ : weight Q = 4) (hclasses : 2 ≤ (residueIndices q Q).card)
    (hnot31 : ¬ ∃ β, residueWeight q Q β = 3) (α : σ →₀ ℕ) :
    residueWeight q (P * Q) α ≤ 2 * s + 2 * t := by
  have hl := residueWeight_lt_of_two_classes q Q hclasses α
  have hl2 : residueWeight q Q α ≤ 2 := by
    have hne : residueWeight q Q α ≠ 3 := fun h => hnot31 ⟨α, h⟩
    omega
  have hmono := two_level_mono (u := weight Q) (s := s) (t := t) hl2 (by omega : 2 ≤ weight Q) hts
  have h := (residueWeight_mul_two_level q P Q s t hts hzero hother α).trans hmono
  simpa only [hQ, Nat.reduceSub, Nat.mul_comm] using h

end WeightedPilz
