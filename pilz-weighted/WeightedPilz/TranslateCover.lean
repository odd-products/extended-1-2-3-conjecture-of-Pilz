import WeightedPilz.Basic
import WeightedPilz.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite translate covers of valuation supports, and their conversion into
weighted cancellation bounds. Extra variables in the translations are allowed. -/

noncomputable section
namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

theorem factorization_cross_of_translated_eq {u v a x : ℕ}
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hx : 0 < x)
    (b d : ℕ →₀ ℕ)
    (h₁ : u.factorization + b = a.factorization + d)
    (h₂ : v.factorization + b = x.factorization + d) : u * x = v * a := by
  apply Nat.factorization_inj (ne_of_gt (Nat.mul_pos hu hx)) (ne_of_gt (Nat.mul_pos hv ha))
  rw [Nat.factorization_mul (ne_of_gt hu) (ne_of_gt hx),
    Nat.factorization_mul (ne_of_gt hv) (ne_of_gt ha)]
  ext p
  have h₁p := congrArg (fun e : ℕ →₀ ℕ => e p) h₁
  have h₂p := congrArg (fun e : ℕ →₀ ℕ => e p) h₂
  simp only [Finsupp.add_apply] at h₁p h₂p ⊢
  omega

/-- An anchored numerical certificate of two missing products bounds every
monomial translate, even when the translations use extra variables. -/
theorem translated_integer_support_inter_card (A U : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hU : ∀ u ∈ U, 0 < u) (hAcard : 2 ≤ A.card)
    (hmissing : ∀ u ∈ U, ∀ a ∈ A, ∃ x ∈ A, ∃ y ∈ A,
      x ≠ y ∧ (∀ v ∈ U, u * x ≠ v * a) ∧ (∀ v ∈ U, u * y ≠ v * a))
    (b d : ℕ →₀ ℕ) :
    ((U.image (fun u => u.factorization + b)) ∩
      (A.image (fun a => a.factorization + d))).card + 2 ≤ A.card := by
  classical
  let T := U.image (fun u => u.factorization + b)
  let V := A.filter (fun a => a.factorization + d ∈ T)
  have heq : T ∩ A.image (fun a => a.factorization + d) =
      V.image (fun a => a.factorization + d) := by
    ext e
    constructor
    · intro he
      obtain ⟨heT, a, ha, rfl⟩ :=
        (by simpa only [Finset.mem_inter, Finset.mem_image] using he)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, heT⟩, rfl⟩
    · intro he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp ha).2,
        Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1, rfl⟩⟩
  have hinj : Set.InjOn (fun a : ℕ => a.factorization + d) V := by
    intro a ha x hx heq
    exact Nat.factorization_inj (ne_of_gt (hA a (Finset.mem_filter.mp ha).1))
      (ne_of_gt (hA x (Finset.mem_filter.mp hx).1)) (add_right_cancel heq)
  change (T ∩ A.image (fun a => a.factorization + d)).card + 2 ≤ _
  rw [heq, Finset.card_image_iff.mpr hinj]
  by_cases hV : V.Nonempty
  · obtain ⟨a, haV⟩ := hV
    obtain ⟨ha, hat⟩ := Finset.mem_filter.mp haV
    obtain ⟨u, hu, hua⟩ := Finset.mem_image.mp hat
    obtain ⟨x, hx, y, hy, hxy, hxmiss, hymiss⟩ := hmissing u hu a ha
    have hnot (z : ℕ) (hz : z ∈ A) (hzmiss : ∀ v ∈ U, u * z ≠ v * a) : z ∉ V := by
      intro hzV
      obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hzV).2
      exact hzmiss v hv (factorization_cross_of_translated_eq
        (hU u hu) (hU v hv) (hA a ha) (hA z hz) b d hua hvz)
    have hsub : ({x, y} : Finset ℕ) ⊆ A \ V := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_sdiff.mpr ⟨hx, hnot _ hx hxmiss⟩
      · obtain rfl := Finset.mem_singleton.mp hz
        exact Finset.mem_sdiff.mpr ⟨hy, hnot _ hy hymiss⟩
    have htwo : 2 ≤ (A \ V).card := by
      simpa [hxy] using Finset.card_le_card hsub
    have hpart := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun a => a.factorization + d ∈ T) A)
    change (A \ V).card + V.card = A.card at hpart
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hV]
    simpa using hAcard

variable {σ K : Type*} [DecidableEq σ] [Field K]

/-- Each translated core support can cover at most `s` certified terms;
an arbitrary multiplier therefore covers at most `s * weight E` of them. -/
theorem support_inter_mul_le_translate_cover (T : Finset (σ →₀ ℕ))
    (C E : MvPolynomial σ K) (s : ℕ)
    (hcover : ∀ d, (T ∩ C.support.image (fun e => e + d)).card ≤ s) :
    (T ∩ (C * E).support).card ≤ s * weight E := by
  classical
  have hsub : T ∩ (C * E).support ⊆
      E.support.biUnion (fun d => T ∩ C.support.image (fun e => e + d)) := by
    intro z hz
    obtain ⟨hzT, hzCE⟩ := Finset.mem_inter.mp hz
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp (MvPolynomial.support_mul C E hzCE)
    exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_inter.mpr
      ⟨hzT, Finset.mem_image.mpr ⟨x, hx, hxy⟩⟩⟩
  have hcard := Finset.card_biUnion_le_card_mul E.support
    (fun d => T ∩ C.support.image (fun e => e + d)) s (fun d _ => hcover d)
  exact (Finset.card_le_card hsub).trans (by simpa only [weight, Nat.mul_comm] using hcard)

/-- Certified terms that are not covered survive subtraction. -/
theorem weight_sub_lower_of_translate_cover (P C E : MvPolynomial σ K)
    (T : Finset (σ →₀ ℕ)) (hT : T ⊆ P.support) (s : ℕ)
    (hcover : ∀ d, (T ∩ C.support.image (fun e => e + d)).card ≤ s) :
    T.card ≤ weight (P - C * E) + s * weight E := by
  classical
  have hsub : T \ (C * E).support ⊆ (P - C * E).support := by
    intro e he
    have hp := MvPolynomial.mem_support_iff.mp (hT (Finset.mem_sdiff.mp he).1)
    have hq := MvPolynomial.notMem_support_iff.mp (Finset.mem_sdiff.mp he).2
    simpa only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, hq, sub_zero] using hp
  have hcard := Finset.card_le_card hsub
  have hcover' := support_inter_mul_le_translate_cover T C E s hcover
  have hpart := Finset.card_sdiff_add_card_inter T (C * E).support
  unfold weight at *
  omega

end WeightedPilz
