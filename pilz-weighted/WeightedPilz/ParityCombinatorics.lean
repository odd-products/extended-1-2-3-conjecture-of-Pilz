import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-! Counting unpaired occupied classes under a fixed-point-free involution. -/
namespace WeightedPilz

/-- If every pair crosses a distinguished bit, at most twice the number of
occupied classes having that bit can belong to occupied pairs. -/
theorem unpaired_card_lower_of_involutive_on {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (f : ι → ι) (hf : ∀ x ∈ A, f (f x) = x)
    (p : ι → Prop) [DecidablePred p]
    (hflip : ∀ x ∈ A, p (f x) ↔ ¬ p x) :
    A.card ≤ (A.filter (fun x => f x ∉ A)).card + 2 * (A.filter p).card := by
  classical
  let P := A.filter (fun x => f x ∈ A)
  have hyes : (P.filter p).card ≤ (A.filter p).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxP, hxp⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxP).1, hxp⟩
  have hno : (P.filter (fun x => ¬ p x)).card ≤ (A.filter p).card := by
    have hinj : Set.InjOn f ((P.filter (fun x => ¬ p x) : Finset ι) : Set ι) :=
      fun x hx y hy hxy => by
        have hh := congrArg f hxy
        have hxA := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
        have hyA := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
        rwa [hf x hxA, hf y hyA] at hh
    rw [← Finset.card_image_of_injOn hinj]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxP, hxp⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxA, hfx⟩ := Finset.mem_filter.mp hxP
    exact Finset.mem_filter.mpr ⟨hfx, (hflip x hxA).mpr hxp⟩
  have hP := Finset.filter_card_add_filter_neg_card_eq_card (s := P) p
  have hA := Finset.filter_card_add_filter_neg_card_eq_card
    (s := A) (fun x => f x ∈ A)
  change (P.filter p).card + (P.filter (fun x => ¬ p x)).card = P.card at hP
  change P.card + (A.filter (fun x => f x ∉ A)).card = A.card at hA
  omega

theorem unpaired_card_lower {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (f : ι → ι) (hf : Function.Involutive f)
    (p : ι → Prop) [DecidablePred p]
    (hflip : ∀ x ∈ A, p (f x) ↔ ¬ p x) :
    A.card ≤ (A.filter (fun x => f x ∉ A)).card + 2 * (A.filter p).card :=
  unpaired_card_lower_of_involutive_on A f (fun x _ => hf x) p hflip

end WeightedPilz
