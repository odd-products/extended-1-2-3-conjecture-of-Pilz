import WeightedPilz.GroupActions
import Mathlib.Algebra.Group.Units.Hom

/-! The reduction from commuting monoid endomorphisms to the group of additive
units, together with the nonunit-summand alternative. The all-field interval
theorem is the only external mathematical premise of the final criterion. -/

namespace WeightedPilz

open scoped BigOperators

universe u
variable {M : Type u} [AddCommMonoid M]

/-- Compose each active weight once, in a fixed order. -/
def intervalEndComposite (φ : ℕ → AddMonoid.End M) : ℕ → AddMonoid.End M
  | 0 => 1
  | n + 1 => φ (n + 1) * intervalEndComposite φ n

theorem intervalEndComposite_reflectsZero (φ : ℕ → AddMonoid.End M) (n : ℕ) :
    (∀ a, 1 ≤ a → a ≤ n → ReflectsZero (φ a)) →
      ReflectsZero (intervalEndComposite φ n) := by
  induction n with
  | zero => intro h x hx; exact hx
  | succ n ih =>
      intro h x hx
      apply ih (fun a ha han => h a ha (by omega)) x
      exact h (n + 1) (by omega) (by omega) _ hx

theorem intervalEndComposite_commute (φ : ℕ → AddMonoid.End M) (n : ℕ)
    (θ : AddMonoid.End M) :
    (∀ a, 1 ≤ a → a ≤ n → Function.Commute (φ a) θ) →
      Function.Commute (intervalEndComposite φ n) θ := by
  induction n with
  | zero => intro h x; rfl
  | succ n ih =>
      intro h x
      change φ (n + 1) (intervalEndComposite φ n (θ x)) =
        θ (φ (n + 1) (intervalEndComposite φ n x))
      rw [ih (fun a ha han => h a ha (by omega)) x]
      exact h (n + 1) (by omega) (by omega) _

/-- If one active weight sends a value to an additive unit, the full composite
does so as well, since commuting factors can be applied in either order. -/
theorem isAddUnit_intervalEndComposite_of_weight (φ : ℕ → AddMonoid.End M) (n : ℕ) :
    (∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n →
      Function.Commute (φ a) (φ b)) →
    ∀ a, 1 ≤ a → a ≤ n → ∀ x, IsAddUnit (φ a x) →
      IsAddUnit (intervalEndComposite φ n x) := by
  induction n with
  | zero => intro h a ha han; omega
  | succ n ih =>
      intro h a ha han x hx
      by_cases heq : a = n + 1
      · subst a
        have hcomp := intervalEndComposite_commute φ n (φ (n + 1))
          (fun b hb hbn => h b hb (by omega) (n + 1) (by omega) (by omega))
        change IsAddUnit (φ (n + 1) (intervalEndComposite φ n x))
        rw [← hcomp x]
        exact hx.map (intervalEndComposite φ n)
      · change IsAddUnit (φ (n + 1) (intervalEndComposite φ n x))
        exact (ih (fun b hb hbn d hd hdn => h b hb (by omega) d hd (by omega))
          a ha (by omega) x hx).map (φ (n + 1))

/-- A nonunit summand cannot occur in a zero output. -/
theorem intervalEndAction_ne_zero_of_nonunit_term (n : ℕ)
    (φ : ℕ → AddMonoid.End M) (f : ℕ+ →₀ M) {a : ℕ}
    (ha : a ∈ Finset.range n) (b : ℕ+)
    (hunit : ¬IsAddUnit (φ (a + 1) (f b))) :
    intervalEndAction n φ f (intervalIndex a * b) ≠ 0 := by
  classical
  intro hz
  rw [intervalEndAction_apply] at hz
  have hu : IsAddUnit
      (∑ d ∈ Finset.range n, if intervalIndex d ∣ intervalIndex a * b then
        φ (d + 1) (f (PNat.divExact (intervalIndex a * b) (intervalIndex d))) else 0) := by
    rw [hz]
    exact isAddUnit_zero
  have ht := IsAddUnit.sum_iff.mp hu a ha
  have hd : intervalIndex a ∣ intervalIndex a * b := ⟨b, rfl⟩
  have hquot : PNat.divExact (intervalIndex a * b) (intervalIndex a) = b :=
    mul_left_cancel (PNat.mul_div_exact hd)
  exact hunit (by simpa only [if_pos hd, hquot] using ht)

/-- A coefficient whose full composite is noninvertible already forces all
`n` distinct outputs at its interval multiples to be nonzero. -/
theorem intervalEndAction_bound_of_nonunit_composite (n : ℕ)
    (φ : ℕ → AddMonoid.End M)
    (hcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n →
      Function.Commute (φ a) (φ b))
    (f : ℕ+ →₀ M) (b : ℕ+)
    (hb : ¬IsAddUnit (intervalEndComposite φ n (f b))) :
    n ≤ (intervalEndAction n φ f).support.card := by
  classical
  have hs : (Finset.range n).image (fun a => intervalIndex a * b) ⊆
      (intervalEndAction n φ f).support := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
    apply Finsupp.mem_support_iff.mpr
    apply intervalEndAction_ne_zero_of_nonunit_term n φ f ha b
    intro hu
    exact hb (isAddUnit_intervalEndComposite_of_weight φ n hcomm (a + 1)
      (by omega) (by have := Finset.mem_range.mp ha; omega) (f b) hu)
  have hcard := Finset.card_le_card hs
  have hinj : Function.Injective (fun a => intervalIndex a * b) :=
    fun _ _ h => intervalIndex_injective (mul_right_cancel h)
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_range] using hcard

/-- A zero-reflecting endomorphism restricts to an injective map on additive units. -/
theorem addUnits_map_injective_of_reflectsZero (φ : AddMonoid.End M)
    (hφ : ReflectsZero φ) : Function.Injective (AddUnits.map φ) := by
  apply (reflectsZero_iff_injective (AddUnits.map φ)).mp
  intro x hx
  apply AddUnits.val_injective
  apply hφ
  exact congrArg AddUnits.val hx

/-- Every commuting zero-reflecting monoid action has the interval support
bound, assuming the all-field interval theorem. -/
theorem intervalEndBound_commuting_monoid_of_field_bounds (n : ℕ)
    (φ : ℕ → AddMonoid.End M)
    (hcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n →
      Function.Commute (φ a) (φ b))
    (hzero : ∀ a, 1 ≤ a → a ≤ n → ReflectsZero (φ a))
    (hfield : ∀ (K : Type u) [Field K] (d : ℕ → K),
      NonzeroWeights n d → IntervalBound n d) : IntervalEndBound n φ := by
  classical
  intro f hf
  let ψ := intervalEndComposite φ n
  have hψ : ReflectsZero ψ := intervalEndComposite_reflectsZero φ n hzero
  by_cases hall : ∀ b, IsAddUnit (ψ (f b))
  · let h : ℕ+ →₀ AddUnits M := Finsupp.onFinset f.support
      (fun b => (hall b).addUnit) (by
        intro b hb
        apply Finsupp.mem_support_iff.mpr
        intro hz
        apply hb
        apply AddUnits.val_injective
        change ψ (f b) = 0
        rw [hz, map_zero])
    have hh : h ≠ 0 := by
      intro hz
      apply hf
      ext b
      apply hψ
      exact congrArg (fun g : ℕ+ →₀ AddUnits M => (g b).val) hz
    let η : ℕ → AddMonoid.End (AddUnits M) := fun a => AddUnits.map (φ a)
    have hηcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n →
        Function.Commute (η a) (η b) := by
      intro a ha han b hb hbn x
      apply AddUnits.val_injective
      exact hcomm a ha han b hb hbn x.val
    have hηinj : ∀ a, 1 ≤ a → a ≤ n → Function.Injective (η a) :=
      fun a ha han => addUnits_map_injective_of_reflectsZero (φ a) (hzero a ha han)
    have hb := intervalEndBound_commuting_group_of_field_bounds n η hηcomm hηinj hfield h hh
    have hcoe : Finsupp.mapRange (AddUnits.coeHom M) (map_zero _) h =
        Finsupp.mapRange ψ ψ.map_zero f := by
      ext b
      rfl
    have hinter : ∀ a ∈ Finset.range n, ∀ x, ψ (φ (a + 1) x) = φ (a + 1) (ψ x) := by
      intro a ha x
      have han := Finset.mem_range.mp ha
      exact intervalEndComposite_commute φ n (φ (a + 1))
        (fun b hb hbn => hcomm b hb hbn (a + 1) (by omega) (by omega)) x
    have heq : Finsupp.mapRange (AddUnits.coeHom M) (map_zero _)
        (intervalEndAction n η h) = Finsupp.mapRange ψ ψ.map_zero
          (intervalEndAction n φ f) := by
      rw [intervalEndAction_naturality n η φ (AddUnits.coeHom M) (fun _ _ _ => rfl),
        hcoe, intervalEndAction_naturality n φ φ ψ hinter]
    have hcoezero : ∀ x : AddUnits M, AddUnits.coeHom M x = 0 → x = 0 :=
      fun x hx => AddUnits.val_injective hx
    have hs : (intervalEndAction n η h).support = (intervalEndAction n φ f).support := by
      rw [← support_mapRange_of_zeroReflecting (AddUnits.coeHom M) hcoezero,
        heq, support_mapRange_of_zeroReflecting ψ hψ]
    rwa [hs] at hb
  · push_neg at hall
    obtain ⟨b, hb⟩ := hall
    exact intervalEndAction_bound_of_nonunit_composite n φ hcomm f b hb

/-- The full zero-reflection criterion for commuting monoid weights, as a
consequence of the all-field interval theorem. Singleton sharpness is given
independently by `intervalEndAction_sharp`. -/
theorem intervalEndBound_commuting_monoid_iff_of_field_bounds (n : ℕ)
    (φ : ℕ → AddMonoid.End M)
    (hcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n →
      Function.Commute (φ a) (φ b))
    (hfield : ∀ (K : Type u) [Field K] (d : ℕ → K),
      NonzeroWeights n d → IntervalBound n d) :
    IntervalEndBound n φ ↔ ∀ a, 1 ≤ a → a ≤ n → ReflectsZero (φ a) := by
  constructor
  · intro h a ha han
    exact reflectsZero_of_intervalEndBound h ha han
  · intro hzero
    exact intervalEndBound_commuting_monoid_of_field_bounds n φ hcomm hzero hfield

end WeightedPilz
