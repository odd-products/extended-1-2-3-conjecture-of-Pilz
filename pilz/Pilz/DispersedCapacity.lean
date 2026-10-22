import Pilz.ParityClasses
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring

/-! The dispersed class-capacity bound of the small-case argument. If a
multiplier occupies several parity classes, at most one of them can use
the distinguished largest class of the other factor. -/

noncomputable section

namespace Pilz

open scoped BigOperators

/-- Charging every contributing term to its complementary class gives a
weighted version of the ordinary class-capacity bound. -/
theorem classWeight_mul_le_sum (C D : Poly) (ε : ℕ → ℕ) :
    classWeight (C * D) ε ≤
      ∑ d ∈ D.support, classWeight C (complementaryParity ε d) := by
  classical
  calc
    classWeight (C * D) ε ≤
        (D.support.biUnion (fun d =>
          (paritySupport C (complementaryParity ε d)).image (fun c => c + d))).card :=
      Finset.card_le_card (paritySupport_mul_subset C D ε)
    _ ≤ ∑ d ∈ D.support,
        ((paritySupport C (complementaryParity ε d)).image (fun c => c + d)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ d ∈ D.support, classWeight C (complementaryParity ε d) :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)

/-- A subset contained in one fibre uses at most the total size minus the
number of other occupied fibres. This form also covers an empty subset. -/
private theorem filter_card_add_image_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) (p : α → Prop) [DecidablePred p]
    (hp : ∀ a ∈ A, ∀ b ∈ A, p a → p b → f a = f b) :
    (A.filter p).card + (A.image f).card ≤ A.card + 1 := by
  classical
  let B := A.filter p
  let E := A.filter (fun a => ¬ p a)
  have hpart : B ∪ E = A := Finset.filter_union_filter_neg_eq p A
  have hsum : B.card + E.card = A.card :=
    Finset.filter_card_add_filter_neg_card_eq_card p
  have hB : (B.image f).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨haA, hap⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbA, hbp⟩ := Finset.mem_filter.mp hb
    exact hp a haA b hbA hap hbp
  have himage : A.image f = B.image f ∪ E.image f := by
    rw [← Finset.image_union, hpart]
  have himagecard : (A.image f).card ≤ 1 + E.card := by
    rw [himage]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add hB Finset.card_image_le)
  change B.card + (A.image f).card ≤ A.card + 1
  calc
    B.card + (A.image f).card ≤ B.card + (1 + E.card) :=
      Nat.add_le_add_left himagecard _
    _ = (B.card + E.card) + 1 := by omega
    _ = A.card + 1 := by rw [hsum]

/-- Distinct multiplier parity classes have distinct complementary classes. -/
theorem parityExponent_eq_of_complementaryParity_eq (ε : ℕ → ℕ) (d e : ℕ →₀ ℕ)
    (h : complementaryParity ε d = complementaryParity ε e) :
    parityExponent d = parityExponent e := by
  ext i
  have hi := congrFun h i
  simp only [complementaryParity] at hi
  simp only [parityExponent_apply]
  omega

/-- Additive form of the manuscript's dispersed capacity estimate. The
distinguished class may have fewer than `s` terms; only upper bounds matter. -/
theorem classWeight_mul_dispersed_add (C D : Poly) (ε₀ : ℕ → ℕ) (s t : ℕ)
    (hst : t ≤ s) (hC : ∀ η : ℕ → ℕ, classWeight C η ≤ s)
    (hOther : ∀ η : ℕ → ℕ, η ≠ ε₀ → classWeight C η ≤ t) (ε : ℕ → ℕ) :
    classWeight (C * D) ε + ((parityIndices D).card - 1) * (s - t) ≤ weight D * s := by
  classical
  let p := fun d : ℕ →₀ ℕ => complementaryParity ε d = ε₀
  let b := (D.support.filter p).card
  let e := (D.support.filter (fun d => ¬ p d)).card
  have hsum : b + e = weight D :=
    Finset.filter_card_add_filter_neg_card_eq_card p
  have hfibre : b + (parityIndices D).card ≤ weight D + 1 := by
    apply filter_card_add_image_card_le D.support parityExponent p
    intro a _ha b _hb hpa hpb
    exact parityExponent_eq_of_complementaryParity_eq ε a b (hpa.trans hpb.symm)
  have he : (parityIndices D).card - 1 ≤ e := by omega
  have hcap : classWeight (C * D) ε ≤ b * s + e * t := by
    calc
      classWeight (C * D) ε ≤
          ∑ d ∈ D.support, classWeight C (complementaryParity ε d) :=
        classWeight_mul_le_sum C D ε
      _ ≤ ∑ d ∈ D.support, (if p d then s else t) := by
        apply Finset.sum_le_sum
        intro d _hd
        split_ifs with hp
        · exact hC _
        · exact hOther _ hp
      _ = b * s + e * t := by
        rw [Finset.sum_ite]
        simp [b, e]
  have hmul := Nat.mul_le_mul_right (s - t) he
  have hdiff : t + (s - t) = s := by omega
  calc
    classWeight (C * D) ε + ((parityIndices D).card - 1) * (s - t) ≤
        (b * s + e * t) + e * (s - t) := Nat.add_le_add hcap hmul
    _ = (b + e) * s := by
      calc
        _ = b * s + e * (t + (s - t)) := by ring
        _ = (b + e) * s := by rw [hdiff]; ring
    _ = weight D * s := by rw [hsum]

/-- The natural-subtraction form `us-(k-1)(s-t)`. -/
theorem classWeight_mul_dispersed (C D : Poly) (ε₀ : ℕ → ℕ) (s t : ℕ)
    (hst : t ≤ s) (hC : ∀ η : ℕ → ℕ, classWeight C η ≤ s)
    (hOther : ∀ η : ℕ → ℕ, η ≠ ε₀ → classWeight C η ≤ t) (ε : ℕ → ℕ) :
    classWeight (C * D) ε ≤ weight D * s - ((parityIndices D).card - 1) * (s - t) := by
  have h := classWeight_mul_dispersed_add C D ε₀ s t hst hC hOther ε
  omega

/-- Occupying at least two multiplier classes improves `us` to `(u-1)s+t`. -/
theorem classWeight_mul_dispersed_two (C D : Poly) (ε₀ : ℕ → ℕ) (s t : ℕ)
    (hst : t ≤ s) (hC : ∀ η : ℕ → ℕ, classWeight C η ≤ s)
    (hOther : ∀ η : ℕ → ℕ, η ≠ ε₀ → classWeight C η ≤ t)
    (hclasses : 2 ≤ (parityIndices D).card) (ε : ℕ → ℕ) :
    classWeight (C * D) ε ≤ (weight D - 1) * s + t := by
  classical
  have h := classWeight_mul_dispersed_add C D ε₀ s t hst hC hOther ε
  have hcount : (parityIndices D).card ≤ weight D := Finset.card_image_le
  have hu : 1 ≤ weight D := by omega
  have hk : 1 ≤ (parityIndices D).card - 1 := by omega
  have hmul : s - t ≤ ((parityIndices D).card - 1) * (s - t) := by
    simpa using Nat.mul_le_mul_right (s - t) hk
  have hprod : weight D * s = (weight D - 1) * s + s := by
    calc
      _ = ((weight D - 1) + 1) * s :=
        congrArg (fun a => a * s) (Nat.sub_add_cancel hu).symm
      _ = (weight D - 1) * s + s := by ring
  have hdiff : t + (s - t) = s := by omega
  omega

end Pilz
