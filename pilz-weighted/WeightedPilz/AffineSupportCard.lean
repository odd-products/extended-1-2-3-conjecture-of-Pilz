import WeightedPilz.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Group.Finsupp

/-! The affine dimension of a finite exponent support, computed over the
rationals, is strictly less than the number of its points. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial

variable {σ K : Type*} [CommSemiring K]

def rationalExponent : (σ →₀ ℕ) →+ (σ →₀ ℚ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℚ)

@[simp] theorem rationalExponent_apply (a : σ →₀ ℕ) (i : σ) :
    rationalExponent a i = (a i : ℚ) := rfl

theorem rationalExponent_injective : Function.Injective (rationalExponent (σ := σ)) := by
  intro a b h
  ext i
  exact Nat.cast_injective (congrArg (fun d : σ →₀ ℚ => d i) h)

def affineDifferenceSpan (P : MvPolynomial σ K) : Submodule ℚ (σ →₀ ℚ) :=
  Submodule.span ℚ {x | ∃ a ∈ P.support, ∃ b ∈ P.support,
    x = rationalExponent a - rationalExponent b}

def affineDimension (P : MvPolynomial σ K) : ℕ :=
  Module.finrank ℚ (affineDifferenceSpan P)

def affineSupportGenerators (P : MvPolynomial σ K) (b : σ →₀ ℕ) :
    Finset (σ →₀ ℚ) := by
  classical
  exact (P.support.erase b).image (fun a => rationalExponent a - rationalExponent b)

theorem affineDifferenceSpan_eq_span_erase (P : MvPolynomial σ K)
    (b : σ →₀ ℕ) (hb : b ∈ P.support) :
    affineDifferenceSpan P =
      Submodule.span ℚ (affineSupportGenerators P b : Set (σ →₀ ℚ)) := by
  classical
  have hbase : ∀ a ∈ P.support,
      rationalExponent a - rationalExponent b ∈
        Submodule.span ℚ (affineSupportGenerators P b : Set (σ →₀ ℚ)) := by
    intro a ha
    by_cases hab : a = b
    · subst a
      simp
    · apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨hab, ha⟩, rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, ha, c, hc, rfl⟩
    have h := Submodule.sub_mem _ (hbase a ha) (hbase c hc)
    simpa only [sub_sub_sub_cancel_right] using h
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    apply Submodule.subset_span
    exact ⟨a, (Finset.mem_erase.mp ha).2, b, hb, rfl⟩

instance affineDifferenceSpan_finiteDimensional (P : MvPolynomial σ K) :
    FiniteDimensional ℚ (affineDifferenceSpan P) := by
  classical
  by_cases hP : P = 0
  · subst P
    have hspan : affineDifferenceSpan (0 : MvPolynomial σ K) = ⊥ := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro x ⟨a, ha, b, hb, heq⟩
        exact False.elim ((Finsupp.notMem_support_iff.mpr rfl) ha)
      · exact bot_le
    rw [hspan]
    infer_instance
  · obtain ⟨b, hb⟩ := Finsupp.support_nonempty_iff.mpr hP
    rw [affineDifferenceSpan_eq_span_erase P b hb]
    infer_instance

/-- A nonempty support of affine dimension `d` has at least `d+1` points. -/
theorem affineDimension_add_one_le_weight (P : MvPolynomial σ K) (hP : P ≠ 0) :
    affineDimension P + 1 ≤ weight P := by
  classical
  obtain ⟨b, hb⟩ := Finsupp.support_nonempty_iff.mpr hP
  have hrank := finrank_span_finset_le_card (R := ℚ) (affineSupportGenerators P b)
  have hdim : affineDimension P ≤ (affineSupportGenerators P b).card := by
    rw [affineDimension, affineDifferenceSpan_eq_span_erase P b hb]
    simpa using hrank
  have hcard : (affineSupportGenerators P b).card ≤ (P.support.erase b).card :=
    Finset.card_image_le
  calc
    affineDimension P + 1 ≤ (affineSupportGenerators P b).card + 1 :=
      Nat.add_le_add_right hdim 1
    _ ≤ (P.support.erase b).card + 1 := Nat.add_le_add_right hcard 1
    _ = P.support.card := Finset.card_erase_add_one hb
    _ = weight P := rfl

end WeightedPilz
