import Pilz.Residual
import Pilz.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-!
# Capacity of a full parity class in a product

This is the classwise support bound in the proof of fresh-variable
elimination: each term of the second factor can use only one full parity
class of the first factor.
-/

noncomputable section

namespace Pilz

/-- The class of a term that can combine with `d` to enter class `ε`. -/
def complementaryParity (ε : ℕ → ℕ) (d : ℕ →₀ ℕ) : ℕ → ℕ :=
  fun i => (ε i + d i) % 2

/-- Every product term in one parity class is charged to a term of the
second factor and a single complementary class of the first factor. -/
theorem paritySupport_mul_subset (C D : Poly) (ε : ℕ → ℕ) :
    paritySupport (C * D) ε ⊆ D.support.biUnion (fun d =>
      (paritySupport C (complementaryParity ε d)).image (fun c => c + d)) := by
  classical
  intro e he
  obtain ⟨he, hpar⟩ := Finset.mem_filter.mp he
  obtain ⟨c, hc, d, hd, hcd⟩ :=
    Finset.mem_add.mp (MvPolynomial.support_mul C D he)
  apply Finset.mem_biUnion.mpr
  refine ⟨d, hd, Finset.mem_image.mpr ⟨c, ?_, hcd⟩⟩
  apply Finset.mem_filter.mpr
  refine ⟨hc, ?_⟩
  intro i
  have hi := hpar i
  rw [← hcd, Finsupp.add_apply] at hi
  simp only [complementaryParity]
  omega

/-- If every class of `C` has at most `s` terms, every class of `C*D`
has at most `s * weight D` terms. No condition is required on `D`. -/
theorem classWeight_mul_le (C D : Poly) (s : ℕ)
    (hC : ∀ ε : ℕ → ℕ, classWeight C ε ≤ s) (ε : ℕ → ℕ) :
    classWeight (C * D) ε ≤ s * weight D := by
  classical
  have hsubset := paritySupport_mul_subset C D ε
  have hcard := Finset.card_biUnion_le_card_mul D.support
    (fun d => (paritySupport C (complementaryParity ε d)).image (fun c => c + d))
    s (fun d _hd => Finset.card_image_le.trans (hC (complementaryParity ε d)))
  exact (Finset.card_le_card hsubset).trans (by simpa [weight, Nat.mul_comm] using hcard)

end Pilz
