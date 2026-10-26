import WeightedPilz.Defs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MonoidAlgebra.Support
import Lean.Elab.Tactic.Omega

/-!
# Support bounds used in the directed cut

These are the elementary support estimates from the proof of
`lem:directed-cut`, and the invariance under monomial multiplication in
the frozen manuscript's basic operations subsection. The cancellation estimate holds over every
commutative semiring, so in particular over every field used in the paper.
-/

noncomputable section

namespace WeightedPilz

open MvPolynomial

section GeneralSupport

variable {σ R : Type*} [DecidableEq σ] [CommSemiring R]

/-- A term present on either side survives addition unless it occurs on both sides. -/
theorem support_union_subset_add_union_inter
    (P Q : MvPolynomial σ R) :
    P.support ∪ Q.support ⊆ (P + Q).support ∪ (P.support ∩ Q.support) := by
  classical
  intro d hd
  by_cases hi : d ∈ P.support ∩ Q.support
  · exact Finset.mem_union_right _ hi
  · apply Finset.mem_union_left
    rcases Finset.mem_union.mp hd with hp | hq
    · have hq : d ∉ Q.support := fun hq => hi (Finset.mem_inter.mpr ⟨hp, hq⟩)
      have hq0 := MvPolynomial.notMem_support_iff.mp hq
      simpa only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add,
        hq0, add_zero] using hp
    · have hp : d ∉ P.support := fun hp => hi (Finset.mem_inter.mpr ⟨hp, hq⟩)
      have hp0 := MvPolynomial.notMem_support_iff.mp hp
      simpa only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add,
        hp0, zero_add] using hq

/-- The support cancellation inequality, in a form without truncated subtraction. -/
theorem support_card_add_cancellation (P Q : MvPolynomial σ R) :
    P.support.card + Q.support.card ≤
      (P + Q).support.card + 2 * (P.support ∩ Q.support).card := by
  classical
  have h₁ := Finset.card_le_card (support_union_subset_add_union_inter P Q)
  have h₂ := Finset.card_union_le (P + Q).support (P.support ∩ Q.support)
  have h₃ := Finset.card_union_add_card_inter P.support Q.support
  omega

/-- Disjoint supports add without cancellation. -/
theorem support_card_add_of_disjoint (P Q : MvPolynomial σ R)
    (h : Disjoint P.support Q.support) :
    (P + Q).support.card = P.support.card + Q.support.card := by
  classical
  change (Finsupp.support (P + Q)).card = _
  rw [Finsupp.support_add_eq h]
  exact Finset.card_union_of_disjoint h



/-- Paper, directed cut: at most two terms are lost for each common support point. -/
theorem weight_add_cancellation (P Q : MvPolynomial σ R) :
    weight P + weight Q ≤
      weight (P + Q) + 2 * (P.support ∩ Q.support).card :=
  support_card_add_cancellation P Q

theorem weight_add_of_disjoint (P Q : MvPolynomial σ R)
    (h : Disjoint P.support Q.support) :
    weight (P + Q) = weight P + weight Q :=
  support_card_add_of_disjoint P Q h

/-- Multiplying by a monomial preserves weight. -/
@[simp] theorem weight_monomial_mul (s : σ →₀ ℕ) (P : MvPolynomial σ R) :
    weight ((MvPolynomial.monomial s 1 : MvPolynomial σ R) * P) = weight P := by
  have hs : (MvPolynomial.monomial s 1 * P : MvPolynomial σ R).support =
      P.support.map (addLeftEmbedding s) :=
    AddMonoidAlgebra.support_single_mul P 1 (by simp) s
  simp only [weight, hs, Finset.card_map]

@[simp] theorem weight_mul_monomial (s : σ →₀ ℕ) (P : MvPolynomial σ R) :
    weight (P * (MvPolynomial.monomial s 1 : MvPolynomial σ R)) = weight P := by
  rw [mul_comm]
  exact weight_monomial_mul s P

/-- The product support has no more elements than the set of pairs of terms. -/
theorem weight_mul_le (P Q : MvPolynomial σ R) :
    weight (P * Q) ≤ weight P * weight Q := by
  classical
  unfold weight
  exact (Finset.card_le_card (MvPolynomial.support_mul P Q)).trans
    Finset.card_add_le


end GeneralSupport

section CoefficientMaps

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Coefficient specialization can delete terms but cannot create them. -/
theorem weight_map_le (f : R →+* S) (P : MvPolynomial σ R) :
    weight (MvPolynomial.map f P) ≤ weight P := by
  classical
  exact Finset.card_le_card (MvPolynomial.support_map_subset f P)

/-- Injective coefficient extension preserves the support exactly. -/
theorem weight_map_of_injective (f : R →+* S) (hf : Function.Injective f)
    (P : MvPolynomial σ R) : weight (MvPolynomial.map f P) = weight P := by
  classical
  unfold weight
  rw [MvPolynomial.support_map_of_injective P hf]

end CoefficientMaps

section ScalarMonomials

variable {σ K : Type*} [Field K]

/-- A nonzero scalar monomial translates support bijectively. -/
theorem weight_scalar_monomial_mul (s : σ →₀ ℕ) {c : K} (hc : c ≠ 0)
    (P : MvPolynomial σ K) : weight (MvPolynomial.monomial s c * P) = weight P := by
  classical
  have hs : (MvPolynomial.monomial s c * P).support =
      P.support.map (addLeftEmbedding s) :=
    AddMonoidAlgebra.support_single_mul P c (by simp [hc]) s
  simp only [weight, hs, Finset.card_map]

end ScalarMonomials

end WeightedPilz

