import Pilz.Basic

/-!
# Full parity classes and the protected-class argument

This file formalizes the support-counting part of Corollary `cor:protection`
of the paper. It does not assume or assert that the residual
decomposition from Proposition `prop:residual` exists.
-/

namespace Pilz

/-- The support of a full parity class. The index records exponent parity
in every variable, including variables absent from the polynomial. -/
noncomputable def paritySupport (P : Poly) (ε : ℕ → ℕ) : Finset (ℕ →₀ ℕ) := by
  classical
  exact P.support.filter fun d => ∀ i, d i % 2 = ε i

/-- The number of terms in a full parity class. -/
noncomputable def classWeight (P : Poly) (ε : ℕ → ℕ) : ℕ :=
  (paritySupport P ε).card

theorem paritySupport_subset (P : Poly) (ε : ℕ → ℕ) :
    paritySupport P ε ⊆ P.support := by
  classical
  exact Finset.filter_subset _ _

theorem classWeight_le_weight (P : Poly) (ε : ℕ → ℕ) :
    classWeight P ε ≤ weight P := by
  exact Finset.card_le_card (paritySupport_subset P ε)

theorem paritySupport_add_subset (P Q : Poly) (ε : ℕ → ℕ) :
    paritySupport (P + Q) ε ⊆ paritySupport P ε ∪ paritySupport Q ε := by
  classical
  intro d hd
  obtain ⟨hd, hpar⟩ := Finset.mem_filter.mp hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hp | hq
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp, hpar⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hq, hpar⟩))

theorem classWeight_add_le (P Q : Poly) (ε : ℕ → ℕ) :
    classWeight (P + Q) ε ≤ classWeight P ε + classWeight Q ε := by
  classical
  exact le_trans (Finset.card_le_card (paritySupport_add_subset P Q ε))
    (Finset.card_union_le _ _)

/-- A residual class costing at least the target cannot be hidden by a
class of capacity at most `r*u` inside a short product. This is the
protected-class inequality, stated with natural-number subtraction
removed so that all boundary cases are explicit. -/
theorem protected_class
    (G₀ C D R : Poly) (ε : ℕ → ℕ) (N m r u : ℕ)
    (hres : R = G₀ + C * D)
    (hshort : m < N)
    (hbudget : weight G₀ + r * u = m)
    (hcap : classWeight (C * D) ε ≤ r * u)
    (hcost : 0 < classWeight R ε → N ≤ classWeight R ε) :
    classWeight R ε = 0 := by
  by_contra hne
  have hpos : 0 < classWeight R ε := Nat.pos_of_ne_zero hne
  have htriangle : classWeight R ε ≤ classWeight G₀ ε + classWeight (C * D) ε := by
    rw [hres]
    exact classWeight_add_le G₀ (C * D) ε
  have hG := classWeight_le_weight G₀ ε
  have hN := hcost hpos
  omega

/-- The stronger threshold in Corollary `cor:protection` (i). -/
theorem protected_class_strict
    (G₀ C D R : Poly) (ε : ℕ → ℕ) (N m r u : ℕ)
    (hres : R = G₀ + C * D)
    (hbudget : weight G₀ + r * u = m)
    (hcap : classWeight (C * D) ε + m < r * u + N)
    (hcost : 0 < classWeight R ε → N ≤ classWeight R ε) :
    classWeight R ε = 0 := by
  by_contra hne
  have hpos : 0 < classWeight R ε := Nat.pos_of_ne_zero hne
  have htriangle : classWeight R ε ≤ classWeight G₀ ε + classWeight (C * D) ε := by
    rw [hres]
    exact classWeight_add_le G₀ (C * D) ε
  have hG := classWeight_le_weight G₀ ε
  have hN := hcost hpos
  omega

/-- Vanishing of all full parity classes implies vanishing of the polynomial. -/
theorem eq_zero_of_all_classWeight_eq_zero (P : Poly)
    (h : ∀ ε, classWeight P ε = 0) : P = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  change P.coeff d = 0
  by_contra hcoeff
  have hmem : d ∈ paritySupport P (fun i => d i % 2) := by
    apply Finset.mem_filter.mpr
    exact ⟨MvPolynomial.mem_support_iff.mpr hcoeff, fun _ => rfl⟩
  have hempty : paritySupport P (fun i => d i % 2) = ∅ :=
    Finset.card_eq_zero.mp (h _)
  rw [hempty] at hmem
  exact Finset.notMem_empty d hmem

end Pilz
