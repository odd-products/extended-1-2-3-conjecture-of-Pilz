import Pilz.FreshAlgebra
import Pilz.Support
import Mathlib.Tactic.FinCases

/-!
# Products separated by independent base variables

If the variables of `P` lie in `B` and `Q` is independent of every variable
in `B`, different monomials of `P` produce disjoint copies of `Q`. This is
the separated-base-row argument in the cofactor-width step of Section 3.
-/

noncomputable section

namespace Pilz

open scoped BigOperators

theorem IndependentOf.add {P Q : Poly} {z : ℕ}
    (hP : IndependentOf P z) (hQ : IndependentOf Q z) :
    IndependentOf (P + Q) z := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hp | hq
  · exact hP d hp
  · exact hQ d hq

theorem IndependentOf.mul {P Q : Poly} {z : ℕ}
    (hP : IndependentOf P z) (hQ : IndependentOf Q z) :
    IndependentOf (P * Q) z := by
  intro d hd
  obtain ⟨e, he, f, hf, rfl⟩ :=
    Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simp [Finsupp.add_apply, hP e he, hQ f hf]

/-- Outside the chosen base, every exponent occurring in `P` is zero. -/
theorem exponent_zero_of_vars_subset {P : Poly} {B : Finset ℕ}
    (hP : P.vars ⊆ B) {d : ℕ →₀ ℕ} (hd : d ∈ P.support)
    {p : ℕ} (hp : p ∉ B) : d p = 0 := by
  apply MvPolynomial.mem_support_notMem_vars_zero hd
  exact fun hm => hp (hP hm)

theorem support_monomial_one_mul (d : ℕ →₀ ℕ) (Q : Poly) :
    (MvPolynomial.monomial d 1 * Q).support =
      Q.support.map (addLeftEmbedding d) :=
  AddMonoidAlgebra.support_single_mul Q 1 (by simp) d

theorem mem_support_monomial_one_mul {d e : ℕ →₀ ℕ} {Q : Poly} :
    e ∈ (MvPolynomial.monomial d 1 * Q).support ↔
      ∃ q ∈ Q.support, d + q = e := by
  classical
  rw [support_monomial_one_mul, Finset.mem_map]
  rfl

/-- Distinct base monomials produce disjoint product rows. -/
theorem base_rows_disjoint {P Q : Poly} {B : Finset ℕ}
    (hP : P.vars ⊆ B) (hQ : ∀ p ∈ B, IndependentOf Q p)
    {d e : ℕ →₀ ℕ} (hd : d ∈ P.support) (he : e ∈ P.support) (hne : d ≠ e) :
    Disjoint (MvPolynomial.monomial d 1 * Q).support
      (MvPolynomial.monomial e 1 * Q).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro t htd hte
  obtain ⟨q, hq, hqt⟩ := mem_support_monomial_one_mul.mp htd
  obtain ⟨r, hr, hrt⟩ := mem_support_monomial_one_mul.mp hte
  apply hne
  ext p
  by_cases hp : p ∈ B
  · have hh := congrArg (fun u : ℕ →₀ ℕ => u p) (hqt.trans hrt.symm)
    simpa [Finsupp.add_apply, hQ p hp q hq, hQ p hp r hr] using hh
  · rw [exponent_zero_of_vars_subset hP hd hp,
      exponent_zero_of_vars_subset hP he hp]

private theorem support_sum_of_disjoint {α : Type*} (s : Finset α) (f : α → Poly)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i).support (f j).support) :
    (∑ i ∈ s, f i).support = s.biUnion (fun i => (f i).support) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hsdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i).support (f j).support := by
      intro i hi j hj hij
      exact hdis i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hsumdis : Disjoint (f a).support (∑ i ∈ s, f i).support := by
      apply Finset.disjoint_left.mpr
      intro d hda hds
      obtain ⟨j, hj, hdj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hds)
      have haj : a ≠ j := by intro h; subst j; exact ha hj
      exact Finset.disjoint_left.mp
        (hdis a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) haj) hda hdj
    have hadd : (f a + ∑ i ∈ s, f i).support =
        (f a).support ∪ (∑ i ∈ s, f i).support := Finsupp.support_add_eq hsumdis
    rw [Finset.sum_insert ha, hadd, ih hsdis, Finset.biUnion_insert]

private theorem nonzero_coefficient_eq_one {c : ZMod 2} (hc : c ≠ 0) : c = 1 := by
  fin_cases c <;> simp_all

theorem as_sum_monomial_one (P : Poly) :
    P = ∑ d ∈ P.support, MvPolynomial.monomial d 1 := by
  classical
  calc
    P = ∑ d ∈ P.support, MvPolynomial.monomial d (MvPolynomial.coeff d P) := P.as_sum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [nonzero_coefficient_eq_one (MvPolynomial.mem_support_iff.mp hd)]

theorem support_mul_independent_base (P Q : Poly) (B : Finset ℕ)
    (hP : P.vars ⊆ B) (hQ : ∀ p ∈ B, IndependentOf Q p) :
    (P * Q).support =
      P.support.biUnion (fun d => (MvPolynomial.monomial d 1 * Q).support) := by
  classical
  have hmul : P * Q = ∑ d ∈ P.support, MvPolynomial.monomial d 1 * Q := by
    calc
      P * Q = (∑ d ∈ P.support, MvPolynomial.monomial d 1) * Q :=
        congrArg (fun R : Poly => R * Q) (as_sum_monomial_one P)
      _ = _ := Finset.sum_mul _ _ _
  rw [hmul]
  apply support_sum_of_disjoint
  intro d hd e he hne
  exact base_rows_disjoint hP hQ hd he hne

/-- No cancellation occurs across the independent base rows. -/
theorem weight_mul_independent_base (P Q : Poly) (B : Finset ℕ)
    (hP : P.vars ⊆ B) (hQ : ∀ p ∈ B, IndependentOf Q p) :
    weight (P * Q) = weight P * weight Q := by
  classical
  unfold weight
  rw [support_mul_independent_base P Q B hP hQ, Finset.card_biUnion]
  · change (∑ d ∈ P.support, weight (MvPolynomial.monomial d 1 * Q)) =
      P.support.card * weight Q
    simp [weight_monomial_mul, Finset.sum_const, nsmul_eq_mul]
  · intro d hd e he hne
    exact base_rows_disjoint hP hQ hd he hne

/-- A nonconstant base row cannot meet a polynomial independent of the base. -/
theorem row_disjoint_independent_base {P Q R : Poly} {B : Finset ℕ}
    (hP : P.vars ⊆ B) (hQ : ∀ p ∈ B, IndependentOf Q p)
    (hR : ∀ p ∈ B, IndependentOf R p) {d : ℕ →₀ ℕ}
    (hd : d ∈ P.support) (hdzero : d ≠ 0) :
    Disjoint (MvPolynomial.monomial d 1 * Q).support R.support := by
  classical
  obtain ⟨p, hdp⟩ := Finsupp.ne_iff.mp hdzero
  have hp : p ∈ B := by
    by_contra hp
    exact hdp (exponent_zero_of_vars_subset hP hd hp)
  apply Finset.disjoint_left.mpr
  intro t hrow htR
  obtain ⟨q, hq, rfl⟩ := mem_support_monomial_one_mul.mp hrow
  have htzero := hR p hp (d + q) htR
  have hqzero := hQ p hp q hq
  simp only [Finsupp.add_apply, hqzero, add_zero] at htzero
  exact hdp htzero

/-- Every row is nonconstant if the constant coefficient of `P` is zero. -/
theorem mul_disjoint_independent_base (P Q R : Poly) (B : Finset ℕ)
    (hP : P.vars ⊆ B) (hPzero : MvPolynomial.coeff 0 P = 0)
    (hQ : ∀ p ∈ B, IndependentOf Q p)
    (hR : ∀ p ∈ B, IndependentOf R p) :
    Disjoint (P * Q).support R.support := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht htR
  rw [support_mul_independent_base P Q B hP hQ] at ht
  obtain ⟨d, hd, hrow⟩ := Finset.mem_biUnion.mp ht
  have hd0 : d ≠ 0 := by
    intro heq
    subst d
    exact (MvPolynomial.mem_support_iff.mp hd) hPzero
  exact Finset.disjoint_left.mp
    (row_disjoint_independent_base hP hQ hR hd hd0) hrow htR

end Pilz
