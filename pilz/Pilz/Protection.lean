import Pilz.NormalForm

/-! The summed protected-class inequalities of Corollary `cor:protection`. -/

noncomputable section

namespace Pilz

open scoped BigOperators

theorem classWeight_pos_of_mem_parityIndices {P : Poly} {ε : ℕ →₀ ℕ}
    (hε : ε ∈ parityIndices P) : 0 < classWeight P ε := by
  classical
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hε
  apply Finset.card_pos.mpr
  exact ⟨d, Finset.mem_filter.mpr ⟨hd, fun _ => rfl⟩⟩

theorem sum_classWeights_le (P : Poly) (A : Finset (ℕ →₀ ℕ)) :
    (∑ ε ∈ A, classWeight P ε) ≤ weight P := by
  classical
  have hdis : (A : Set (ℕ →₀ ℕ)).PairwiseDisjoint (fun ε => paritySupport P ε) := by
    intro ε _ η _ hne
    apply Finset.disjoint_left.mpr
    intro d hdε hdη
    apply hne
    ext i
    exact ((Finset.mem_filter.mp hdε).2 i).symm.trans ((Finset.mem_filter.mp hdη).2 i)
  have hs : A.biUnion (fun ε => paritySupport P ε) ⊆ P.support := by
    intro d hd
    obtain ⟨ε, _, hdε⟩ := Finset.mem_biUnion.mp hd
    exact paritySupport_subset P ε hdε
  change (∑ ε ∈ A, (paritySupport P ε).card) ≤ P.support.card
  rw [← Finset.card_biUnion hdis]
  exact Finset.card_le_card hs

/-- A bound on each class bounds its intersection with a polynomial by the
number of occupied classes of that polynomial. -/
theorem support_inter_card_le_classes (P R : Poly) (M : ℕ)
    (hcap : ∀ ε : ℕ → ℕ, classWeight P ε ≤ M) :
    (P.support ∩ R.support).card ≤ (parityIndices R).card * M := by
  classical
  have hs : P.support ∩ R.support ⊆
      (parityIndices R).biUnion (fun ε => paritySupport P ε) := by
    intro d hd
    obtain ⟨hdP, hdR⟩ := Finset.mem_inter.mp hd
    apply Finset.mem_biUnion.mpr
    exact ⟨parityExponent d, Finset.mem_image.mpr ⟨d, hdR, rfl⟩,
      Finset.mem_filter.mpr ⟨hdP, fun _ => rfl⟩⟩
  exact (Finset.card_le_card hs).trans
    (Finset.card_biUnion_le_card_mul _ _ M (fun ε _ => hcap ε))

theorem residual_weight_lower (R : Poly) (N : ℕ)
    (hcost : ∀ ε : ℕ → ℕ, 0 < classWeight R ε → N ≤ classWeight R ε) :
    (parityIndices R).card * N ≤ weight R := by
  classical
  rw [← sum_classWeights R]
  calc
    (parityIndices R).card * N = ∑ _ε ∈ parityIndices R, N := by simp
    _ ≤ ∑ ε ∈ parityIndices R, classWeight R ε :=
      Finset.sum_le_sum (fun _ hε => hcost _ (classWeight_pos_of_mem_parityIndices hε))

/-- Natural-number form of `wt(Q) ≥ wt(P) + a(N−2M)`, valid even when
`N < 2M`, with no truncated subtraction. -/
theorem protected_classes_weight (P Q R : Poly) (N M : ℕ)
    (hres : R = Q + P)
    (hcap : ∀ ε : ℕ → ℕ, classWeight P ε ≤ M)
    (hcost : ∀ ε : ℕ → ℕ, 0 < classWeight R ε → N ≤ classWeight R ε) :
    weight P + (parityIndices R).card * N ≤
      weight Q + 2 * ((parityIndices R).card * M) := by
  have hQ : P + R = Q := by
    rw [hres, add_left_comm P Q P, CharTwo.add_self_eq_zero, add_zero]
  have hc := weight_add_cancellation P R
  rw [hQ] at hc
  have hi := support_inter_card_le_classes P R M hcap
  have hr := residual_weight_lower R N hcost
  omega

/-- The occupied residual classes use at least `a(N−M)` terms of the core
part, again expressed without subtraction. -/
theorem protected_classes_core (P Q R : Poly) (N M : ℕ)
    (hres : R = Q + P)
    (hcap : ∀ ε : ℕ → ℕ, classWeight P ε ≤ M)
    (hcost : ∀ ε : ℕ → ℕ, 0 < classWeight R ε → N ≤ classWeight R ε) :
    (parityIndices R).card * N ≤ weight Q + (parityIndices R).card * M := by
  classical
  have hbound : ∑ ε ∈ parityIndices R, classWeight R ε ≤
      ∑ ε ∈ parityIndices R, (classWeight Q ε + M) := by
    apply Finset.sum_le_sum
    intro ε _
    rw [hres]
    exact (classWeight_add_le Q P ε).trans (Nat.add_le_add_left (hcap ε) _)
  rw [sum_classWeights, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hbound
  have hR := residual_weight_lower R N hcost
  have hQ := sum_classWeights_le Q (parityIndices R)
  omega

namespace FreshData

theorem evenInFresh_C_mul (S : FreshData) (D : Poly) (hD : S.EvenInFresh D) :
    S.EvenInFresh (S.C * D) := by
  apply (S.evenInFresh_iff_pderiv_eq_zero _).mpr
  intro z hz
  rw [MvPolynomial.pderiv_mul,
    pderiv_eq_zero_of_exponent_zero S.C z (S.independent z hz),
    (S.evenInFresh_iff_pderiv_eq_zero D).mp hD z hz, zero_mul, mul_zero, add_zero]

theorem weight_F_mul_even (S : FreshData) (D : Poly) (hD : S.EvenInFresh D) :
    weight (S.F * D) = weight (S.C * D) + S.vars.card * weight D := by
  rw [FreshData.F, add_mul]
  exact S.weight_normalForm _ _ (S.evenInFresh_C_mul D hD) hD

end FreshData

/-- Corollary `cor:protection` (ii), first inequality. -/
theorem normalForm_protected_weight (S : FreshData) (N : ℕ) (nf : NormalFormData S N)
    (hN : N ≤ weight S.C + S.vars.card) (M : ℕ)
    (hcap : ∀ ε : ℕ → ℕ, classWeight (S.C * nf.D) ε ≤ M) :
    weight (S.F * nf.D) + (parityIndices (nf.G₀ + S.C * nf.D)).card * N ≤
      weight nf.G + 2 * ((parityIndices (nf.G₀ + S.C * nf.D)).card * M) := by
  have hh := protected_classes_weight (S.C * nf.D) nf.G₀
    (nf.G₀ + S.C * nf.D) N M rfl hcap (normalForm_residual_cost S N nf hN)
  rw [S.weight_F_mul_even nf.D nf.evenD]
  have hw := normalForm_weight S N nf
  omega

/-- Corollary `cor:protection` (ii), second inequality. -/
theorem normalForm_protected_core (S : FreshData) (N : ℕ) (nf : NormalFormData S N)
    (hN : N ≤ weight S.C + S.vars.card) (M : ℕ)
    (hcap : ∀ ε : ℕ → ℕ, classWeight (S.C * nf.D) ε ≤ M) :
    (parityIndices (nf.G₀ + S.C * nf.D)).card * N ≤
      weight nf.G₀ + (parityIndices (nf.G₀ + S.C * nf.D)).card * M :=
  protected_classes_core _ _ _ N M rfl hcap (normalForm_residual_cost S N nf hN)

/-- Corollary `cor:protection` (iii), first alternative. -/
theorem normalForm_excluded_of_twice_capacity (S : FreshData) (N : ℕ)
    (nf : NormalFormData S N) (hN : N ≤ weight S.C + S.vars.card) (M : ℕ)
    (hcap : ∀ ε : ℕ → ℕ, classWeight (S.C * nf.D) ε ≤ M)
    (hNM : 2 * M ≤ N) (hprod : N ≤ weight (S.F * nf.D)) : False := by
  have hh := normalForm_protected_weight S N nf hN M hcap
  have hm := Nat.mul_le_mul_left (parityIndices (nf.G₀ + S.C * nf.D)).card hNM
  have hshort := nf.extremal.1.2.2
  nlinarith

/-- Corollary `cor:protection` (iii), at most one residual class. -/
theorem normalForm_excluded_of_one_class (S : FreshData) (N : ℕ)
    (nf : NormalFormData S N) (hN : N ≤ weight S.C + S.vars.card) (M : ℕ)
    (hcap : ∀ ε : ℕ → ℕ, classWeight (S.C * nf.D) ε ≤ M)
    (ha : (parityIndices (nf.G₀ + S.C * nf.D)).card ≤ 1)
    (hprodN : N ≤ weight (S.F * nf.D))
    (hprodM : 2 * M ≤ weight (S.F * nf.D)) : False := by
  have hh := normalForm_protected_weight S N nf hN M hcap
  have hshort := nf.extremal.1.2.2
  have ha' : (parityIndices (nf.G₀ + S.C * nf.D)).card = 0 ∨
      (parityIndices (nf.G₀ + S.C * nf.D)).card = 1 := by omega
  rcases ha' with hz | ho
  · rw [hz] at hh
    omega
  · rw [ho] at hh
    omega

end Pilz
