import WeightedPilz.Fresh

/-! Disjoint fresh rows and the weight identity in the synchronized normal form. -/

noncomputable section

namespace WeightedPilz

variable {σ K : Type*} [DecidableEq σ] [Field K]

open MvPolynomial
open scoped BigOperators

private theorem support_sum_of_pairwise_disjoint (s : Finset σ) (f : σ → MvPolynomial σ K)
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

namespace FreshData

theorem odd_exponent_freshRow (S : FreshData σ K) (D : MvPolynomial σ K) (hD : S.EvenInFresh D)
    {i : σ} (hi : i ∈ S.vars) {d : σ →₀ ℕ} (hd : d ∈ (X i * D).support) :
    Odd (d i) := by
  classical
  rw [support_X_mul] at hd
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hd
  have h := Nat.odd_add_one.mpr (Nat.not_odd_iff_even.mpr (hD i hi e he))
  simpa [Finsupp.add_apply, Nat.add_comm] using h

theorem even_exponent_freshRow_of_ne (S : FreshData σ K) (D : MvPolynomial σ K) (hD : S.EvenInFresh D)
    (i j : σ) (hj : j ∈ S.vars) (hji : j ≠ i)
    {d : σ →₀ ℕ} (hd : d ∈ (X i * D).support) : Even (d j) := by
  classical
  rw [support_X_mul] at hd
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hd
  simpa [Finsupp.add_apply, hji.symm] using hD j hj e he

theorem freshRows_disjoint (S : FreshData σ K) (D : MvPolynomial σ K) (hD : S.EvenInFresh D)
    {i j : σ} (hi : i ∈ S.vars) (_hj : j ∈ S.vars) (hij : i ≠ j) :
    Disjoint (X i * D).support (X j * D).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hdi hdj
  exact Nat.not_odd_iff_even.mpr
    (S.even_exponent_freshRow_of_ne D hD j i hi hij hdj)
    (S.odd_exponent_freshRow D hD hi hdi)

theorem evenPart_freshRow_disjoint (S : FreshData σ K) (G₀ D : MvPolynomial σ K)
    (hG₀ : S.EvenInFresh G₀) (hD : S.EvenInFresh D)
    {i : σ} (hi : i ∈ S.vars) :
    Disjoint G₀.support (X i * D).support := by
  apply Finset.disjoint_left.mpr
  intro d hd₀ hdi
  exact Nat.not_odd_iff_even.mpr (hG₀ i hi d hd₀) (S.odd_exponent_freshRow D hD hi hdi)

theorem support_freshSum_mul (S : FreshData σ K) (D : MvPolynomial σ K) (hD : S.EvenInFresh D) :
    (S.freshSum * D).support = S.vars.biUnion (fun i => (X i * D).support) := by
  classical
  rw [freshSum, Finset.sum_mul]
  apply support_sum_of_pairwise_disjoint
  intro i hi j hj hij
  exact S.freshRows_disjoint D hD hi hj hij

theorem weight_freshSum_mul (S : FreshData σ K) (D : MvPolynomial σ K) (hD : S.EvenInFresh D) :
    weight (S.freshSum * D) = S.vars.card * weight D := by
  classical
  unfold weight
  rw [S.support_freshSum_mul D hD, Finset.card_biUnion]
  · change (∑ i ∈ S.vars, weight (X i * D)) = S.vars.card * weight D
    simp [MvPolynomial.X, nsmul_eq_mul]
  · intro i hi j hj hij
    exact S.freshRows_disjoint D hD hi hj hij

theorem normalForm_disjoint (S : FreshData σ K) (G₀ D : MvPolynomial σ K)
    (hG₀ : S.EvenInFresh G₀) (hD : S.EvenInFresh D) :
    Disjoint G₀.support (S.freshSum * D).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hd₀ hds
  rw [S.support_freshSum_mul D hD] at hds
  obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp hds
  exact Finset.disjoint_left.mp (S.evenPart_freshRow_disjoint G₀ D hG₀ hD hi) hd₀ hdi

theorem support_normalForm (S : FreshData σ K) (G₀ D : MvPolynomial σ K)
    (hG₀ : S.EvenInFresh G₀) (hD : S.EvenInFresh D) :
    (G₀ + S.freshSum * D).support = G₀.support ∪ (S.freshSum * D).support := by
  exact Finsupp.support_add_eq (S.normalForm_disjoint G₀ D hG₀ hD)

/-- Exact term count of a synchronized normal form. -/
theorem weight_normalForm (S : FreshData σ K) (G₀ D : MvPolynomial σ K)
    (hG₀ : S.EvenInFresh G₀) (hD : S.EvenInFresh D) :
    weight (G₀ + S.freshSum * D) = weight G₀ + S.vars.card * weight D := by
  rw [weight_add_of_disjoint G₀ (S.freshSum * D) (S.normalForm_disjoint G₀ D hG₀ hD),
    S.weight_freshSum_mul D hD]

theorem support_evenPart_subset_normalForm (S : FreshData σ K) (G₀ D : MvPolynomial σ K)
    (hG₀ : S.EvenInFresh G₀) (hD : S.EvenInFresh D) :
    G₀.support ⊆ (G₀ + S.freshSum * D).support := by
  rw [S.support_normalForm G₀ D hG₀ hD]
  exact Finset.subset_union_left

theorem support_freshRow_subset_normalForm (S : FreshData σ K) (G₀ D : MvPolynomial σ K)
    (hG₀ : S.EvenInFresh G₀) (hD : S.EvenInFresh D)
    {i : σ} (hi : i ∈ S.vars) :
    (X i * D).support ⊆ (G₀ + S.freshSum * D).support := by
  classical
  rw [S.support_normalForm G₀ D hG₀ hD, S.support_freshSum_mul D hD]
  intro d hd
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hd⟩)

/-- Every joint base exponent of `D` occurs unchanged in the whole normal
form, because a complete copy of `D` occupies any chosen fresh row. -/
theorem base_exponents_D_normalForm (S : FreshData σ K) (G₀ D : MvPolynomial σ K)
    (hG₀ : S.EvenInFresh G₀) (hD : S.EvenInFresh D)
    {e : σ →₀ ℕ} (he : e ∈ D.support) :
    ∃ d ∈ (G₀ + S.freshSum * D).support,
      ∀ p : σ, p ∉ S.vars → d p = e p := by
  classical
  obtain ⟨i, hi⟩ := S.nonempty
  have hrow : Finsupp.single i 1 + e ∈ (X i * D).support := by
    rw [support_X_mul]
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩
  refine ⟨Finsupp.single i 1 + e,
    S.support_freshRow_subset_normalForm G₀ D hG₀ hD hi hrow, ?_⟩
  intro p hp
  have hpi : p ≠ i := by intro h; subst p; exact hp hi
  simp [Finsupp.add_apply, hpi.symm]

/-- Base-only polynomials have even fresh exponents, independently of the field. -/
theorem BaseOnly.even {S : FreshData σ K} {D : MvPolynomial σ K}
    (hD : S.BaseOnly D) : S.EvenInFresh D := by
  intro z hz d hd
  rw [hD z hz d hd]
  exact ⟨0, rfl⟩

theorem BaseOnly.mul {S : FreshData σ K} {A B : MvPolynomial σ K}
    (hA : S.BaseOnly A) (hB : S.BaseOnly B) : S.BaseOnly (A * B) := by
  intro z hz d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul A B hd)
  simp [Finsupp.add_apply, hA z hz a ha, hB z hz b hb]

/-- Equation `eq:intro-base`: each fresh variable records one complete copy of D. -/
theorem weight_mul_base (S : FreshData σ K) (D : MvPolynomial σ K)
    (hD : S.BaseOnly D) :
    weight (S.F * D) = weight (S.C * D) + S.vars.card * weight D := by
  rw [F, add_mul]
  exact S.weight_normalForm (S.C * D) D
    ((BaseOnly.mul S.independent hD).even) hD.even
end FreshData
end WeightedPilz
