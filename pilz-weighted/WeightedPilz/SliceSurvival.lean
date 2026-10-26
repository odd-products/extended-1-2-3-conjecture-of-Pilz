import WeightedPilz.Frobenius

/-! Surviving homogeneous rows under arbitrary cancellation with a polynomial
occupying fewer rows. The grading can record several coordinates at once. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators Pointwise
variable {σ Γ K : Type*} [AddCommMonoid Γ] [DecidableEq Γ] [Field K]

def PureGrade (f : (σ →₀ ℕ) →+ Γ) (g : Γ) (P : MvPolynomial σ K) : Prop :=
  ∀ d ∈ P.support, f d = g

theorem PureGrade.monomial (f : (σ →₀ ℕ) →+ Γ) (d : σ →₀ ℕ) (c : K) :
    PureGrade f (f d) (monomial d c) := by
  classical
  intro e he
  have heq : e = d := Finset.mem_singleton.mp (support_monomial_subset he)
  simpa only [heq]

theorem PureGrade.mul {f : (σ →₀ ℕ) →+ Γ} {a b : Γ} {P Q : MvPolynomial σ K}
    (hP : PureGrade f a P) (hQ : PureGrade f b Q) : PureGrade f (a + b) (P * Q) := by
  classical
  intro d hd
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  rw [map_add, hP u hu, hQ v hv]

theorem PureGrade.pow {f : (σ →₀ ℕ) →+ Γ} {a : Γ} {P : MvPolynomial σ K}
    (hP : PureGrade f a P) (n : ℕ) : PureGrade f (n • a) (P ^ n) := by
  classical
  induction n with
  | zero =>
      simpa only [pow_zero, zero_nsmul, map_zero] using (PureGrade.monomial f 0 (1 : K))
  | succ n ih =>
      simpa only [pow_succ, succ_nsmul] using ih.mul hP

theorem grade_image_sum_subset {ι : Type*} (f : (σ →₀ ℕ) →+ Γ)
    (I : Finset ι) (g : ι → Γ) (P : ι → MvPolynomial σ K)
    (hP : ∀ i ∈ I, PureGrade f (g i) (P i)) :
    (∑ i ∈ I, P i).support.image f ⊆ I.image g := by
  classical
  intro a ha
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  exact Finset.mem_image.mpr ⟨i, hi, (hP i hi d hdi).symm⟩

theorem grade_image_sum_card_le {ι : Type*} (f : (σ →₀ ℕ) →+ Γ)
    (I : Finset ι) (g : ι → Γ) (P : ι → MvPolynomial σ K)
    (hP : ∀ i ∈ I, PureGrade f (g i) (P i)) :
    ((∑ i ∈ I, P i).support.image f).card ≤ I.card := by
  classical
  exact (Finset.card_le_card (grade_image_sum_subset f I g P hP)).trans (Finset.card_image_le)

/-- Every row whose grade is absent from the other summand survives in full. -/
theorem weight_ge_untouched_graded_blocks {ι : Type*}
    (f : (σ →₀ ℕ) →+ Γ) (I J : Finset ι) (g : ι → Γ)
    (P : MvPolynomial σ K) (Q : ι → MvPolynomial σ K)
    (hJ : J ⊆ I) (hg : Set.InjOn g I)
    (hQ : ∀ i ∈ I, PureGrade f (g i) (Q i))
    (hmiss : ∀ i ∈ J, g i ∉ P.support.image f) :
    (∑ i ∈ J, weight (Q i)) ≤ weight (P + ∑ i ∈ I, Q i) := by
  classical
  have hdis : J.toSet.PairwiseDisjoint (fun i => (Q i).support) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro d hdi hdj
    exact hij (hg (hJ hi) (hJ hj) ((hQ i (hJ hi) d hdi).symm.trans (hQ j (hJ hj) d hdj)))
  have hsurvive : J.biUnion (fun i => (Q i).support) ⊆ (P + ∑ i ∈ I, Q i).support := by
    intro d hd
    obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp hd
    have hdP : d ∉ P.support := by
      intro hdP
      exact hmiss i hi (Finset.mem_image.mpr ⟨d, hdP, hQ i (hJ hi) d hdi⟩)
    have hothers : ∀ j ∈ I, j ≠ i → coeff d (Q j) = 0 := by
      intro j hj hji
      apply notMem_support_iff.mp
      intro hdj
      exact hji (hg hj (hJ hi) ((hQ j hj d hdj).symm.trans (hQ i (hJ hi) d hdi)))
    apply mem_support_iff.mpr
    rw [coeff_add, notMem_support_iff.mp hdP, zero_add, coeff_sum,
      Finset.sum_eq_single i hothers (by intro hn; exact (hn (hJ hi)).elim)]
    exact mem_support_iff.mp hdi
  calc
    _ = (J.biUnion (fun i => (Q i).support)).card := (Finset.card_biUnion hdis).symm
    _ ≤ _ := Finset.card_le_card hsurvive

/-- Six distinct rows with costs at least four, except one of cost at least
three, leave eleven terms after adding any polynomial occupying three rows. -/
theorem six_rows_survive_three (f : (σ →₀ ℕ) →+ Γ)
    (P : MvPolynomial σ K) (Q : Fin 6 → MvPolynomial σ K) (g : Fin 6 → Γ)
    (bad : Fin 6) (hg : Function.Injective g)
    (hQ : ∀ i, PureGrade f (g i) (Q i))
    (hP : (P.support.image f).card ≤ 3)
    (hlow : ∀ i, 3 ≤ weight (Q i))
    (hhigh : ∀ i, i ≠ bad → 4 ≤ weight (Q i)) :
    11 ≤ weight (P + ∑ i, Q i) := by
  classical
  let J : Finset (Fin 6) := Finset.univ.filter (fun i => g i ∉ P.support.image f)
  have hcomp : (Finset.univ \ J).image g ⊆ P.support.image f := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hi' := (Finset.mem_sdiff.mp hi).2
    simpa only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi'
  have hcard : 3 ≤ J.card := by
    have hc := Finset.card_le_card hcomp
    rw [Finset.card_image_of_injective _ hg, Finset.card_sdiff_of_subset (Finset.subset_univ J)] at hc
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    have hle : J.card ≤ 6 := (Finset.card_le_card (Finset.subset_univ J)).trans_eq (by simp)
    omega
  have hsum := weight_ge_untouched_graded_blocks f Finset.univ J g P Q
    (Finset.subset_univ J) hg.injOn (fun i _ => hQ i)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have hbound : 4 * J.card ≤ (∑ i ∈ J, weight (Q i)) + 1 := by
    have hp : ∀ i ∈ J, 4 ≤ weight (Q i) + if i = bad then 1 else 0 := by
      intro i hi
      by_cases hib : i = bad
      · simp only [if_pos hib]
        have := hlow i
        omega
      · simp only [if_neg hib, add_zero]
        exact hhigh i hib
    have hh := Finset.sum_le_sum hp
    simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib] at hh
    have hex : (∑ i ∈ J, if i = bad then 1 else 0) ≤ 1 := by
      simp only [Finset.sum_ite_eq']
      split <;> omega
    omega
  omega

end WeightedPilz
