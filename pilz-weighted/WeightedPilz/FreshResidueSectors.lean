import WeightedPilz.Fresh

/-! Aggregate rows occupy disjoint fresh-residue sectors. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

def freshExponentDegree (V : Finset σ) (d : σ →₀ ℕ) : ℕ := ∑ z ∈ V, d z

@[simp] theorem freshExponentDegree_add (V : Finset σ) (a b : σ →₀ ℕ) :
    freshExponentDegree V (a + b) = freshExponentDegree V a + freshExponentDegree V b := by
  simp [freshExponentDegree, Finset.sum_add_distrib]

@[simp] theorem freshExponentDegree_zero (V : Finset σ) : freshExponentDegree V 0 = 0 := by
  simp [freshExponentDegree]

theorem support_mul_fresh_degree (V : Finset σ) (P Q : MvPolynomial σ K) (a b : ℕ)
    (hP : ∀ d ∈ P.support, freshExponentDegree V d = a)
    (hQ : ∀ d ∈ Q.support, freshExponentDegree V d = b) :
    ∀ d ∈ (P * Q).support, freshExponentDegree V d = a + b := by
  intro d hd
  obtain ⟨e, he, f, hf, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hd)
  simp [hP e he, hQ f hf]

theorem support_pow_fresh_degree (V : Finset σ) (P : MvPolynomial σ K) (a n : ℕ)
    (hP : ∀ d ∈ P.support, freshExponentDegree V d = a) :
    ∀ d ∈ (P ^ n).support, freshExponentDegree V d = n * a := by
  classical
  induction n with
  | zero =>
    intro d hd
    have hd0 : d = 0 := by
      simpa only [pow_zero, one_def, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] using hd
    simp [hd0]
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using support_mul_fresh_degree V (P ^ n) P
      (n * a) a ih hP

theorem support_sum_of_pairwise_disjoint {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K)
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
    rw [Finset.sum_insert ha, hadd, ih hsdis,
      Finset.biUnion_insert]

theorem weight_sum_of_pairwise_disjoint {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i).support (f j).support) :
    weight (∑ i ∈ s, f i) = ∑ i ∈ s, weight (f i) := by
  classical
  rw [weight, support_sum_of_pairwise_disjoint s f hdis]
  apply Finset.card_biUnion
  intro i hi j hj hij
  exact hdis i hi j hj hij

namespace FreshData

def PowersInFresh (S : FreshData σ K) (q : ℕ) (A : MvPolynomial σ K) : Prop :=
  ∀ z ∈ S.vars, ∀ d ∈ A.support, q ∣ d z

theorem support_freshSum_degree (S : FreshData σ K) :
    ∀ d ∈ S.freshSum.support, freshExponentDegree S.vars d = 1 := by
  classical
  intro d hd
  rw [S.support_freshSum] at hd
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
  simp [freshExponentDegree, Finsupp.single_apply, hz]

theorem support_freshSum_pow_degree (S : FreshData σ K) (j : ℕ) :
    ∀ d ∈ (S.freshSum ^ j).support, freshExponentDegree S.vars d = j := by
  simpa using support_pow_fresh_degree S.vars S.freshSum 1 j S.support_freshSum_degree

theorem PowersInFresh.degree_dvd {S : FreshData σ K} {q : ℕ} {A : MvPolynomial σ K}
    (hA : S.PowersInFresh q A) {d : σ →₀ ℕ} (hd : d ∈ A.support) :
    q ∣ freshExponentDegree S.vars d := by
  exact Finset.dvd_sum (fun z hz => hA z hz d hd)

theorem aggregate_row_residue (S : FreshData σ K) (q j : ℕ)
    (A : MvPolynomial σ K) (hj : j < q) (hA : S.PowersInFresh q A) :
    ∀ d ∈ (S.freshSum ^ j * A).support, freshExponentDegree S.vars d % q = j := by
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hd)
  rw [freshExponentDegree_add, S.support_freshSum_pow_degree j a ha, Nat.add_mod,
    Nat.mod_eq_zero_of_dvd (hA.degree_dvd hb), add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hj]

theorem aggregate_rows_disjoint (S : FreshData σ K) (q i j : ℕ)
    (A B : MvPolynomial σ K) (hi : i < q) (hj : j < q) (hij : i ≠ j)
    (hA : S.PowersInFresh q A) (hB : S.PowersInFresh q B) :
    Disjoint (S.freshSum ^ i * A).support (S.freshSum ^ j * B).support := by
  apply Finset.disjoint_left.mpr
  intro d hdA hdB
  exact hij ((S.aggregate_row_residue q i A hi hA d hdA).symm.trans
    (S.aggregate_row_residue q j B hj hB d hdB))

theorem aggregate_rows_support (S : FreshData σ K) (q : ℕ)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j < q, S.PowersInFresh q (A j)) :
    (∑ j ∈ Finset.range q, S.freshSum ^ j * A j).support =
      (Finset.range q).biUnion (fun j => (S.freshSum ^ j * A j).support) := by
  apply support_sum_of_pairwise_disjoint
  intro i hi j hj hij
  exact S.aggregate_rows_disjoint q i j (A i) (A j)
    (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    (hA i (Finset.mem_range.mp hi)) (hA j (Finset.mem_range.mp hj))

theorem aggregate_rows_weight (S : FreshData σ K) (q : ℕ)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j < q, S.PowersInFresh q (A j)) :
    weight (∑ j ∈ Finset.range q, S.freshSum ^ j * A j) =
      ∑ j ∈ Finset.range q, weight (S.freshSum ^ j * A j) := by
  apply weight_sum_of_pairwise_disjoint
  intro i hi j hj hij
  exact S.aggregate_rows_disjoint q i j (A i) (A j)
    (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    (hA i (Finset.mem_range.mp hi)) (hA j (Finset.mem_range.mp hj))

theorem aggregate_row_mem_support (S : FreshData σ K) (q : ℕ)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j < q, S.PowersInFresh q (A j))
    {j : ℕ} (hj : j < q) {d : σ →₀ ℕ}
    (hd : d ∈ (S.freshSum ^ j * A j).support) :
    d ∈ (∑ k ∈ Finset.range q, S.freshSum ^ k * A k).support := by
  rw [S.aggregate_rows_support q A hA]
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hd⟩

theorem PowersInFresh.add {S : FreshData σ K} {q : ℕ} {A B : MvPolynomial σ K}
    (hA : S.PowersInFresh q A) (hB : S.PowersInFresh q B) : S.PowersInFresh q (A + B) := by
  intro z hz d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
  · exact hA z hz d hd
  · exact hB z hz d hd

theorem PowersInFresh.mul {S : FreshData σ K} {q : ℕ} {A B : MvPolynomial σ K}
    (hA : S.PowersInFresh q A) (hB : S.PowersInFresh q B) : S.PowersInFresh q (A * B) := by
  intro z hz d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hd)
  exact dvd_add (hA z hz a ha) (hB z hz b hb)

theorem PowersInFresh.neg {S : FreshData σ K} {q : ℕ} {A : MvPolynomial σ K}
    (hA : S.PowersInFresh q A) : S.PowersInFresh q (-A) := by
  intro z hz d hd
  rw [support_neg] at hd
  exact hA z hz d hd

theorem PowersInFresh.pow {S : FreshData σ K} {q : ℕ} {A : MvPolynomial σ K}
    (hA : S.PowersInFresh q A) (n : ℕ) : S.PowersInFresh q (A ^ n) := by
  classical
  induction n with
  | zero =>
    intro z hz d hd
    have hd0 : d = 0 := by
      simpa only [pow_zero, one_def, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] using hd
    simp [hd0]
  | succ n ih => simpa only [pow_succ] using ih.mul hA

theorem PowersInFresh.sum {S : FreshData σ K} {q : ℕ} {ι : Type*}
    (s : Finset ι) (A : ι → MvPolynomial σ K)
    (hA : ∀ j ∈ s, S.PowersInFresh q (A j)) : S.PowersInFresh q (∑ j ∈ s, A j) := by
  intro z hz d hd
  obtain ⟨j, hj, hdj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  exact hA j hj z hz d hdj

theorem core_powersInFresh (S : FreshData σ K) (q : ℕ) : S.PowersInFresh q S.C := by
  intro z hz d hd
  rw [S.independent z hz d hd]
  exact dvd_zero q

theorem aggregate_replacement_powersInFresh (S : FreshData σ K) (q : ℕ)
    (s : Finset ℕ) (A : ℕ → MvPolynomial σ K)
    (hA : ∀ j ∈ s, S.PowersInFresh q (A j)) :
    S.PowersInFresh q (∑ j ∈ s, (-S.C) ^ j * A j) := by
  apply PowersInFresh.sum
  intro j hj
  exact ((S.core_powersInFresh q).neg.pow j).mul (hA j hj)

/-- A polynomial in fresh `q`th powers is disjoint from every positive
aggregate row below degree `q`. -/
theorem disjoint_powers_positive_rows (S : FreshData σ K) (q : ℕ)
    (P : MvPolynomial σ K) (s : Finset ℕ) (A : ℕ → MvPolynomial σ K)
    (hP : S.PowersInFresh q P) (hj : ∀ j ∈ s, 0 < j ∧ j < q)
    (hA : ∀ j ∈ s, S.PowersInFresh q (A j)) :
    Disjoint P.support (∑ j ∈ s, S.freshSum ^ j * A j).support := by
  apply Finset.disjoint_left.mpr
  intro d hdP hdT
  obtain ⟨j, hjmem, hdj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hdT)
  have hzero := Nat.mod_eq_zero_of_dvd (hP.degree_dvd hdP)
  have hrow := S.aggregate_row_residue q j (A j) (hj j hjmem).2 (hA j hjmem) d hdj
  exact (Nat.ne_of_gt (hj j hjmem).1) (hrow.symm.trans hzero)

end FreshData

end WeightedPilz
