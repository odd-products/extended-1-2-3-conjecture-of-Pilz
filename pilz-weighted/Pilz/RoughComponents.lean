import Pilz.SmoothParts
import Pilz.Slices
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Exact rough-component decomposition

Unique arithmetic smooth/rough factorization groups the interval polynomial
by its rough part. A multiplier in the smooth variables preserves these
disjoint fibers, so their actual weights add exactly.
-/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

theorem smoothInterval_vars_subset (T : Finset ℕ) (n : ℕ) :
    (smoothInterval T n).vars ⊆ T := by
  classical
  intro p hp
  obtain ⟨d, hd, hdp⟩ := (MvPolynomial.mem_vars p).mp hp
  have hpos : ∀ a ∈ smoothNumbers T n, 0 < a :=
    fun a ha => ((mem_smoothNumbers T n a).mp ha).1
  rw [smoothInterval, support_polynomialOf _ hpos] at hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  exact ((mem_smoothNumbers T n a).mp ha).2.2 hdp

/-- The interval sum is reindexed by the unique rough/smooth pair. -/
theorem interval_sum_rough_smooth (T : Finset ℕ) (n : ℕ)
    (hT : ∀ p ∈ T, Nat.Prime p) :
    interval n = ∑ b ∈ roughNumbers T n,
      ∑ c ∈ smoothNumbers T (n / b), monomialOf (b * c) := by
  classical
  have hsum : (∑ a ∈ Finset.Icc 1 n, monomialOf a) =
      ∑ bc ∈ (roughNumbers T n).sigma (fun b => smoothNumbers T (n / b)),
        monomialOf (bc.1 * bc.2) := by
    apply Finset.sum_bij (fun a _ => (⟨roughFactor T a, smoothFactor T a⟩ : Σ _ : ℕ, ℕ))
    · intro a ha
      exact Finset.mem_sigma.mpr ⟨roughFactor_mem T hT ha, smoothFactor_mem T ha⟩
    · intro a ha b hb hparts
      have hrough := congrArg Sigma.fst hparts
      have hsmooth := congrArg (fun bc : (Σ _ : ℕ, ℕ) => bc.2) hparts
      calc
        a = roughFactor T a * smoothFactor T a :=
          (roughFactor_mul_smoothFactor T (ne_of_gt (Finset.mem_Icc.mp ha).1)).symm
        _ = roughFactor T b * smoothFactor T b := congrArg₂ (· * ·) hrough hsmooth
        _ = b := roughFactor_mul_smoothFactor T (ne_of_gt (Finset.mem_Icc.mp hb).1)
    · rintro ⟨b, c⟩ hbc
      obtain ⟨hb, hc⟩ := Finset.mem_sigma.mp hbc
      obtain ⟨hbpos, _hbn, hbrough⟩ := (mem_roughNumbers T n b).mp hb
      obtain ⟨hcpos, hcn, hcsmooth⟩ := (mem_smoothNumbers T (n / b) c).mp hc
      have hprod : b * c ∈ Finset.Icc 1 n := by
        apply Finset.mem_Icc.mpr
        refine ⟨Nat.mul_pos hbpos hcpos, ?_⟩
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hbpos).mp hcn
      refine ⟨b * c, hprod, ?_⟩
      rw [roughFactor_mul_of_rough_smooth T hbpos hcpos hbrough hcsmooth,
        smoothFactor_mul_of_rough_smooth T hbpos hcpos hbrough hcsmooth]
    · intro a ha
      rw [roughFactor_mul_smoothFactor T (ne_of_gt (Finset.mem_Icc.mp ha).1)]
  exact hsum.trans (Finset.sum_sigma _ _ _)

/-- The polynomial form of the paper's rough decomposition, before multiplying. -/
theorem interval_eq_rough_components (T : Finset ℕ) (n : ℕ)
    (hT : ∀ p ∈ T, Nat.Prime p) :
    interval n = ∑ b ∈ roughNumbers T n, monomialOf b * smoothInterval T (n / b) := by
  classical
  rw [interval_sum_rough_smooth T n hT]
  apply Finset.sum_congr rfl
  intro b hb
  rw [smoothInterval, polynomialOf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  exact monomialOf_mul (ne_of_gt ((mem_roughNumbers T n b).mp hb).1)
    (ne_of_gt ((mem_smoothNumbers T (n / b) c).mp hc).1)

theorem interval_mul_eq_rough_components (T : Finset ℕ) (n : ℕ) (D : Poly)
    (hT : ∀ p ∈ T, Nat.Prime p) :
    interval n * D = ∑ b ∈ roughNumbers T n,
      monomialOf b * (smoothInterval T (n / b) * D) := by
  rw [interval_eq_rough_components T n hT, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  exact mul_assoc _ _ _

theorem outsideExponent_roughFactor (T : Finset ℕ) (b : ℕ)
    (hb : ∀ p ∈ T, ¬p ∣ b) : outsideExponent T b.factorization = b.factorization :=
  outsideFactorization_eq_self_of_rough T b hb

theorem rough_row_outsideExponent (T : Finset ℕ) (b : ℕ) (P : Poly)
    (hb : ∀ p ∈ T, ¬p ∣ b) (hP : P.vars ⊆ T)
    {d : ℕ →₀ ℕ} (hd : d ∈ (monomialOf b * P).support) :
    outsideExponent T d = b.factorization := by
  classical
  have hs : (monomialOf b * P).support =
      P.support.map (addLeftEmbedding b.factorization) :=
    AddMonoidAlgebra.support_single_mul P 1 (by simp) b.factorization
  rw [hs] at hd
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hd
  change outsideExponent T (b.factorization + e) = b.factorization
  rw [outsideExponent_add, outsideExponent_roughFactor T b hb,
    (vars_subset_iff_outsideExponent_zero T P).mp hP e he, add_zero]

theorem rough_rows_disjoint (T : Finset ℕ) (b c : ℕ) (P Q : Poly)
    (hbpos : 0 < b) (hcpos : 0 < c)
    (hb : ∀ p ∈ T, ¬p ∣ b) (hc : ∀ p ∈ T, ¬p ∣ c)
    (hP : P.vars ⊆ T) (hQ : Q.vars ⊆ T) (hbc : b ≠ c) :
    Disjoint (monomialOf b * P).support (monomialOf c * Q).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hdb hdc
  have heq : b.factorization = c.factorization :=
    (rough_row_outsideExponent T b P hb hP hdb).symm.trans
      (rough_row_outsideExponent T c Q hc hQ hdc)
  exact hbc (Nat.factorization_inj (ne_of_gt hbpos) (ne_of_gt hcpos) heq)

private theorem support_sum_of_disjoint (s : Finset ℕ) (f : ℕ → Poly)
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

theorem weight_sum_of_disjoint_support (s : Finset ℕ) (f : ℕ → Poly)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i).support (f j).support) :
    weight (∑ i ∈ s, f i) = ∑ i ∈ s, weight (f i) := by
  classical
  unfold weight
  rw [support_sum_of_disjoint s f hdis]
  exact Finset.card_biUnion hdis

theorem smoothComponent_vars_subset (T : Finset ℕ) (j : ℕ) (D : Poly)
    (hD : D.vars ⊆ T) : (smoothInterval T j * D).vars ⊆ T := by
  exact (MvPolynomial.vars_mul _ _).trans
    (Finset.union_subset (smoothInterval_vars_subset T j) hD)

/-- The exact weight sum in equation `eq:rough-decomposition` of the paper. -/
theorem weight_interval_mul_eq_sum_rough_components (T : Finset ℕ) (n : ℕ) (D : Poly)
    (hT : ∀ p ∈ T, Nat.Prime p) (hD : D.vars ⊆ T) :
    weight (interval n * D) = ∑ b ∈ roughNumbers T n,
      weight (smoothInterval T (n / b) * D) := by
  classical
  rw [interval_mul_eq_rough_components T n D hT]
  calc
    weight (∑ b ∈ roughNumbers T n, monomialOf b * (smoothInterval T (n / b) * D)) =
        ∑ b ∈ roughNumbers T n, weight (monomialOf b * (smoothInterval T (n / b) * D)) := by
      apply weight_sum_of_disjoint_support
      intro b hb c hc hbc
      obtain ⟨hbpos, _hbn, hbrough⟩ := (mem_roughNumbers T n b).mp hb
      obtain ⟨hcpos, _hcn, hcrough⟩ := (mem_roughNumbers T n c).mp hc
      exact rough_rows_disjoint T b c _ _ hbpos hcpos hbrough hcrough
        (smoothComponent_vars_subset T (n / b) D hD)
        (smoothComponent_vars_subset T (n / c) D hD) hbc
    _ = ∑ b ∈ roughNumbers T n, weight (smoothInterval T (n / b) * D) := by
      apply Finset.sum_congr rfl
      intro b _
      exact weight_monomial_mul b.factorization _

end Pilz
