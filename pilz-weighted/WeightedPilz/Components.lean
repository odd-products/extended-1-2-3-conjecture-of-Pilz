import WeightedPilz.Basic
import WeightedPilz.Support
import WeightedPilz.VariableSlices
import Pilz.SmoothParts
import Pilz.ComponentCounts
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Weighted rough-component decomposition

The arithmetic smooth/rough factorization is independent of the coefficient
field. A component with rough part `b` inherits weight `c (b*a)` at its smooth
index `a`; the weights need not agree between distinct components.
-/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators
open Pilz (roughNumbers roughCount roughIntervalCount smoothNumbers Smooth
  roughFactor smoothFactor mem_roughNumbers mem_smoothNumbers)

variable {K : Type*} [Field K]

def smoothInterval (T : Finset ℕ) (j : ℕ) (c : ℕ → K) : Poly K :=
  polynomialOf (smoothNumbers T j) c

theorem smoothInterval_vars_subset (T : Finset ℕ) (j : ℕ) (c : ℕ → K) :
    (smoothInterval T j c).vars ⊆ T := by
  classical
  intro p hp
  obtain ⟨d, hd, hdp⟩ := (MvPolynomial.mem_vars p).mp hp
  change d ∈ (∑ a ∈ smoothNumbers T j,
    MvPolynomial.monomial a.factorization (c a)).support at hd
  obtain ⟨a, ha, hda⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  have hdf : d = a.factorization :=
    Finset.mem_singleton.mp (Finsupp.support_single_subset hda)
  subst d
  exact ((mem_smoothNumbers T j a).mp ha).2.2 hdp

/-- The weights inherited by a component remain nonzero at every allowed index. -/
theorem component_weights_nonzero (T : Finset ℕ) (n b : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hb : b ∈ roughNumbers T n) :
    ∀ a ∈ smoothNumbers T (n / b), c (b * a) ≠ 0 := by
  intro a ha
  obtain ⟨hbpos, _, _⟩ := (mem_roughNumbers T n b).mp hb
  obtain ⟨hapos, han, _⟩ := (mem_smoothNumbers T (n / b) a).mp ha
  apply hc
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.mul_pos hbpos hapos, ?_⟩
  simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hbpos).mp han

theorem interval_sum_rough_smooth (T : Finset ℕ) (n : ℕ) (c : ℕ → K)
    (hT : ∀ p ∈ T, Nat.Prime p) :
    interval n c = ∑ b ∈ roughNumbers T n,
      ∑ a ∈ smoothNumbers T (n / b),
        MvPolynomial.monomial (b * a).factorization (c (b * a)) := by
  classical
  have hsum : (∑ a ∈ Finset.Icc 1 n, MvPolynomial.monomial a.factorization (c a)) =
      ∑ ba ∈ (roughNumbers T n).sigma (fun b => smoothNumbers T (n / b)),
        MvPolynomial.monomial (ba.1 * ba.2).factorization (c (ba.1 * ba.2)) := by
    apply Finset.sum_bij (fun a _ => (⟨roughFactor T a, smoothFactor T a⟩ : Σ _ : ℕ, ℕ))
    · intro a ha
      exact Finset.mem_sigma.mpr ⟨Pilz.roughFactor_mem T hT ha, Pilz.smoothFactor_mem T ha⟩
    · intro a ha b hb hparts
      have hrough := congrArg Sigma.fst hparts
      have hsmooth := congrArg (fun ba : (Σ _ : ℕ, ℕ) => ba.2) hparts
      calc
        a = roughFactor T a * smoothFactor T a :=
          (Pilz.roughFactor_mul_smoothFactor T (ne_of_gt (Finset.mem_Icc.mp ha).1)).symm
        _ = roughFactor T b * smoothFactor T b := congrArg₂ (· * ·) hrough hsmooth
        _ = b := Pilz.roughFactor_mul_smoothFactor T (ne_of_gt (Finset.mem_Icc.mp hb).1)
    · rintro ⟨b, a⟩ hba
      obtain ⟨hb, ha⟩ := Finset.mem_sigma.mp hba
      obtain ⟨hbpos, _, hbrough⟩ := (mem_roughNumbers T n b).mp hb
      obtain ⟨hapos, han, hasmooth⟩ := (mem_smoothNumbers T (n / b) a).mp ha
      have hprod : b * a ∈ Finset.Icc 1 n := by
        apply Finset.mem_Icc.mpr
        refine ⟨Nat.mul_pos hbpos hapos, ?_⟩
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hbpos).mp han
      refine ⟨b * a, hprod, ?_⟩
      rw [Pilz.roughFactor_mul_of_rough_smooth T hbpos hapos hbrough hasmooth,
        Pilz.smoothFactor_mul_of_rough_smooth T hbpos hapos hbrough hasmooth]
    · intro a ha
      rw [Pilz.roughFactor_mul_smoothFactor T (ne_of_gt (Finset.mem_Icc.mp ha).1)]
  exact hsum.trans (Finset.sum_sigma _ _ _)

/-- Each rough row has its own inherited coefficient function. -/
theorem interval_eq_rough_components (T : Finset ℕ) (n : ℕ) (c : ℕ → K)
    (hT : ∀ p ∈ T, Nat.Prime p) :
    interval n c = ∑ b ∈ roughNumbers T n,
      monomialOf b * smoothInterval T (n / b) (fun a => c (b * a)) := by
  classical
  rw [interval_sum_rough_smooth T n c hT]
  apply Finset.sum_congr rfl
  intro b hb
  rw [smoothInterval, polynomialOf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hb0 : b ≠ 0 := ne_of_gt ((mem_roughNumbers T n b).mp hb).1
  have ha0 : a ≠ 0 := ne_of_gt ((mem_smoothNumbers T (n / b) a).mp ha).1
  simp only [monomialOf, Nat.factorization_mul hb0 ha0,
    MvPolynomial.monomial_mul, one_mul]

theorem interval_mul_eq_rough_components (T : Finset ℕ) (n : ℕ)
    (c : ℕ → K) (D : Poly K) (hT : ∀ p ∈ T, Nat.Prime p) :
    interval n c * D = ∑ b ∈ roughNumbers T n,
      monomialOf b * (smoothInterval T (n / b) (fun a => c (b * a)) * D) := by
  rw [interval_eq_rough_components T n c hT, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  exact mul_assoc _ _ _

theorem rough_row_outsideExponent (T : Finset ℕ) (b : ℕ) (P : Poly K)
    (hb : ∀ p ∈ T, ¬p ∣ b) (hP : P.vars ⊆ T)
    {d : ℕ →₀ ℕ} (hd : d ∈ (monomialOf b * P).support) :
    outsideExponent (T : Set ℕ) d = b.factorization := by
  classical
  have hs : (monomialOf b * P).support =
      P.support.map (addLeftEmbedding b.factorization) :=
    AddMonoidAlgebra.support_single_mul P 1 (by simp) b.factorization
  rw [hs] at hd
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hd
  change outsideExponent (T : Set ℕ) (b.factorization + e) = b.factorization
  rw [outsideExponent_add,
    (show outsideExponent (T : Set ℕ) b.factorization = b.factorization from
      by simpa only [outsideExponent, Finset.mem_coe] using
        Pilz.outsideFactorization_eq_self_of_rough T b hb),
    (vars_subset_iff_outsideExponent_zero (T : Set ℕ) P).mp hP e he, add_zero]

theorem rough_rows_disjoint (T : Finset ℕ) (b a : ℕ) (P Q : Poly K)
    (hbpos : 0 < b) (hapos : 0 < a)
    (hb : ∀ p ∈ T, ¬p ∣ b) (ha : ∀ p ∈ T, ¬p ∣ a)
    (hP : P.vars ⊆ T) (hQ : Q.vars ⊆ T) (hba : b ≠ a) :
    Disjoint (monomialOf b * P).support (monomialOf a * Q).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hdb hda
  have heq : b.factorization = a.factorization :=
    (rough_row_outsideExponent T b P hb hP hdb).symm.trans
      (rough_row_outsideExponent T a Q ha hQ hda)
  exact hba (Nat.factorization_inj (ne_of_gt hbpos) (ne_of_gt hapos) heq)

theorem weight_sum_of_disjoint_support (s : Finset ℕ) (f : ℕ → Poly K)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i).support (f j).support) :
    weight (∑ i ∈ s, f i) = ∑ i ∈ s, weight (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weight]
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
    rw [Finset.sum_insert ha, weight_add_of_disjoint _ _ hsumdis,
      ih hsdis, Finset.sum_insert ha]

theorem smoothComponent_vars_subset (T : Finset ℕ) (j : ℕ) (c : ℕ → K) (D : Poly K)
    (hD : D.vars ⊆ T) : (smoothInterval T j c * D).vars ⊆ T :=
  (MvPolynomial.vars_mul _ _).trans
    (Finset.union_subset (smoothInterval_vars_subset T j c) hD)

/-- The exact weighted equation `arith:eq:prime-rank-decomposition`. -/
theorem weight_interval_mul_eq_sum_rough_components (T : Finset ℕ) (n : ℕ)
    (c : ℕ → K) (D : Poly K) (hT : ∀ p ∈ T, Nat.Prime p) (hD : D.vars ⊆ T) :
    weight (interval n c * D) = ∑ b ∈ roughNumbers T n,
      weight (smoothInterval T (n / b) (fun a => c (b * a)) * D) := by
  classical
  rw [interval_mul_eq_rough_components T n c D hT]
  calc
    weight (∑ b ∈ roughNumbers T n,
        monomialOf b * (smoothInterval T (n / b) (fun a => c (b * a)) * D)) =
        ∑ b ∈ roughNumbers T n,
          weight (monomialOf b * (smoothInterval T (n / b) (fun a => c (b * a)) * D)) := by
      apply weight_sum_of_disjoint_support
      intro b hb a ha hba
      obtain ⟨hbpos, _, hbrough⟩ := (mem_roughNumbers T n b).mp hb
      obtain ⟨hapos, _, harough⟩ := (mem_roughNumbers T n a).mp ha
      exact rough_rows_disjoint T b a _ _ hbpos hapos hbrough harough
        (smoothComponent_vars_subset T (n / b) _ D hD)
        (smoothComponent_vars_subset T (n / a) _ D hD) hba
    _ = ∑ b ∈ roughNumbers T n,
        weight (smoothInterval T (n / b) (fun a => c (b * a)) * D) := by
      apply Finset.sum_congr rfl
      intro b _
      exact weight_monomial_mul b.factorization _

@[simp] theorem smoothInterval_one (T : Finset ℕ) (c : ℕ → K) :
    smoothInterval T 1 c = MvPolynomial.C (c 1) := by
  simp [smoothInterval, smoothNumbers, polynomialOf, Finset.filter_singleton]

theorem weight_smoothInterval_one_mul (T : Finset ℕ) (c : ℕ → K) (D : Poly K)
    (hc : c 1 ≠ 0) : weight (smoothInterval T 1 c * D) = weight D := by
  rw [smoothInterval_one]
  exact weight_scalar_monomial_mul 0 hc D

/-- Index-one components give scalar multiples of the multiplier. -/
theorem weight_interval_mul_ge_index_one (T : Finset ℕ) (n : ℕ)
    (c : ℕ → K) (D : Poly K) (hc : NonzeroWeights n c)
    (hT : ∀ p ∈ T, Nat.Prime p) (hD : D.vars ⊆ T) :
    weight D * roughIntervalCount T n ≤ weight (interval n c * D) := by
  classical
  rw [weight_interval_mul_eq_sum_rough_components T n c D hT hD]
  let B := (roughNumbers T n).filter (fun b => n / b = 1)
  calc
    weight D * roughIntervalCount T n = B.card * weight D := by
      rw [Pilz.card_roughNumbers_index_one]
      exact Nat.mul_comm _ _
    _ = ∑ b ∈ B, weight (smoothInterval T (n / b) (fun a => c (b * a)) * D) := by
      symm
      calc
        _ = ∑ _b ∈ B, weight D := by
          apply Finset.sum_congr rfl
          intro b hb
          have hidx : n / b = 1 := (Finset.mem_filter.mp hb).2
          rw [hidx]
          apply weight_smoothInterval_one_mul
          simp only [Nat.mul_one]
          obtain ⟨hbpos, hbn, _⟩ :=
            (mem_roughNumbers T n b).mp (Finset.mem_filter.mp hb).1
          exact hc b (Finset.mem_Icc.mpr ⟨hbpos, hbn⟩)
        _ = B.card * weight D := by simp
    _ ≤ ∑ b ∈ roughNumbers T n,
        weight (smoothInterval T (n / b) (fun a => c (b * a)) * D) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end WeightedPilz
