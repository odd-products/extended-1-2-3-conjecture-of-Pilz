import Pilz.NormalForm
import Pilz.Endpoints
import Pilz.Slices

/-!
# The core cannot vanish cheaply

The specialization of the paper's core lemma to fresh coefficients `Pᵢ = 1`,
which is the form used for the interval polynomials. We slice at a monomial
of least total fresh degree in the two auxiliary polynomials.
-/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

theorem outsideSlice_add (B : Finset ℕ) (β : ℕ →₀ ℕ) (P Q : Poly) :
    outsideSlice B β (P + Q) = outsideSlice B β P + outsideSlice B β Q := by
  classical
  ext d
  by_cases h : outsideExponent B d = β <;>
    simp [coeff_outsideSlice, h]

namespace FreshData

/-- Total degree in the fresh variables, including multiplicities. -/
def freshDegree (S : FreshData) (d : ℕ →₀ ℕ) : ℕ := ∑ z ∈ S.vars, d z

theorem freshDegree_add (S : FreshData) (d e : ℕ →₀ ℕ) :
    S.freshDegree (d + e) = S.freshDegree d + S.freshDegree e := by
  simp [freshDegree, Finsupp.add_apply, Finset.sum_add_distrib]

theorem freshDegree_outsideExponent (S : FreshData) (d : ℕ →₀ ℕ) :
    S.freshDegree (outsideExponent S.base d) = S.freshDegree d := by
  classical
  apply Finset.sum_congr rfl
  intro z hz
  have hzb : z ∉ S.base := fun hm => S.not_mem_fresh_of_mem_base hm hz
  simp [outsideExponent_apply, hzb]

theorem freshDegree_freshSum_square (S : FreshData) {d : ℕ →₀ ℕ}
    (hd : d ∈ (S.freshSum ^ 2).support) : S.freshDegree d = 2 := by
  classical
  rw [support_square, S.support_freshSum] at hd
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
  simp [freshDegree, doubleExponent, two_smul, Finsupp.add_apply,
    Finset.sum_add_distrib, Finsupp.single_apply, hz]

/-- The lowest fresh-degree part of `CD + F²E` contributes a nonzero
multiple of `C` whenever `D` has fewer than `distance C` terms. -/
theorem core_weight_lower (S : FreshData) (D E : Poly) (hD : D ≠ 0)
    (hsmall : weight D < distance S.C) :
    distance S.C ≤ weight (S.C * D + (S.C ^ 2 + S.freshSum ^ 2) * E) := by
  classical
  obtain ⟨d, hd, hmin⟩ := (D.support ∪ E.support).exists_min_image
    S.freshDegree (Finset.Nonempty.mono Finset.subset_union_left
      (MvPolynomial.support_nonempty.mpr hD))
  let β := outsideExponent S.base d
  let Dβ := outsideSlice S.base β D
  let Eβ := outsideSlice S.base β E
  have hsome : Dβ ≠ 0 ∨ Eβ ≠ 0 := by
    rcases Finset.mem_union.mp hd with hdD | hdE
    · left
      apply MvPolynomial.support_nonempty.mp
      exact ⟨d, by rw [support_outsideSlice]; exact Finset.mem_filter.mpr ⟨hdD, rfl⟩⟩
    · right
      apply MvPolynomial.support_nonempty.mp
      exact ⟨d, by rw [support_outsideSlice]; exact Finset.mem_filter.mpr ⟨hdE, rfl⟩⟩
  have hhigh : outsideSlice S.base β (S.freshSum ^ 2 * E) = 0 := by
    apply MvPolynomial.support_eq_empty.mp
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    rw [support_outsideSlice] at ha
    obtain ⟨ha, hβ⟩ := Finset.mem_filter.mp ha
    obtain ⟨b, hb, c, hc, hbc⟩ :=
      Finset.mem_add.mp (MvPolynomial.support_mul (S.freshSum ^ 2) E ha)
    have hdeg : S.freshDegree a = S.freshDegree d := by
      calc
        S.freshDegree a = S.freshDegree (outsideExponent S.base a) :=
          (S.freshDegree_outsideExponent a).symm
        _ = S.freshDegree d := by rw [hβ]; exact S.freshDegree_outsideExponent d
    have hle := hmin c (Finset.mem_union_right D.support hc)
    have hbdeg := S.freshDegree_freshSum_square hb
    rw [← hbc, S.freshDegree_add, hbdeg] at hdeg
    omega
  have hlow : Dβ + S.C * Eβ ≠ 0 := by
    intro hz
    have heq : Dβ = S.C * Eβ := by
      have hh := congrArg (fun P : Poly => P + S.C * Eβ) hz
      simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using hh
    by_cases hEβ : Eβ = 0
    · rcases hsome with hDβ | hEβ'
      · exact hDβ (by simpa only [hEβ, mul_zero] using heq)
      · exact hEβ' hEβ
    · have hb : distance S.C ≤ weight Dβ := by
        rw [heq]
        exact distance_le_weight_mul S.C Eβ hEβ
      exact (not_lt_of_ge (hb.trans (weight_outsideSlice_le S.base β D))) hsmall
  have hslice :
      outsideSlice S.base β (S.C * D + (S.C ^ 2 + S.freshSum ^ 2) * E) =
        S.C * (Dβ + S.C * Eβ) := by
    rw [add_mul, outsideSlice_add, outsideSlice_add, hhigh, add_zero,
      outsideSlice_mul S.base β S.C D (by rfl)]
    have hC2 : (S.C ^ 2).vars ⊆ S.base := by
      exact (MvPolynomial.vars_pow S.C 2).trans (by rfl)
    rw [outsideSlice_mul S.base β (S.C ^ 2) E hC2]
    dsimp only [Dβ, Eβ]
    ring
  have hb := distance_le_weight_mul S.C (Dβ + S.C * Eβ) hlow
  change distance S.C ≤ weight (S.C * (Dβ + S.C * Eβ)) at hb
  rw [← hslice] at hb
  exact hb.trans (weight_outsideSlice_le S.base β _)

end FreshData

/-- Paper, Lemma `lem:core`, the interval-polynomial normal-form conclusion. -/
theorem normalForm_core_budget (S : FreshData) (N : ℕ) (nf : NormalFormData S N)
    (hsmall : weight nf.D < distance S.C) :
    S.vars.card * weight nf.D + distance S.C ≤ weight nf.G := by
  obtain ⟨E, hE⟩ := S.square_dvd_residual nf.extremal.1.2.1 nf.common
  have hG₀ : nf.G₀ = S.C * nf.D + (S.C ^ 2 + S.freshSum ^ 2) * E := by
    have hres : nf.G₀ + S.C * nf.D = S.F ^ 2 * E := by
      calc
        nf.G₀ + S.C * nf.D = nf.G + S.F * nf.D := by
          rw [nf.eq_form, FreshData.F, add_mul]
          calc
            nf.G₀ + S.C * nf.D = (nf.G₀ + S.C * nf.D) +
                (S.freshSum * nf.D + S.freshSum * nf.D) := by
              rw [CharTwo.add_self_eq_zero, add_zero]
            _ = nf.G₀ + S.freshSum * nf.D + (S.C * nf.D + S.freshSum * nf.D) := by
              ac_rfl
        _ = S.F ^ 2 * E := hE
    have hh := congrArg (fun P : Poly => P + S.C * nf.D) hres
    calc
      nf.G₀ = (S.C ^ 2 + S.freshSum ^ 2) * E + S.C * nf.D := by
        simpa only [FreshData.F, CharTwo.add_sq, add_assoc,
          CharTwo.add_self_eq_zero, add_zero] using hh
      _ = S.C * nf.D + (S.C ^ 2 + S.freshSum ^ 2) * E := add_comm _ _
  have hb := S.core_weight_lower nf.D E nf.D_ne_zero hsmall
  rw [← hG₀] at hb
  have hw := normalForm_weight S N nf
  omega

end Pilz
