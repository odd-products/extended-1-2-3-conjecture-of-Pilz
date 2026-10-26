import WeightedPilz.FreshRows
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-! Exact expanded weights through aggregate fresh degree two. -/

noncomputable section
namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [DecidableEq σ] [Field K]

private def ZeroAt (z : σ) (P : MvPolynomial σ K) : Prop :=
  ∀ d ∈ P.support, d z = 0

private theorem zeroAt_add {z : σ} {A B : MvPolynomial σ K}
    (hA : ZeroAt z A) (hB : ZeroAt z B) : ZeroAt z (A + B) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
  · exact hA d hd
  · exact hB d hd

private theorem zeroAt_mul {z : σ} {A B : MvPolynomial σ K}
    (hA : ZeroAt z A) (hB : ZeroAt z B) : ZeroAt z (A * B) := by
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul A B hd)
  simp [Finsupp.add_apply, hA a ha, hB b hb]

private theorem zeroAt_C (z : σ) (a : K) : ZeroAt z (C a) := by
  intro d hd
  exact MvPolynomial.mem_support_notMem_vars_zero hd (by simp)

private theorem zeroAt_sum_variables (z : σ) (V : Finset σ) (hz : z ∉ V) :
    ZeroAt z (∑ i ∈ V, (X i : MvPolynomial σ K)) := by
  classical
  intro d hd
  obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  rw [support_X] at hdi
  obtain rfl := Finset.mem_singleton.mp hdi
  have hiz : i ≠ z := by intro h; subst i; exact hz hi
  simp [hiz]

private theorem coordinate_Xpow_mul (z : σ) (k : ℕ) (P : MvPolynomial σ K)
    (hP : ZeroAt z P) {d : σ →₀ ℕ} (hd : d ∈ (X z ^ k * P).support) :
    d z = k := by
  classical
  rw [X_pow_eq_monomial] at hd
  have hs : (monomial (Finsupp.single z k) 1 * P).support =
      P.support.map (addLeftEmbedding (Finsupp.single z k)) :=
    AddMonoidAlgebra.support_single_mul P 1 (by simp) _
  rw [hs] at hd
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hd
  change (Finsupp.single z k + e) z = k
  simp [Finsupp.add_apply, hP e he]

private theorem disjoint_coordinate_rows (z : σ) (a b : ℕ)
    (A B : MvPolynomial σ K) (hA : ∀d∈A.support, d z = a)
    (hB : ∀d∈B.support, d z = b) (hab : a ≠ b) : Disjoint A.support B.support := by
  apply Finset.disjoint_left.mpr
  intro d hdA hdB
  exact hab ((hA d hdA).symm.trans (hB d hdB))

private theorem weight_two_coordinate_rows (z : σ) (A B : MvPolynomial σ K)
    (hA : ZeroAt z A) (hB : ZeroAt z B) :
    weight (A + X z * B) = weight A + weight B := by
  have hrow : ∀d∈(X z * B).support, d z = 1 := by
    intro d hd
    exact coordinate_Xpow_mul z 1 B hB (by simpa only [pow_one] using hd)
  rw [weight_add_of_disjoint A (X z * B)
    (disjoint_coordinate_rows z 0 1 A _ hA hrow (by decide))]
  simp [MvPolynomial.X]

private theorem weight_three_coordinate_rows (z : σ) (A B D : MvPolynomial σ K)
    (hA : ZeroAt z A) (hB : ZeroAt z B) (hD : ZeroAt z D) :
    weight (A + X z * B + X z ^ 2 * D) = weight A + weight B + weight D := by
  have hrow1 : ∀d∈(X z * B).support, d z = 1 := by
    intro d hd
    exact coordinate_Xpow_mul z 1 B hB (by simpa only [pow_one] using hd)
  have hrow2 : ∀d∈(X z ^ 2 * D).support, d z = 2 := by
    intro d hd
    exact coordinate_Xpow_mul z 2 D hD hd
  have hdis : Disjoint (A + X z * B).support (X z ^ 2 * D).support := by
    apply Finset.disjoint_left.mpr
    intro d hd hdd
    have hd2 := hrow2 d hdd
    rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
    · have hd0 := hA d hd
      omega
    · have hd1 := hrow1 d hd
      omega
  rw [weight_add_of_disjoint _ _ hdis, weight_two_coordinate_rows z A B hA hB]
  simp [X_pow_eq_monomial]

/-- Exact linear expansion in a finite set of independent variables. -/
theorem weight_linear_fresh_rows (V : Finset σ) (A B : MvPolynomial σ K)
    (hA : ∀ z ∈ V, ∀ d ∈ A.support, d z = 0)
    (hB : ∀ z ∈ V, ∀ d ∈ B.support, d z = 0) :
    weight (A + (∑ i ∈ V, X i) * B) = weight A + V.card * weight B := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | @insert z V hz ih =>
    have hAz : ZeroAt z A := hA z (Finset.mem_insert_self _ _)
    have hBz : ZeroAt z B := hB z (Finset.mem_insert_self _ _)
    have hAV := fun i hi => hA i (Finset.mem_insert_of_mem hi)
    have hBV := fun i hi => hB i (Finset.mem_insert_of_mem hi)
    have hZ := zeroAt_sum_variables (K := K) z V hz
    rw [Finset.sum_insert hz]
    have heq : A + (X z + ∑ i ∈ V, X i) * B =
        (A + (∑ i ∈ V, X i) * B) + X z * B := by ring
    rw [heq, weight_two_coordinate_rows z _ B (zeroAt_add hAz (zeroAt_mul hZ hBz)) hBz,
      ih hAV hBV, Finset.card_insert_of_notMem hz]
    ring

/-- The row coefficients `1, r, binomial(r+1,2)` in every characteristic other than two. -/
theorem weight_quadratic_fresh_rows (V : Finset σ) (A B D : MvPolynomial σ K)
    (hA : ∀ z ∈ V, ∀ d ∈ A.support, d z = 0)
    (hB : ∀ z ∈ V, ∀ d ∈ B.support, d z = 0)
    (hD : ∀ z ∈ V, ∀ d ∈ D.support, d z = 0) (h2 : (2 : K) ≠ 0) :
    weight (A + (∑ i ∈ V, X i) * B + (∑ i ∈ V, X i)^2 * D) =
      weight A + V.card * weight B + Nat.choose (V.card + 1) 2 * weight D := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | @insert z V hz ih =>
    have hAz : ZeroAt z A := hA z (Finset.mem_insert_self _ _)
    have hBz : ZeroAt z B := hB z (Finset.mem_insert_self _ _)
    have hDz : ZeroAt z D := hD z (Finset.mem_insert_self _ _)
    have hAV := fun i hi => hA i (Finset.mem_insert_of_mem hi)
    have hBV := fun i hi => hB i (Finset.mem_insert_of_mem hi)
    have hDV := fun i hi => hD i (Finset.mem_insert_of_mem hi)
    let Z : MvPolynomial σ K := ∑ i ∈ V, X i
    have hZ : ZeroAt z Z := zeroAt_sum_variables z V hz
    have h2Dz : ZeroAt z (C 2 * D) := zeroAt_mul (zeroAt_C z 2) hDz
    have h2DV : ∀i∈V, ∀d∈(C 2 * D).support, d i = 0 := by
      intro i hi
      exact zeroAt_mul (zeroAt_C i 2) (hDV i hi)
    have h2weight : weight (C 2 * D) = weight D := weight_scalar_monomial_mul 0 h2 D
    have hlin := weight_linear_fresh_rows V B (C 2 * D) hBV h2DV
    rw [h2weight] at hlin
    rw [Finset.sum_insert hz]
    change weight (A + (X z + Z) * B + (X z + Z)^2 * D) = _
    have heq : A + (X z + Z) * B + (X z + Z)^2 * D =
        (A + Z * B + Z^2 * D) + X z * (B + Z * (C 2 * D)) + X z^2 * D := by
      simp only [map_ofNat]
      ring
    have hrow0 : ZeroAt z (A + Z * B + Z^2 * D) :=
      zeroAt_add (zeroAt_add hAz (zeroAt_mul hZ hBz))
        (zeroAt_mul (by simpa only [pow_two] using zeroAt_mul hZ hZ) hDz)
    have hrow1 : ZeroAt z (B + Z * (C 2 * D)) := zeroAt_add hBz (zeroAt_mul hZ h2Dz)
    rw [heq, weight_three_coordinate_rows z _ _ D hrow0 hrow1 hDz]
    change weight (A + (∑ i ∈ V, X i) * B + (∑ i ∈ V, X i)^2 * D) +
      weight (B + (∑ i ∈ V, X i) * (C 2 * D)) + weight D = _
    rw [ih hAV hBV hDV, hlin, Finset.card_insert_of_notMem hz]
    have hchoose : Nat.choose (V.card + 1 + 1) 2 = Nat.choose (V.card + 1) 2 + (V.card + 1) := by
      rw [Nat.choose_succ_succ]
      simp [Nat.add_comm]
    rw [hchoose]
    ring

namespace FreshData

/-- Equation `eq:large-affine`, as an exact identity before any lower bound. -/
theorem weight_mul_affine (S : FreshData σ K) (D B : MvPolynomial σ K)
    (hD : S.BaseOnly D) (hB : S.BaseOnly B) (h2 : (2 : K) ≠ 0) :
    weight (S.F * (D + S.freshSum * B)) =
      weight (S.C * D) + S.vars.card * weight (D + S.C * B) +
        (S.vars.card * (S.vars.card + 1) / 2) * weight B := by
  have hCD := BaseOnly.mul S.independent hD
  have hCB := BaseOnly.mul S.independent hB
  have hmiddle : S.BaseOnly (D + S.C * B) := by
    intro z hz
    exact zeroAt_add (hD z hz) (hCB z hz)
  have h := weight_quadratic_fresh_rows S.vars (S.C * D) (D + S.C * B) B
    hCD hmiddle hB h2
  have heq : S.F * (D + S.freshSum * B) =
      S.C * D + S.freshSum * (D + S.C * B) + S.freshSum^2 * B := by
    rw [F]
    ring
  rw [heq]
  convert h using 1
  simp [Nat.choose_two_right, Nat.mul_comm]

end FreshData
end WeightedPilz
