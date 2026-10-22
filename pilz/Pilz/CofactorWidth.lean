import Pilz.FreshWidth
import Pilz.BaseFactor
import Pilz.SeparatedRows
import Pilz.Endpoints

/-!
# A short multiple has a cofactor of positive base width

This is the cofactor-width step in the proof of `prop:residual`. If the
cofactor has width zero in every base variable, remove its common monomial
factor. The nonconstant core terms then produce disjoint copies of the
remaining cofactor. The constant core term and the fresh terms form one
additional row, whose weight is bounded by endpoint slicing.
-/

noncomputable section

namespace Pilz
namespace FreshData

/-- A base-independent multiplier cannot shorten the fresh-linear polynomial. -/
theorem weight_mul_of_base_independent (S : FreshData) (Q : Poly) (hQ : Q ≠ 0)
    (hIQ : ∀ p ∈ S.base, IndependentOf Q p) :
    weight S.C + S.vars.card ≤ weight (S.F * Q) := by
  classical
  let P : Poly := S.C.erase 0
  let c0 : ZMod 2 := MvPolynomial.coeff 0 S.C
  let V : Poly := MvPolynomial.C c0 + S.freshSum
  have hPsupp : P.support = S.C.support.erase 0 := Finsupp.support_erase
  have hPvars : P.vars ⊆ S.base := by
    intro p hp
    obtain ⟨d, hd, hpd⟩ := (MvPolynomial.mem_vars p).mp hp
    rw [hPsupp] at hd
    exact (MvPolynomial.mem_vars p).mpr ⟨d, (Finset.mem_erase.mp hd).2, hpd⟩
  have hPzero : MvPolynomial.coeff 0 P = 0 := Finsupp.erase_same
  have hCeq : S.C = P + MvPolynomial.C c0 := by
    exact (Finsupp.erase_add_single (0 : ℕ →₀ ℕ)
      (show (ℕ →₀ ℕ) →₀ ZMod 2 from S.C)).symm
  have hF : S.F = P + V := by
    change S.C + S.freshSum = P + (MvPolynomial.C c0 + S.freshSum)
    rw [hCeq]
    ac_rfl
  have hIV : ∀ p ∈ S.base, IndependentOf V p := by
    intro p hp
    apply IndependentOf.add
    · intro d hd
      exact MvPolynomial.mem_support_notMem_vars_zero hd (by simp)
    · intro d hd
      rw [S.support_freshSum] at hd
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
      have hzp : z ≠ p := by
        intro heq
        exact S.not_mem_fresh_of_mem_base hp (heq ▸ hz)
      simp [hzp.symm]
  have hIR : ∀ p ∈ S.base, IndependentOf (V * Q) p :=
    fun p hp => (hIV p hp).mul (hIQ p hp)
  have hdis : Disjoint (P * Q).support (V * Q).support :=
    mul_disjoint_independent_base P Q (V * Q) S.base hPvars hPzero hIQ hIR
  have hweight : weight (S.F * Q) = weight P * weight Q + weight (V * Q) := by
    rw [hF, add_mul, weight_add_of_disjoint _ _ hdis,
      weight_mul_independent_base P Q S.base hPvars hIQ]
  have hpure : ∀ p ∈ S.vars, ∃ k : ℕ, 0 < k ∧
      MvPolynomial.coeff (Finsupp.single p k) V ≠ 0 := by
    intro p hp
    refine ⟨1, by decide, ?_⟩
    have hzero : (0 : ℕ →₀ ℕ) ≠ Finsupp.single p 1 := by
      intro h
      have hh := congrArg (fun d : ℕ →₀ ℕ => d p) h
      simp at hh
    simp [V, MvPolynomial.coeff_add, MvPolynomial.coeff_C, hzero,
      S.coeff_freshSum, hp]
  have hconst : MvPolynomial.coeff 0 V = c0 := by
    have hfresh : MvPolynomial.coeff 0 S.freshSum = 0 := by
      change MvPolynomial.constantCoeff S.freshSum = 0
      simp [freshSum]
    simp only [V, MvPolynomial.coeff_add, MvPolynomial.coeff_zero_C, hfresh, add_zero]
  have hmul : weight P ≤ weight P * weight Q := by
    have hpos : 1 ≤ weight Q := weight_pos hQ
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (weight P) hpos
  by_cases hc0 : c0 = 0
  · have hnot : (0 : ℕ →₀ ℕ) ∉ S.C.support :=
      MvPolynomial.notMem_support_iff.mpr hc0
    have hPeq : P = S.C := Finsupp.erase_of_notMem_support hnot
    have hPweight : weight P = weight S.C := congrArg weight hPeq
    have hbound : S.vars.card ≤ weight (V * Q) :=
      pure_powers_weight_mul S.vars V Q hpure hQ
    omega
  · have hmem : (0 : ℕ →₀ ℕ) ∈ S.C.support :=
      MvPolynomial.mem_support_iff.mpr hc0
    have hPweight : weight P + 1 = weight S.C := by
      change P.support.card + 1 = S.C.support.card
      rw [hPsupp]
      exact Finset.card_erase_add_one hmem
    have hbound : S.vars.card + 1 ≤ weight (V * Q) :=
      pure_endpoints_weight_mul S.vars V Q (by rw [hconst]; exact hc0) hpure hQ
    omega

/-- The cofactor of a short multiple must have positive width in some base
variable, exactly as required by the residual square-root descent. -/
theorem cofactor_positive_width (S : FreshData) (N : ℕ) (H : Poly) (hH : H ≠ 0)
    (hN : N ≤ weight S.C + S.vars.card) (hshort : weight (S.F * H) < N) :
    ∃ p ∈ S.base, 0 < widthOf p H := by
  classical
  by_contra hnone
  have hwidth : ∀ p ∈ S.base, widthOf p H = 0 := by
    intro p hp
    apply Nat.eq_zero_of_not_pos
    exact fun hpos => hnone ⟨p, hp, hpos⟩
  obtain ⟨e, Q, _hfactor, hQ, hIQ, hproducts⟩ :=
    exists_base_independent_factor S.base H hH hwidth
  have hlower := S.weight_mul_of_base_independent Q hQ hIQ
  have hsame := hproducts S.F
  omega

theorem totalWidth_cofactor_pos (S : FreshData) (N : ℕ) (H : Poly) (hH : H ≠ 0)
    (hN : N ≤ weight S.C + S.vars.card) (hshort : weight (S.F * H) < N) :
    0 < totalWidth S.base H := by
  obtain ⟨p, hp, hpos⟩ := S.cofactor_positive_width N H hH hN hshort
  exact hpos.trans_le (Finset.single_le_sum (f := fun q => widthOf q H)
    (fun _ _ => Nat.zero_le _) hp)

end FreshData
end Pilz
