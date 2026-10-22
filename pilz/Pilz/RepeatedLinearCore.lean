import Pilz.LinearCoreBounds
import Pilz.SmallCoreBounds
import Pilz.Fresh

/-! Repeated endpoint slicing and the numerical core bounds in the paper's
finite interval tables. -/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

/-- Successively slice every fresh linear coordinate. All coefficients avoid
all the slicing coordinates; the constant term witnesses that the bottom
coefficient stays nonzero at every step. -/
theorem repeated_linear_core_distance (T : Finset ℕ) (C : Poly) (A : ℕ → Poly)
    (hC : constantCoeff C ≠ 0)
    (hA : ∀ p ∈ T, A p ≠ 0)
    (hCdeg : ∀ p ∈ T, C.degreeOf p = 0)
    (hAdeg : ∀ p ∈ T, ∀ q ∈ T, (A p).degreeOf q = 0) :
    distance C + ∑ p ∈ T, distance (A p) ≤
      distance (C + ∑ p ∈ T, A p * X p) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T hp ih =>
      have hAT : ∀ q ∈ T, A q ≠ 0 := fun q hq => hA q (Finset.mem_insert_of_mem hq)
      have hCT : ∀ q ∈ T, C.degreeOf q = 0 :=
        fun q hq => hCdeg q (Finset.mem_insert_of_mem hq)
      have hATdeg : ∀ q ∈ T, ∀ r ∈ T, (A q).degreeOf r = 0 :=
        fun q hq r hr => hAdeg q (Finset.mem_insert_of_mem hq) r (Finset.mem_insert_of_mem hr)
      have hprev := ih hAT hCT hATdeg
      let B := C + ∑ q ∈ T, A q * X q
      have hB : B ≠ 0 := by
        intro hz
        apply hC
        have hh := congrArg constantCoeff hz
        simpa [B, map_add, map_sum, map_mul] using hh
      have hBdeg : B.degreeOf p = 0 := by
        apply Nat.eq_zero_of_le_zero
        refine (degreeOf_add_le p C (∑ q ∈ T, A q * X q)).trans ?_
        rw [hCdeg p (Finset.mem_insert_self _ _), Nat.zero_max]
        refine (degreeOf_sum_le p T (fun q => A q * X q)).trans ?_
        rw [Finset.sup_le_iff]
        intro q hq
        have hqp : q ≠ p := by intro heq; exact hp (heq ▸ hq)
        refine (degreeOf_mul_le p (A q) (X q)).trans_eq ?_
        rw [hAdeg q (Finset.mem_insert_of_mem hq) p (Finset.mem_insert_self _ _)]
        simp [degreeOf_X, Ne.symm hqp]
      have hlin := linear_core_distance p B (A p) hB
        (hA p (Finset.mem_insert_self _ _)) hBdeg
        (hAdeg p (Finset.mem_insert_self _ _) p (Finset.mem_insert_self _ _))
      have heq : C + ∑ q ∈ insert p T, A q * X q = B + A p * X p := by
        rw [Finset.sum_insert hp]
        dsimp [B]
        ring
      rw [heq, Finset.sum_insert hp]
      dsimp [B] at hlin ⊢
      omega

end Pilz


