import WeightedPilz.CoefficientRank
import WeightedPilz.ActionConvolution

/-! Vector-valued interval convolution and the coefficient-rank argument. -/
noncomputable section
namespace WeightedPilz
open scoped BigOperators
open Submodule Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def vectorInterval (n : ℕ) (c : ℕ → K) (f : ℕ+ →₀ V) : ℕ+ →₀ V :=
  intervalEndAction n (fun a => scalarWeightEnd (c a)) f

theorem coefficientSpan_vectorInterval_le (n : ℕ) (c : ℕ → K) (f : ℕ+ →₀ V) :
    coefficientSpan (K := K) (vectorInterval n c f) ≤ coefficientSpan (K := K) f := by
  classical
  apply span_le.mpr
  rintro _ ⟨m, rfl⟩
  change intervalEndAction n (fun a => scalarWeightEnd (c a)) f m ∈ _
  rw [intervalScalarAction_apply]
  apply sum_mem
  intro a ha
  split_ifs
  · exact smul_mem _ _ (subset_span ⟨_, rfl⟩)
  · exact zero_mem _

/-- The coefficient spans agree because the first convolution weight is
invertible and every other divisor quotient is strictly smaller. -/
theorem coefficientSpan_vectorInterval (n : ℕ) (c : ℕ → K) (hn : 0 < n)
    (hc : c 1 ≠ 0) (f : ℕ+ →₀ V) :
    coefficientSpan (K := K) (vectorInterval n c f) = coefficientSpan (K := K) f := by
  classical
  apply le_antisymm (coefficientSpan_vectorInterval_le n c f)
  apply span_le.mpr
  rintro _ ⟨m, rfl⟩
  induction m using WellFoundedLT.induction with
  | ind m ih =>
    let g := vectorInterval n c f
    let t : ℕ → V := fun a => if intervalIndex a ∣ m then
      c (a + 1) • f (PNat.divExact m (intervalIndex a)) else 0
    have hformula : g m = ∑ a ∈ Finset.range n, t a :=
      intervalScalarAction_apply n c f m
    have hzero : 0 ∈ Finset.range n := Finset.mem_range.mpr hn
    rw [← Finset.add_sum_erase _ _ hzero] at hformula
    have hidx : intervalIndex 0 = 1 := rfl
    have hdiv : PNat.divExact m 1 = m := by
      simpa using (PNat.mul_div_exact (one_dvd m))
    have hfirst : t 0 = c 1 • f m := by simp [t, hidx, hdiv]
    rw [hfirst] at hformula
    have htail : (∑ a ∈ (Finset.range n).erase 0, t a) ∈ coefficientSpan (K := K) g := by
      apply sum_mem
      intro a ha
      by_cases hd : intervalIndex a ∣ m
      · have hapos : 1 < a + 1 := by
          have := (Finset.mem_erase.mp ha).1
          omega
        have hprod := congrArg (fun x : ℕ+ => (x : ℕ)) (PNat.mul_div_exact hd)
        change (a + 1) * (PNat.divExact m (intervalIndex a) : ℕ) = (m : ℕ) at hprod
        have hlt : PNat.divExact m (intervalIndex a) < m := by
          change (PNat.divExact m (intervalIndex a) : ℕ) < (m : ℕ)
          have hmul := Nat.mul_lt_mul_of_pos_right hapos (PNat.divExact m (intervalIndex a)).pos
          simpa only [one_mul, hprod] using hmul
        simpa only [t, if_pos hd] using smul_mem (coefficientSpan (K := K) g)
          (c (a + 1)) (ih _ hlt)
      · simp only [t, if_neg hd]
        exact zero_mem _
    have hgm : g m ∈ coefficientSpan (K := K) g := subset_span ⟨m, rfl⟩
    have hcf : c 1 • f m ∈ coefficientSpan (K := K) g := by
      rw [hformula] at hgm
      simpa only [add_sub_cancel_right] using sub_mem hgm htail
    have h := smul_mem (coefficientSpan (K := K) g) ((c 1)⁻¹) hcf
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h

theorem vectorInterval_ne_zero (n : ℕ) (c : ℕ → K) (hn : 0 < n)
    (hc : c 1 ≠ 0) (f : ℕ+ →₀ V) (hf : f ≠ 0) : vectorInterval n c f ≠ 0 := by
  intro hz
  have hspan := coefficientSpan_vectorInterval n c hn hc f
  rw [hz] at hspan
  have hbot : coefficientSpan (K := K) f = ⊥ := by
    rw [← hspan]
    simp [coefficientSpan]
  apply hf
  ext m
  have h : f m ∈ coefficientSpan (K := K) f := subset_span ⟨m, rfl⟩
  simpa [hbot] using h

/-- Rank enhancement of the scalar interval theorem. The scalar field theorem
is an explicit dependency until the full interval proof has been assembled. -/
theorem vectorInterval_rank_bound_of_intervalBound (n : ℕ) (c : ℕ → K)
    (hn : 0 < n) (hc : NonzeroWeights n c) (hfield : IntervalBound n c)
    (f : ℕ+ →₀ V) (hf : f ≠ 0) :
    n + finrank K (coefficientSpan (K := K) f) ≤ (vectorInterval n c f).support.card + 1 := by
  have hc1 : c 1 ≠ 0 := hc 1 (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
  have hg := vectorInterval_ne_zero n c hn hc1 f hf
  rw [← coefficientSpan_vectorInterval n c hn hc1 f]
  apply coefficientRank_projection_bound _ hg
  intro φ hφ
  let fφ : ArithmeticFunction K := Finsupp.mapRange φ φ.map_zero f
  let gφ : ArithmeticFunction K := Finsupp.mapRange φ φ.map_zero (vectorInterval n c f)
  have hnat : gφ = arithmeticKernel n c * fφ := by
    have h := intervalEndAction_naturality n
      (fun a => scalarWeightEnd (M := V) (c a))
      (fun a => scalarWeightEnd (M := K) (c a)) φ.toAddMonoidHom
      (fun a ha x => φ.map_smul (c (a + 1)) x) f
    simpa only [gφ, fφ, vectorInterval, intervalEndAction_scalar_eq_convolution] using h
  have hinput : fφ ≠ 0 := by
    intro hz
    apply hφ
    change gφ = 0
    rw [hnat, hz, mul_zero]
  change n ≤ gφ.support.card
  rw [hnat]
  exact convolution_bound_of_intervalBound hfield _ hinput

end WeightedPilz
