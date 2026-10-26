import WeightedPilz.InitialAll
import WeightedPilz.MiddleTheorem
import WeightedPilz.LargeTheorem
import WeightedPilz.Convolution
import WeightedPilz.Binary
import WeightedPilz.Laurent

/-! The weighted interval theorem over every field and its equivalent forms. -/

noncomputable section
namespace WeightedPilz
variable {K : Type*} [Field K]

theorem nonzeroWeights_restrict {n m : ℕ} {c : ℕ → K}
    (hc : NonzeroWeights n c) (hm : m ≤ n) : NonzeroWeights m c := by
  intro a ha
  exact hc a (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp ha).2.trans hm⟩)

/-- The frozen field theorem, including the harmless empty-interval case. -/
theorem intervalBound_all (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c) :
    IntervalBound n c := by
  by_cases h24 : n ≤ 24
  · exact intervalBound_initial n c hc h24
  by_cases h66 : n ≤ 66
  · exact intervalBound_middle n c hc (by omega) h66
  · exact intervalBound_large_of_initial n c hc (by omega)
      (fun j hj w hw => intervalBound_initial j w hw (by omega))

/-- Every nonzero polynomial multiplier has at least `n` output monomials. -/
theorem weighted_interval (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (H : Poly K) (hH : H ≠ 0) : n ≤ (interval n c * H).support.card :=
  intervalBound_all n c hc H hH

/-- The same bound for arbitrary Laurent polynomial multipliers. -/
theorem weighted_interval_laurent (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (H : LaurentPoly ℕ K) (hH : H ≠ 0) :
    n ≤ (toLaurent (interval n c) * H).support.card :=
  laurent_bound_of_polynomial_bound (interval n c) n (intervalBound_all n c hc) H hH

theorem weighted_interval_distance (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c) :
    distance (interval n c) = n := by
  apply Nat.le_antisymm
  · simpa only [weight_interval n c hc] using distance_le_weight (interval n c)
  · exact (le_distance_iff _ _).mpr (intervalBound_all n c hc)

theorem weighted_interval_laurent_distance (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) : laurentDistance (toLaurent (interval n c)) = n := by
  rw [laurentDistance_toLaurent, weighted_interval_distance n c hc]

/-- The equivalent finite-support multiplicative-convolution inequality. -/
theorem weighted_convolution (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (f : ArithmeticFunction K) (hf : f ≠ 0) :
    n ≤ (arithmeticKernel n c * f).support.card :=
  convolution_bound_of_intervalBound (intervalBound_all n c hc) f hf

/-- The original symmetric-difference assertion, derived from the weighted theorem. -/
theorem weighted_symmetric_difference (n : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    n ≤ (intervalSymmetricDifference n A).card := by
  apply symmetric_difference_bound_of_intervalBound (n := n) _ A hA hne
  exact intervalBound_all n (fun _ => (1 : ZMod 2)) (fun _ _ => one_ne_zero)

end WeightedPilz
