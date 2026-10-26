import WeightedPilz.BinarySupportGeometry
import WeightedPilz.Arithmetic.BinarySmoothCertificates

/-! The weighted characteristic-two smooth-core bounds 7, 6 and 8. -/

namespace WeightedPilz
variable {K : Type*} [Field K] [CharP K 2]

theorem binarySmooth_support_distance (n : ℕ) (hn : 25 ≤ n) (hn' : n ≤ 66) :
    SupportDistanceBound K (Arithmetic.binarySmoothSupport n) (Arithmetic.binarySmoothBound n) := by
  by_cases h26 : n ≤ 26
  · obtain ⟨ho, hi, hleaf, htop⟩ := Arithmetic.binarySmooth_low_data hn h26
    have hinner : SupportDistanceBound K
        (Arithmetic.rowSupport 3 0 (Arithmetic.binarySmoothSupport n)) 4 :=
      supportDistanceBound_three_rows _ 5 2 2 1 hi
        (supportDistanceBound_two _ hleaf) (supportDistanceBound_one _ hi.top_nonempty)
    simpa only [Arithmetic.binarySmoothBound, if_pos h26] using
      supportDistanceBound_three_rows _ 3 2 4 2 ho hinner
        (supportDistanceBound_two _ htop)
  by_cases h48 : n ≤ 48
  · obtain ⟨ho, hi, hleaf⟩ := Arithmetic.binarySmooth_middle_data (by omega) h48
    have hinner : SupportDistanceBound K
        (Arithmetic.rowSupport 2 0 (Arithmetic.binarySmoothSupport n)) 4 :=
      supportDistanceBound_three_rows _ 5 2 2 1 hi
        (supportDistanceBound_two _ hleaf) (supportDistanceBound_one _ hi.top_nonempty)
    simpa only [Arithmetic.binarySmoothBound, if_neg h26, if_pos h48] using
      supportDistanceBound_three_rows _ 2 (Nat.log2 n) 4 1 ho hinner
        (supportDistanceBound_one _ ho.top_nonempty)
  · obtain ⟨ho, hm, hi, hleaf⟩ := Arithmetic.binarySmooth_high_data (by omega) hn'
    have hinner : SupportDistanceBound K
        (Arithmetic.rowSupport 7 0 (Arithmetic.rowSupport 2 0 (Arithmetic.binarySmoothSupport n))) 4 :=
      supportDistanceBound_three_rows _ 5 2 2 1 hi
        (supportDistanceBound_two _ hleaf) (supportDistanceBound_one _ hi.top_nonempty)
    have hmiddle : SupportDistanceBound K
        (Arithmetic.rowSupport 2 0 (Arithmetic.binarySmoothSupport n)) 6 :=
      supportDistanceBound_three_rows _ 7 2 4 1 hm hinner
        (supportDistanceBound_one _ hm.top_nonempty)
    simpa only [Arithmetic.binarySmoothBound, if_neg h26, if_neg h48] using
      supportDistanceBound_three_rows _ 2 (Nat.log2 n) 6 1 ho hmiddle
        (supportDistanceBound_one _ ho.top_nonempty)

/-- Equation `fin-binary-smooth`, uniformly over arbitrary characteristic-two fields. -/
theorem middle_binary_smooth_distance (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66) :
    Arithmetic.binarySmoothBound n ≤
      distance (smoothInterval (Pilz.primesUpTo (Nat.sqrt n)) n c) :=
  binarySmooth_support_distance n hn hn' _ (smoothInterval_support_eq_binarySmoothSupport n c hc)

/-- The improved five-smooth component used in the quantitative rough-count table. -/
theorem middle_binary_five_smooth_distance (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 27 ≤ n) (hn' : n ≤ 48) :
    6 ≤ distance (smoothInterval (Pilz.primesUpTo 5) n c) := by
  have hslo : 5 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hshi : Nat.sqrt n < 7 := Nat.sqrt_lt.mpr (by omega)
  have hprimes : Pilz.primesUpTo (Nat.sqrt n) = Pilz.primesUpTo 5 := by
    rcases (show Nat.sqrt n = 5 ∨ Nat.sqrt n = 6 by omega) with hs | hs
    · rw [hs]
    · rw [hs]
      decide
  have h := middle_binary_smooth_distance n c hc (by omega) (by omega)
  rw [hprimes] at h
  simpa only [Arithmetic.binarySmoothBound, if_neg (show ¬n ≤ 26 by omega), if_pos hn'] using h

end WeightedPilz
