import WeightedPilz.Arithmetic.UniqueProducts
import Lean.Elab.Tactic.Omega

/-! Exact anchored two-missing-products certificates for the two exceptional
cube-residue cores. Literal sets are proved equal to the mathematical sets. -/

namespace WeightedPilz.Arithmetic

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def missingWitnesses (n u a : ℕ) : ℕ × ℕ :=
  if ¬ a ∣ u then (1, if ¬ a ∣ 2 * u then 2 else 3)
  else if u / a = 1 then (4, 6)
  else if u / a = 2 then (2, 3)
  else if u / a ≤ n / 2 then (2, 4)
  else if u / a ≤ n then (1, 2)
  else (n, n - 1)

private def MissingWitnessProperty (C U : Finset ℕ) (n u a : ℕ) : Prop :=
  let w := missingWitnesses n u a
  w.1 ∈ C ∧ w.2 ∈ C ∧ w.1 ≠ w.2 ∧
    (∀ v ∈ U, u * w.1 ≠ v * a) ∧ (∀ v ∈ U, u * w.2 ≠ v * a)

private instance (C U : Finset ℕ) (n u a : ℕ) :
    Decidable (MissingWitnessProperty C U n u a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

private def missingCore27 : Finset ℕ :=
  ⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27] : List ℕ), by decide⟩

private def missingUnique27 : Finset ℕ :=
  ⟨([1, 2, 3, 5, 7, 11, 13, 33, 35, 39, 49, 55, 65, 77, 91, 98, 99, 117, 121, 125, 128, 143, 147, 165, 169, 175, 195, 196, 224, 231, 242, 243, 250, 256, 273, 275, 280, 294, 297, 308, 315, 320, 325, 330, 338, 350, 351, 352, 364, 375, 384, 390, 396, 405, 416, 420, 440, 441, 450, 462, 468, 480, 484, 486, 500, 504, 520, 525, 528, 540, 546, 550, 567, 572, 576, 594, 600, 624, 625, 648, 650, 675, 676, 702, 729] : List ℕ), by decide⟩

private theorem missingCore27_eq : core 27 = missingCore27 := by decide +kernel

private theorem missingUnique27_divisors :
    ∀ u ∈ missingUnique27,
      (missingCore27.filter (fun a =>
        a ≤ u / a ∧ u % a = 0 ∧ u / a ∈ missingCore27)).card = 1 := by
  decide +kernel

private theorem missingUnique27_eq : uniqueProducts 27 = missingUnique27 := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    have hc : (representations 27 u).card = 1 := by
      rw [representations_card_eq]
      simpa only [representationDivisors, missingCore27_eq] using
        missingUnique27_divisors u hu
    refine Finset.mem_filter.mpr ⟨?_, hc⟩
    exact representations_nonempty_iff.mp
      (Finset.card_pos.mp (by omega : 0 < (representations 27 u).card))
  · rw [uniqueProducts_card_27]
    decide +kernel

private theorem missingCheck_27_1 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 1 a := by
  decide +kernel

private theorem missingCheck_27_2 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 2 a := by
  decide +kernel

private theorem missingCheck_27_3 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 3 a := by
  decide +kernel

private theorem missingCheck_27_5 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 5 a := by
  decide +kernel

private theorem missingCheck_27_7 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 7 a := by
  decide +kernel

private theorem missingCheck_27_11 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 11 a := by
  decide +kernel

private theorem missingCheck_27_13 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 13 a := by
  decide +kernel

private theorem missingCheck_27_33 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 33 a := by
  decide +kernel

private theorem missingCheck_27_35 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 35 a := by
  decide +kernel

private theorem missingCheck_27_39 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 39 a := by
  decide +kernel

private theorem missingCheck_27_49 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 49 a := by
  decide +kernel

private theorem missingCheck_27_55 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 55 a := by
  decide +kernel

private theorem missingCheck_27_65 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 65 a := by
  decide +kernel

private theorem missingCheck_27_77 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 77 a := by
  decide +kernel

private theorem missingCheck_27_91 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 91 a := by
  decide +kernel

private theorem missingCheck_27_98 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 98 a := by
  decide +kernel

private theorem missingCheck_27_99 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 99 a := by
  decide +kernel

private theorem missingCheck_27_117 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 117 a := by
  decide +kernel

private theorem missingCheck_27_121 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 121 a := by
  decide +kernel

private theorem missingCheck_27_125 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 125 a := by
  decide +kernel

private theorem missingCheck_27_128 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 128 a := by
  decide +kernel

private theorem missingCheck_27_143 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 143 a := by
  decide +kernel

private theorem missingCheck_27_147 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 147 a := by
  decide +kernel

private theorem missingCheck_27_165 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 165 a := by
  decide +kernel

private theorem missingCheck_27_169 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 169 a := by
  decide +kernel

private theorem missingCheck_27_175 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 175 a := by
  decide +kernel

private theorem missingCheck_27_195 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 195 a := by
  decide +kernel

private theorem missingCheck_27_196 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 196 a := by
  decide +kernel

private theorem missingCheck_27_224 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 224 a := by
  decide +kernel

private theorem missingCheck_27_231 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 231 a := by
  decide +kernel

private theorem missingCheck_27_242 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 242 a := by
  decide +kernel

private theorem missingCheck_27_243 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 243 a := by
  decide +kernel

private theorem missingCheck_27_250 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 250 a := by
  decide +kernel

private theorem missingCheck_27_256 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 256 a := by
  decide +kernel

private theorem missingCheck_27_273 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 273 a := by
  decide +kernel

private theorem missingCheck_27_275 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 275 a := by
  decide +kernel

private theorem missingCheck_27_280 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 280 a := by
  decide +kernel

private theorem missingCheck_27_294 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 294 a := by
  decide +kernel

private theorem missingCheck_27_297 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 297 a := by
  decide +kernel

private theorem missingCheck_27_308 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 308 a := by
  decide +kernel

private theorem missingCheck_27_315 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 315 a := by
  decide +kernel

private theorem missingCheck_27_320 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 320 a := by
  decide +kernel

private theorem missingCheck_27_325 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 325 a := by
  decide +kernel

private theorem missingCheck_27_330 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 330 a := by
  decide +kernel

private theorem missingCheck_27_338 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 338 a := by
  decide +kernel

private theorem missingCheck_27_350 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 350 a := by
  decide +kernel

private theorem missingCheck_27_351 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 351 a := by
  decide +kernel

private theorem missingCheck_27_352 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 352 a := by
  decide +kernel

private theorem missingCheck_27_364 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 364 a := by
  decide +kernel

private theorem missingCheck_27_375 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 375 a := by
  decide +kernel

private theorem missingCheck_27_384 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 384 a := by
  decide +kernel

private theorem missingCheck_27_390 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 390 a := by
  decide +kernel

private theorem missingCheck_27_396 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 396 a := by
  decide +kernel

private theorem missingCheck_27_405 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 405 a := by
  decide +kernel

private theorem missingCheck_27_416 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 416 a := by
  decide +kernel

private theorem missingCheck_27_420 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 420 a := by
  decide +kernel

private theorem missingCheck_27_440 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 440 a := by
  decide +kernel

private theorem missingCheck_27_441 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 441 a := by
  decide +kernel

private theorem missingCheck_27_450 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 450 a := by
  decide +kernel

private theorem missingCheck_27_462 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 462 a := by
  decide +kernel

private theorem missingCheck_27_468 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 468 a := by
  decide +kernel

private theorem missingCheck_27_480 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 480 a := by
  decide +kernel

private theorem missingCheck_27_484 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 484 a := by
  decide +kernel

private theorem missingCheck_27_486 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 486 a := by
  decide +kernel

private theorem missingCheck_27_500 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 500 a := by
  decide +kernel

private theorem missingCheck_27_504 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 504 a := by
  decide +kernel

private theorem missingCheck_27_520 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 520 a := by
  decide +kernel

private theorem missingCheck_27_525 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 525 a := by
  decide +kernel

private theorem missingCheck_27_528 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 528 a := by
  decide +kernel

private theorem missingCheck_27_540 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 540 a := by
  decide +kernel

private theorem missingCheck_27_546 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 546 a := by
  decide +kernel

private theorem missingCheck_27_550 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 550 a := by
  decide +kernel

private theorem missingCheck_27_567 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 567 a := by
  decide +kernel

private theorem missingCheck_27_572 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 572 a := by
  decide +kernel

private theorem missingCheck_27_576 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 576 a := by
  decide +kernel

private theorem missingCheck_27_594 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 594 a := by
  decide +kernel

private theorem missingCheck_27_600 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 600 a := by
  decide +kernel

private theorem missingCheck_27_624 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 624 a := by
  decide +kernel

private theorem missingCheck_27_625 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 625 a := by
  decide +kernel

private theorem missingCheck_27_648 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 648 a := by
  decide +kernel

private theorem missingCheck_27_650 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 650 a := by
  decide +kernel

private theorem missingCheck_27_675 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 675 a := by
  decide +kernel

private theorem missingCheck_27_676 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 676 a := by
  decide +kernel

private theorem missingCheck_27_702 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 702 a := by
  decide +kernel

private theorem missingCheck_27_729 :
    ∀ a ∈ missingCore27, MissingWitnessProperty missingCore27 missingUnique27 27 729 a := by
  decide +kernel

private theorem missingChecks27 :
    ∀ u ∈ missingUnique27, ∀ a ∈ missingCore27,
      MissingWitnessProperty missingCore27 missingUnique27 27 u a := by
  change ∀ u ∈ ([1, 2, 3, 5, 7, 11, 13, 33, 35, 39, 49, 55, 65, 77, 91, 98, 99, 117, 121, 125, 128, 143, 147, 165, 169, 175, 195, 196, 224, 231, 242, 243, 250, 256, 273, 275, 280, 294, 297, 308, 315, 320, 325, 330, 338, 350, 351, 352, 364, 375, 384, 390, 396, 405, 416, 420, 440, 441, 450, 462, 468, 480, 484, 486, 500, 504, 520, 525, 528, 540, 546, 550, 567, 572, 576, 594, 600, 624, 625, 648, 650, 675, 676, 702, 729] : List ℕ), ∀ a ∈ missingCore27,
    MissingWitnessProperty missingCore27 missingUnique27 27 u a
  simp only [List.forall_mem_cons, List.forall_mem_nil]
  exact ⟨missingCheck_27_1, missingCheck_27_2, missingCheck_27_3, missingCheck_27_5, missingCheck_27_7, missingCheck_27_11, missingCheck_27_13, missingCheck_27_33, missingCheck_27_35, missingCheck_27_39, missingCheck_27_49, missingCheck_27_55, missingCheck_27_65, missingCheck_27_77, missingCheck_27_91, missingCheck_27_98, missingCheck_27_99, missingCheck_27_117, missingCheck_27_121, missingCheck_27_125, missingCheck_27_128, missingCheck_27_143, missingCheck_27_147, missingCheck_27_165, missingCheck_27_169, missingCheck_27_175, missingCheck_27_195, missingCheck_27_196, missingCheck_27_224, missingCheck_27_231, missingCheck_27_242, missingCheck_27_243, missingCheck_27_250, missingCheck_27_256, missingCheck_27_273, missingCheck_27_275, missingCheck_27_280, missingCheck_27_294, missingCheck_27_297, missingCheck_27_308, missingCheck_27_315, missingCheck_27_320, missingCheck_27_325, missingCheck_27_330, missingCheck_27_338, missingCheck_27_350, missingCheck_27_351, missingCheck_27_352, missingCheck_27_364, missingCheck_27_375, missingCheck_27_384, missingCheck_27_390, missingCheck_27_396, missingCheck_27_405, missingCheck_27_416, missingCheck_27_420, missingCheck_27_440, missingCheck_27_441, missingCheck_27_450, missingCheck_27_462, missingCheck_27_468, missingCheck_27_480, missingCheck_27_484, missingCheck_27_486, missingCheck_27_500, missingCheck_27_504, missingCheck_27_520, missingCheck_27_525, missingCheck_27_528, missingCheck_27_540, missingCheck_27_546, missingCheck_27_550, missingCheck_27_567, missingCheck_27_572, missingCheck_27_576, missingCheck_27_594, missingCheck_27_600, missingCheck_27_624, missingCheck_27_625, missingCheck_27_648, missingCheck_27_650, missingCheck_27_675, missingCheck_27_676, missingCheck_27_702, missingCheck_27_729, by simp⟩

private def missingCore28 : Finset ℕ :=
  ⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28] : List ℕ), by decide⟩

private def missingUnique28 : Finset ℕ :=
  ⟨([1, 2, 3, 5, 7, 11, 13, 33, 35, 39, 49, 55, 65, 77, 91, 98, 99, 117, 121, 125, 128, 143, 147, 165, 169, 175, 195, 231, 242, 243, 250, 256, 273, 275, 294, 297, 315, 320, 325, 330, 338, 350, 351, 352, 375, 384, 390, 392, 396, 405, 416, 440, 441, 448, 450, 462, 468, 480, 484, 486, 500, 520, 525, 528, 540, 546, 550, 560, 567, 572, 576, 588, 594, 600, 616, 624, 625, 648, 650, 672, 675, 676, 700, 702, 728, 729, 756, 784] : List ℕ), by decide⟩

private theorem missingCore28_eq : core 28 = missingCore28 := by decide +kernel

private theorem missingUnique28_divisors :
    ∀ u ∈ missingUnique28,
      (missingCore28.filter (fun a =>
        a ≤ u / a ∧ u % a = 0 ∧ u / a ∈ missingCore28)).card = 1 := by
  decide +kernel

private theorem missingUnique28_eq : uniqueProducts 28 = missingUnique28 := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    have hc : (representations 28 u).card = 1 := by
      rw [representations_card_eq]
      simpa only [representationDivisors, missingCore28_eq] using
        missingUnique28_divisors u hu
    refine Finset.mem_filter.mpr ⟨?_, hc⟩
    exact representations_nonempty_iff.mp
      (Finset.card_pos.mp (by omega : 0 < (representations 28 u).card))
  · rw [uniqueProducts_card_28]
    decide +kernel

private theorem missingCheck_28_1 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 1 a := by
  decide +kernel

private theorem missingCheck_28_2 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 2 a := by
  decide +kernel

private theorem missingCheck_28_3 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 3 a := by
  decide +kernel

private theorem missingCheck_28_5 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 5 a := by
  decide +kernel

private theorem missingCheck_28_7 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 7 a := by
  decide +kernel

private theorem missingCheck_28_11 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 11 a := by
  decide +kernel

private theorem missingCheck_28_13 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 13 a := by
  decide +kernel

private theorem missingCheck_28_33 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 33 a := by
  decide +kernel

private theorem missingCheck_28_35 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 35 a := by
  decide +kernel

private theorem missingCheck_28_39 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 39 a := by
  decide +kernel

private theorem missingCheck_28_49 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 49 a := by
  decide +kernel

private theorem missingCheck_28_55 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 55 a := by
  decide +kernel

private theorem missingCheck_28_65 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 65 a := by
  decide +kernel

private theorem missingCheck_28_77 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 77 a := by
  decide +kernel

private theorem missingCheck_28_91 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 91 a := by
  decide +kernel

private theorem missingCheck_28_98 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 98 a := by
  decide +kernel

private theorem missingCheck_28_99 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 99 a := by
  decide +kernel

private theorem missingCheck_28_117 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 117 a := by
  decide +kernel

private theorem missingCheck_28_121 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 121 a := by
  decide +kernel

private theorem missingCheck_28_125 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 125 a := by
  decide +kernel

private theorem missingCheck_28_128 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 128 a := by
  decide +kernel

private theorem missingCheck_28_143 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 143 a := by
  decide +kernel

private theorem missingCheck_28_147 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 147 a := by
  decide +kernel

private theorem missingCheck_28_165 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 165 a := by
  decide +kernel

private theorem missingCheck_28_169 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 169 a := by
  decide +kernel

private theorem missingCheck_28_175 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 175 a := by
  decide +kernel

private theorem missingCheck_28_195 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 195 a := by
  decide +kernel

private theorem missingCheck_28_231 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 231 a := by
  decide +kernel

private theorem missingCheck_28_242 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 242 a := by
  decide +kernel

private theorem missingCheck_28_243 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 243 a := by
  decide +kernel

private theorem missingCheck_28_250 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 250 a := by
  decide +kernel

private theorem missingCheck_28_256 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 256 a := by
  decide +kernel

private theorem missingCheck_28_273 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 273 a := by
  decide +kernel

private theorem missingCheck_28_275 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 275 a := by
  decide +kernel

private theorem missingCheck_28_294 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 294 a := by
  decide +kernel

private theorem missingCheck_28_297 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 297 a := by
  decide +kernel

private theorem missingCheck_28_315 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 315 a := by
  decide +kernel

private theorem missingCheck_28_320 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 320 a := by
  decide +kernel

private theorem missingCheck_28_325 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 325 a := by
  decide +kernel

private theorem missingCheck_28_330 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 330 a := by
  decide +kernel

private theorem missingCheck_28_338 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 338 a := by
  decide +kernel

private theorem missingCheck_28_350 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 350 a := by
  decide +kernel

private theorem missingCheck_28_351 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 351 a := by
  decide +kernel

private theorem missingCheck_28_352 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 352 a := by
  decide +kernel

private theorem missingCheck_28_375 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 375 a := by
  decide +kernel

private theorem missingCheck_28_384 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 384 a := by
  decide +kernel

private theorem missingCheck_28_390 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 390 a := by
  decide +kernel

private theorem missingCheck_28_392 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 392 a := by
  decide +kernel

private theorem missingCheck_28_396 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 396 a := by
  decide +kernel

private theorem missingCheck_28_405 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 405 a := by
  decide +kernel

private theorem missingCheck_28_416 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 416 a := by
  decide +kernel

private theorem missingCheck_28_440 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 440 a := by
  decide +kernel

private theorem missingCheck_28_441 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 441 a := by
  decide +kernel

private theorem missingCheck_28_448 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 448 a := by
  decide +kernel

private theorem missingCheck_28_450 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 450 a := by
  decide +kernel

private theorem missingCheck_28_462 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 462 a := by
  decide +kernel

private theorem missingCheck_28_468 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 468 a := by
  decide +kernel

private theorem missingCheck_28_480 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 480 a := by
  decide +kernel

private theorem missingCheck_28_484 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 484 a := by
  decide +kernel

private theorem missingCheck_28_486 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 486 a := by
  decide +kernel

private theorem missingCheck_28_500 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 500 a := by
  decide +kernel

private theorem missingCheck_28_520 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 520 a := by
  decide +kernel

private theorem missingCheck_28_525 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 525 a := by
  decide +kernel

private theorem missingCheck_28_528 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 528 a := by
  decide +kernel

private theorem missingCheck_28_540 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 540 a := by
  decide +kernel

private theorem missingCheck_28_546 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 546 a := by
  decide +kernel

private theorem missingCheck_28_550 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 550 a := by
  decide +kernel

private theorem missingCheck_28_560 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 560 a := by
  decide +kernel

private theorem missingCheck_28_567 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 567 a := by
  decide +kernel

private theorem missingCheck_28_572 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 572 a := by
  decide +kernel

private theorem missingCheck_28_576 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 576 a := by
  decide +kernel

private theorem missingCheck_28_588 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 588 a := by
  decide +kernel

private theorem missingCheck_28_594 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 594 a := by
  decide +kernel

private theorem missingCheck_28_600 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 600 a := by
  decide +kernel

private theorem missingCheck_28_616 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 616 a := by
  decide +kernel

private theorem missingCheck_28_624 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 624 a := by
  decide +kernel

private theorem missingCheck_28_625 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 625 a := by
  decide +kernel

private theorem missingCheck_28_648 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 648 a := by
  decide +kernel

private theorem missingCheck_28_650 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 650 a := by
  decide +kernel

private theorem missingCheck_28_672 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 672 a := by
  decide +kernel

private theorem missingCheck_28_675 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 675 a := by
  decide +kernel

private theorem missingCheck_28_676 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 676 a := by
  decide +kernel

private theorem missingCheck_28_700 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 700 a := by
  decide +kernel

private theorem missingCheck_28_702 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 702 a := by
  decide +kernel

private theorem missingCheck_28_728 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 728 a := by
  decide +kernel

private theorem missingCheck_28_729 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 729 a := by
  decide +kernel

private theorem missingCheck_28_756 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 756 a := by
  decide +kernel

private theorem missingCheck_28_784 :
    ∀ a ∈ missingCore28, MissingWitnessProperty missingCore28 missingUnique28 28 784 a := by
  decide +kernel

private theorem missingChecks28 :
    ∀ u ∈ missingUnique28, ∀ a ∈ missingCore28,
      MissingWitnessProperty missingCore28 missingUnique28 28 u a := by
  change ∀ u ∈ ([1, 2, 3, 5, 7, 11, 13, 33, 35, 39, 49, 55, 65, 77, 91, 98, 99, 117, 121, 125, 128, 143, 147, 165, 169, 175, 195, 231, 242, 243, 250, 256, 273, 275, 294, 297, 315, 320, 325, 330, 338, 350, 351, 352, 375, 384, 390, 392, 396, 405, 416, 440, 441, 448, 450, 462, 468, 480, 484, 486, 500, 520, 525, 528, 540, 546, 550, 560, 567, 572, 576, 588, 594, 600, 616, 624, 625, 648, 650, 672, 675, 676, 700, 702, 728, 729, 756, 784] : List ℕ), ∀ a ∈ missingCore28,
    MissingWitnessProperty missingCore28 missingUnique28 28 u a
  simp only [List.forall_mem_cons, List.forall_mem_nil]
  exact ⟨missingCheck_28_1, missingCheck_28_2, missingCheck_28_3, missingCheck_28_5, missingCheck_28_7, missingCheck_28_11, missingCheck_28_13, missingCheck_28_33, missingCheck_28_35, missingCheck_28_39, missingCheck_28_49, missingCheck_28_55, missingCheck_28_65, missingCheck_28_77, missingCheck_28_91, missingCheck_28_98, missingCheck_28_99, missingCheck_28_117, missingCheck_28_121, missingCheck_28_125, missingCheck_28_128, missingCheck_28_143, missingCheck_28_147, missingCheck_28_165, missingCheck_28_169, missingCheck_28_175, missingCheck_28_195, missingCheck_28_231, missingCheck_28_242, missingCheck_28_243, missingCheck_28_250, missingCheck_28_256, missingCheck_28_273, missingCheck_28_275, missingCheck_28_294, missingCheck_28_297, missingCheck_28_315, missingCheck_28_320, missingCheck_28_325, missingCheck_28_330, missingCheck_28_338, missingCheck_28_350, missingCheck_28_351, missingCheck_28_352, missingCheck_28_375, missingCheck_28_384, missingCheck_28_390, missingCheck_28_392, missingCheck_28_396, missingCheck_28_405, missingCheck_28_416, missingCheck_28_440, missingCheck_28_441, missingCheck_28_448, missingCheck_28_450, missingCheck_28_462, missingCheck_28_468, missingCheck_28_480, missingCheck_28_484, missingCheck_28_486, missingCheck_28_500, missingCheck_28_520, missingCheck_28_525, missingCheck_28_528, missingCheck_28_540, missingCheck_28_546, missingCheck_28_550, missingCheck_28_560, missingCheck_28_567, missingCheck_28_572, missingCheck_28_576, missingCheck_28_588, missingCheck_28_594, missingCheck_28_600, missingCheck_28_616, missingCheck_28_624, missingCheck_28_625, missingCheck_28_648, missingCheck_28_650, missingCheck_28_672, missingCheck_28_675, missingCheck_28_676, missingCheck_28_700, missingCheck_28_702, missingCheck_28_728, missingCheck_28_729, missingCheck_28_756, missingCheck_28_784, by simp⟩

/-- Every anchored rational translate of the unique-product set misses two
distinct core elements, expressed without rational division. -/
theorem two_missing_anchored (n : ℕ) (hn : n = 27 ∨ n = 28) :
    ∀ u ∈ uniqueProducts n, ∀ a ∈ core n,
      ∃ x ∈ core n, ∃ y ∈ core n, x ≠ y ∧
        (∀ v ∈ uniqueProducts n, u * x ≠ v * a) ∧
        (∀ v ∈ uniqueProducts n, u * y ≠ v * a) := by
  rcases hn with rfl | rfl
  · rw [missingUnique27_eq, missingCore27_eq]
    intro u hu a ha
    have h := missingChecks27 u hu a ha
    exact ⟨(missingWitnesses 27 u a).1, h.1, (missingWitnesses 27 u a).2, h.2.1, h.2.2⟩
  · rw [missingUnique28_eq, missingCore28_eq]
    intro u hu a ha
    have h := missingChecks28 u hu a ha
    exact ⟨(missingWitnesses 28 u a).1, h.1, (missingWitnesses 28 u a).2, h.2.1, h.2.2⟩

end WeightedPilz.Arithmetic

