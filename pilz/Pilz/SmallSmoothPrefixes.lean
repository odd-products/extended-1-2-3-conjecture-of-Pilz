import Pilz.TrialSmooth

/-! Shared prefix certificates for the finite small-interval smooth cores. -/

namespace Pilz

def smallSmoothSetFive : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32, 36, 40, 45, 48, 50, 54, 60, 64}
def smallSmoothSetSeven : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42, 45, 48, 49, 50, 54, 56, 60, 63, 64}

theorem smoothNumbers_prefix (T : Finset ℕ) {n m : ℕ} (hnm : n ≤ m) :
    smoothNumbers T n = (smoothNumbers T m).filter (fun a => a ≤ n) := by
  ext a
  simp only [Finset.mem_filter, mem_smoothNumbers]
  constructor
  · rintro ⟨hpos, han, hsm⟩
    exact ⟨⟨hpos, han.trans hnm, hsm⟩, han⟩
  · rintro ⟨⟨hpos, _ham, hsm⟩, han⟩
    exact ⟨hpos, han, hsm⟩

private theorem smallPrimesSixtySix :
    primesUpTo 66 = ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} : Finset ℕ) := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem smallSmooth_five_sixty_six :
    smoothNumbers (primesUpTo 5) 66 = smallSmoothSetFive := by
  rw [smoothNumbers_eq_trialSmoothNumbers]
  unfold trialSmoothNumbers
  rw [smallPrimesSixtySix]
  have h5 : primesUpTo 5 = ({2, 3, 5} : Finset ℕ) := by decide
  rw [h5]
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem smallSmooth_seven_sixty_six :
    smoothNumbers (primesUpTo 7) 66 = smallSmoothSetSeven := by
  rw [smoothNumbers_eq_trialSmoothNumbers]
  unfold trialSmoothNumbers
  rw [smallPrimesSixtySix]
  have h7 : primesUpTo 7 = ({2, 3, 5, 7} : Finset ℕ) := by decide
  rw [h7]
  decide

theorem smallSmooth_five_prefix {n : ℕ} (hn : n ≤ 66) :
    smoothNumbers (primesUpTo 5) n = smallSmoothSetFive.filter (fun a => a ≤ n) := by
  rw [smoothNumbers_prefix _ hn, smallSmooth_five_sixty_six]

theorem smallSmooth_seven_prefix {n : ℕ} (hn : n ≤ 66) :
    smoothNumbers (primesUpTo 7) n = smallSmoothSetSeven.filter (fun a => a ≤ n) := by
  rw [smoothNumbers_prefix _ hn, smallSmooth_seven_sixty_six]

end Pilz

