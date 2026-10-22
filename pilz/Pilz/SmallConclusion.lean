import Pilz.SmallInitial
import Pilz.SmallRegular
import Pilz.SmallCoreTable
import Pilz.SmallNumerics
import Pilz.SmallExceptional
import Pilz.FewExceptions
import Pilz.FewException27

/-! Joining the exact core bounds and numerical rows for the small intervals. -/

namespace Pilz

theorem conjectureAt_regular_table (n : ℕ) (hlo : 11 ≤ n) (hhi : n ≤ 66)
    (hreg : SmallRegularIndex n) : ConjectureAt n := by
  have hκ : (smallRow n).κ ≤ distance (core n) := by
    rw [smallRow_coreKappa n hlo hhi]
    exact coreKappa_distance_lower n hlo hhi
  obtain ⟨hMthree, hMfour, hNM⟩ := smallRow_regular n hreg
  exact conjectureAt_small_regular n (smallRow n).κ (smallRow n).r (smallRow n).T
    (smallRow n).U (smallRow n).M hlo hhi
    (smallRow_fresh_card n hlo hhi) (smallRow_r_pos n hlo hhi) hκ
    (smallRow_kappa_pos n hlo hhi) (smallRow_bound n hlo hhi)
    (smallRow_reduce n hlo hhi) (smallRow_U_le_four n hlo hhi)
    hMthree hMfour hNM

theorem conjectureAt_refined_table (n : ℕ) (hlo : 26 ≤ n) (hhi : n ≤ 29)
    (href : SmallRefinedIndex n) : ConjectureAt n := by
  have hn11 : 11 ≤ n := by omega
  have hn66 : n ≤ 66 := by omega
  have hκ : (smallRow n).κ ≤ distance (core n) := by
    rw [smallRow_coreKappa n hn11 hn66]
    exact coreKappa_distance_lower n hn11 hn66
  obtain ⟨hU, hMtwo, hMthree, hNM⟩ := smallRow_refined n href
  exact conjectureAt_small_regular_26_29 n (smallRow n).κ (smallRow n).r (smallRow n).T
    (smallRow n).U (smallRow n).M hlo hhi
    (smallRow_fresh_card n hn11 hn66) (smallRow_r_pos n hn11 hn66) hκ
    (smallRow_kappa_pos n hn11 hn66) (smallRow_bound n hn11 hn66)
    (smallRow_reduce n hn11 hn66) hU hMtwo hMthree hNM

theorem four_term_exception_product (n : ℕ) (hex : SmallExceptionalIndex n)
    (D : Poly) (hw : weight D = 4) :
    smallProductBound n ≤ weight (interval n * D) := by
  rcases smallRow_exception_cases n hex with h27 | h40 | ⟨h49, h52⟩
  · subst n
    simpa [smallProductBound] using four_term_at_twenty_seven D hw
  · subst n
    simpa [smallProductBound] using four_term_at_forty D hw
  · have h27 : n ≠ 27 := by omega
    have h40 : n ≠ 40 := by omega
    simpa [smallProductBound, h27, h40] using
      four_term_at_forty_nine_to_fifty_two n D h49 h52 hw

theorem conjectureAt_exceptional_table (n : ℕ) (hlo : 11 ≤ n) (hhi : n ≤ 66)
    (hex : SmallExceptionalIndex n) : ConjectureAt n := by
  have hκ : (smallRow n).κ ≤ distance (core n) := by
    rw [smallRow_coreKappa n hlo hhi]
    exact coreKappa_distance_lower n hlo hhi
  obtain ⟨hU, hMthree, hMfour, hNMthree, hclassNum, hMfourN, hBN, hBM⟩ :=
    smallRow_exception n hex
  apply conjectureAt_small_exceptional n (smallRow n).κ (smallRow n).r (smallRow n).T
    (smallMThree n) (smallMFour n) (smallProductBound n) hlo hhi
    (smallRow_fresh_card n hlo hhi) (smallRow_r_pos n hlo hhi) hκ
    (smallRow_kappa_pos n hlo hhi) (smallRow_bound n hlo hhi)
    ?_ hMthree hMfour hNMthree hclassNum hMfourN ?_ hBN hBM
  · intro m u hu hru hhalf hmT
    obtain ⟨husmall, hured⟩ := smallRow_reduce n hlo hhi m u hu hru hhalf hmT
    refine ⟨husmall, ?_⟩
    intro hcore
    simpa only [hU] using hured hcore
  · intro D _hD hw
    exact four_term_exception_product n hex D hw

/-- The complete small-length branch of the paper. -/
theorem conjectureAt_le_sixty_six (n : ℕ) (hn : n ≤ 66) : ConjectureAt n := by
  by_cases hten : n ≤ 10
  · exact conjectureAt_le_ten n hten
  have h11 : 11 ≤ n := by omega
  rcases smallRow_index_cases n h11 hn with hreg | href | hex
  · exact conjectureAt_regular_table n h11 hn hreg
  · obtain ⟨h26, h29⟩ := smallRow_refined_range n href
    exact conjectureAt_refined_table n h26 h29 href
  · exact conjectureAt_exceptional_table n h11 hn hex

end Pilz
