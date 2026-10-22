import Density.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-! Arithmetic intersections of positive integer progressions. -/

noncomputable section

namespace PilzDensity

/-- The positive multiples of `a` with multiplier at most `n`. -/
def row (a n : ℕ) : Finset ℕ := (Finset.Icc 1 n).image (a * ·)

theorem mem_row_iff (a n m : ℕ) (ha : 0 < a) :
    m ∈ row a n ↔ 0 < m ∧ a ∣ m ∧ m ≤ a * n := by
  classical
  constructor
  · intro hm
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hbpos, hble⟩ := Finset.mem_Icc.mp hb
    exact ⟨Nat.mul_pos ha hbpos, dvd_mul_right a b, Nat.mul_le_mul_left a hble⟩
  · rintro ⟨hmpos, ⟨b, rfl⟩, hle⟩
    apply Finset.mem_image.mpr
    refine ⟨b, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Nat.pos_of_mul_pos_left hmpos
    · exact Nat.le_of_mul_le_mul_left hle ha

theorem representationCount_eq_filter_card (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (n m : ℕ) :
    Pilz.representationCount A (Finset.Icc 1 n) m =
      (A.filter fun a => m ∈ row a n).card := by
  classical
  unfold Pilz.representationCount
  apply Finset.card_bij (fun ab _ => ab.1)
  · rintro ⟨a, b⟩ hab
    obtain ⟨hab, heq⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact Finset.mem_filter.mpr ⟨ha, Finset.mem_image.mpr ⟨b, hb, heq⟩⟩
  · rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
    change a = c at heq
    subst c
    obtain ⟨hab, hmulb⟩ := Finset.mem_filter.mp hab
    obtain ⟨_, hmuld⟩ := Finset.mem_filter.mp hcd
    have ha := hA a (Finset.mem_product.mp hab).1
    have hbd : b = d := Nat.eq_of_mul_eq_mul_left ha (hmulb.trans hmuld.symm)
    subst d
    rfl
  · intro a ha
    obtain ⟨ha, hm⟩ := Finset.mem_filter.mp ha
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hm
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, heq⟩, rfl⟩

theorem intersection_eq (A J : Finset ℕ) (n : ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hJA : J ⊆ A) (hJ : J.Nonempty) :
    ((Pilz.productCandidates A (Finset.Icc 1 n)).filter
      fun m => ∀ j ∈ J, m ∈ row j n) =
    (Finset.Ioc 0 (n * J.min' hJ)).filter (J.lcm id ∣ ·) := by
  classical
  ext m
  constructor
  · intro hm
    obtain ⟨_, hm⟩ := Finset.mem_filter.mp hm
    have hjmin : J.min' hJ ∈ J := Finset.min'_mem J hJ
    have hmin := (mem_row_iff (J.min' hJ) n m (hA _ (hJA hjmin))).mp
      (hm _ hjmin)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hmin.1, ?_⟩, ?_⟩
    · simpa only [Nat.mul_comm] using hmin.2.2
    · apply Finset.lcm_dvd_iff.mpr
      intro j hj
      exact ((mem_row_iff j n m (hA j (hJA hj))).mp (hm j hj)).2.1
  · intro hm
    obtain ⟨hmrange, hmdiv⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmpos, hmle⟩ := Finset.mem_Ioc.mp hmrange
    have hall : ∀ j ∈ J, m ∈ row j n := by
      intro j hj
      apply (mem_row_iff j n m (hA j (hJA hj))).mpr
      refine ⟨hmpos, Finset.lcm_dvd_iff.mp hmdiv j hj, ?_⟩
      have hjle : J.min' hJ ≤ j := Finset.min'_le J j hj
      calc
        m ≤ n * J.min' hJ := hmle
        _ ≤ n * j := Nat.mul_le_mul_left n hjle
        _ = j * n := Nat.mul_comm _ _
    apply Finset.mem_filter.mpr
    refine ⟨?_, hall⟩
    obtain ⟨j, hj⟩ := hJ
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp (hall j hj)
    exact Finset.mem_image.mpr ⟨(j, b), Finset.mem_product.mpr ⟨hJA hj, hb⟩, heq⟩

theorem intersection_card (A J : Finset ℕ) (n : ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hJA : J ⊆ A) (hJ : J.Nonempty) :
    ((Pilz.productCandidates A (Finset.Icc 1 n)).filter
      fun m => ∀ j ∈ J, m ∈ row j n).card =
      n * J.min' hJ / J.lcm id := by
  rw [intersection_eq A J n hA hJA hJ]
  exact Nat.Ioc_filter_dvd_card_eq_div _ _

end PilzDensity
