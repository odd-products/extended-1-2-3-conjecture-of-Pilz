import Pilz.RoughComponents
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Exact numbers of rough components at each index threshold. -/

noncomputable section

namespace Pilz

open scoped BigOperators

@[simp] theorem smoothInterval_one (T : Finset ℕ) : smoothInterval T 1 = 1 := by
  simp [smoothInterval, smoothNumbers, Finset.filter_singleton]

theorem roughNumbers_index_ge (T : Finset ℕ) (n k : ℕ) (hk : 0 < k) :
    (roughNumbers T n).filter (fun b => k ≤ n / b) = roughNumbers T (n / k) := by
  ext b
  constructor
  · intro hb
    obtain ⟨hb, hidx⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbpos, _hbn, hbrough⟩ := (mem_roughNumbers T n b).mp hb
    apply (mem_roughNumbers T (n / k) b).mpr
    refine ⟨hbpos, ?_, hbrough⟩
    apply (Nat.le_div_iff_mul_le hk).mpr
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hbpos).mp hidx
  · intro hb
    obtain ⟨hbpos, hbn, hbrough⟩ := (mem_roughNumbers T (n / k) b).mp hb
    apply Finset.mem_filter.mpr
    refine ⟨(mem_roughNumbers T n b).mpr
      ⟨hbpos, hbn.trans (Nat.div_le_self n k), hbrough⟩, ?_⟩
    apply (Nat.le_div_iff_mul_le hbpos).mpr
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk).mp hbn

/-- Components of index at least `k` are counted by `Phi_T(n/k)`. -/
theorem card_roughNumbers_index_ge (T : Finset ℕ) (n k : ℕ) (hk : 0 < k) :
    ((roughNumbers T n).filter (fun b => k ≤ n / b)).card = roughCount T (n / k) := by
  rw [roughNumbers_index_ge T n k hk]
  rfl

theorem roughNumbers_index_one (T : Finset ℕ) (n : ℕ) :
    (roughNumbers T n).filter (fun b => n / b = 1) =
      roughNumbers T n \ roughNumbers T (n / 2) := by
  rw [← roughNumbers_index_ge T n 2 (by decide)]
  ext b
  by_cases hb : b ∈ roughNumbers T n
  · obtain ⟨hbpos, hbn, _hbrough⟩ := (mem_roughNumbers T n b).mp hb
    have hidx : 1 ≤ n / b := (Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn)
    simp only [Finset.mem_filter, Finset.mem_sdiff, hb, true_and]
    omega
  · simp [hb]

/-- The index-one components are counted by the half-interval rough count. -/
theorem card_roughNumbers_index_one (T : Finset ℕ) (n : ℕ) :
    ((roughNumbers T n).filter (fun b => n / b = 1)).card = roughIntervalCount T n := by
  rw [roughNumbers_index_one,
    Finset.card_sdiff_of_subset (roughNumbers_mono T (Nat.div_le_self n 2))]
  rfl

/-- The original rough-number lower bound through the copies of `D` in
components of index one, without any profile estimate for larger indices. -/
theorem weight_interval_mul_ge_index_one (T : Finset ℕ) (n : ℕ) (D : Poly)
    (hT : ∀ p ∈ T, Nat.Prime p) (hD : D.vars ⊆ T) :
    weight D * roughIntervalCount T n ≤ weight (interval n * D) := by
  classical
  rw [weight_interval_mul_eq_sum_rough_components T n D hT hD]
  let B := (roughNumbers T n).filter (fun b => n / b = 1)
  calc
    weight D * roughIntervalCount T n = B.card * weight D := by
      rw [card_roughNumbers_index_one]
      exact Nat.mul_comm _ _
    _ = ∑ b ∈ B, weight (smoothInterval T (n / b) * D) := by
      symm
      calc
        (∑ b ∈ B, weight (smoothInterval T (n / b) * D)) = ∑ _b ∈ B, weight D := by
          apply Finset.sum_congr rfl
          intro b hb
          have hidx : n / b = 1 := (Finset.mem_filter.mp hb).2
          rw [hidx, smoothInterval_one, one_mul]
        _ = B.card * weight D := by simp
    _ ≤ ∑ b ∈ roughNumbers T n, weight (smoothInterval T (n / b) * D) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end Pilz
