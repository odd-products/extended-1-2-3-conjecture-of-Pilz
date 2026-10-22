import Pilz.PrimeCounts
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

/-! Exact rough-number counting, the arithmetic basis of the paper's sieve. -/

namespace Pilz

/-- Positive integers at most `n` divisible by none of the primes in `T`. -/
def roughNumbers (T : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun b => ∀ p ∈ T, ¬p ∣ b

/-- Integer-argument version of the paper's `Phi_T`. -/
def roughCount (T : Finset ℕ) (n : ℕ) : ℕ := (roughNumbers T n).card

/-- The number of rough integers in `(n/2,n]`. -/
def roughIntervalCount (T : Finset ℕ) (n : ℕ) : ℕ :=
  roughCount T n - roughCount T (n / 2)

theorem mem_roughNumbers (T : Finset ℕ) (n b : ℕ) :
    b ∈ roughNumbers T n ↔ 1 ≤ b ∧ b ≤ n ∧ ∀ p ∈ T, ¬p ∣ b := by
  simp [roughNumbers, and_assoc]

theorem roughNumbers_mono (T : Finset ℕ) {a b : ℕ} (hab : a ≤ b) :
    roughNumbers T a ⊆ roughNumbers T b := by
  intro x hx
  rw [mem_roughNumbers] at hx ⊢
  exact ⟨hx.1, hx.2.1.trans hab, hx.2.2⟩

theorem roughCount_mono (T : Finset ℕ) {a b : ℕ} (hab : a ≤ b) :
    roughCount T a ≤ roughCount T b :=
  Finset.card_le_card (roughNumbers_mono T hab)

@[simp] theorem roughCount_empty (n : ℕ) : roughCount ∅ n = n := by
  simp [roughCount, roughNumbers]

theorem roughCount_le (T : Finset ℕ) (n : ℕ) : roughCount T n ≤ n := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun b => ∀ p ∈ T, ¬p ∣ b) (Finset.Icc 1 n))
  simpa [roughCount, roughNumbers] using h

/-- Multiplication by a new prime preserves roughness with respect to `T`. -/
theorem rough_mul_new_prime (T : Finset ℕ) (p b : ℕ)
    (hT : ∀ q ∈ T, Nat.Prime q) (hp : Nat.Prime p) (hpT : p ∉ T) :
    (∀ q ∈ T, ¬q ∣ p * b) ↔ (∀ q ∈ T, ¬q ∣ b) := by
  constructor
  · intro h q hq hdiv
    exact h q hq (dvd_mul_of_dvd_right hdiv p)
  · intro h q hq hdiv
    rcases (hT q hq).dvd_mul.mp hdiv with hqp | hqb
    · have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq (hT q hq) hp).mp hqp
      exact hpT (hqp' ▸ hq)
    · exact h q hq hqb

theorem rough_multiples_eq_image (T : Finset ℕ) (p n : ℕ)
    (hT : ∀ q ∈ T, Nat.Prime q) (hp : Nat.Prime p) (hpT : p ∉ T) :
    (roughNumbers T n).filter (fun b => p ∣ b) =
      (roughNumbers T (n / p)).image (fun b => p * b) := by
  ext b
  constructor
  · intro hb
    obtain ⟨hrough, hdiv⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbpos, hbn, havoid⟩ := (mem_roughNumbers T n b).mp hrough
    obtain ⟨c, hc⟩ := hdiv
    apply Finset.mem_image.mpr
    refine ⟨c, ?_, hc.symm⟩
    apply (mem_roughNumbers T (n / p) c).mpr
    have hcpos : 1 ≤ c := by
      by_contra hnot
      have hz : c = 0 := by omega
      simp [hz] at hc
      omega
    refine ⟨hcpos, ?_, ?_⟩
    · apply (Nat.le_div_iff_mul_le hp.pos).mpr
      simpa [hc, Nat.mul_comm] using hbn
    · apply (rough_mul_new_prime T p c hT hp hpT).mp
      simpa [← hc] using havoid
  · intro hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hcpos, hcn, havoid⟩ := (mem_roughNumbers T (n / p) c).mp hc
    apply Finset.mem_filter.mpr
    refine ⟨?_, dvd_mul_right p c⟩
    apply (mem_roughNumbers T n (p * c)).mpr
    refine ⟨Nat.mul_pos hp.pos hcpos, ?_, ?_⟩
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hcn
    · exact (rough_mul_new_prime T p c hT hp hpT).mpr havoid

/-- The exact one-prime Legendre sieve recurrence used in the paper. -/
theorem roughCount_insert (T : Finset ℕ) (p n : ℕ)
    (hT : ∀ q ∈ T, Nat.Prime q) (hp : Nat.Prime p) (hpT : p ∉ T) :
    roughCount (insert p T) n = roughCount T n - roughCount T (n / p) := by
  have hset : roughNumbers (insert p T) n =
      roughNumbers T n \ (roughNumbers T n).filter (fun b => p ∣ b) := by
    ext b
    simp only [mem_roughNumbers, Finset.mem_sdiff, Finset.mem_filter,
      Finset.forall_mem_insert]
    tauto
  unfold roughCount
  rw [hset, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    rough_multiples_eq_image T p n hT hp hpT]
  rw [Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp.pos h)]

theorem roughCount_singleton (p n : ℕ) (hp : Nat.Prime p) :
    roughCount {p} n = n - n / p := by
  simpa using roughCount_insert ∅ p n (by simp) hp (by simp)

theorem roughCount_insert_add (T : Finset ℕ) (p n : ℕ)
    (hT : ∀ q ∈ T, Nat.Prime q) (hp : Nat.Prime p) (hpT : p ∉ T) :
    roughCount (insert p T) n + roughCount T (n / p) = roughCount T n := by
  rw [roughCount_insert T p n hT hp hpT]
  exact Nat.sub_add_cancel (roughCount_mono T (Nat.div_le_self n p))

theorem roughCount_two (n : ℕ) : roughCount {2} n = (n + 1) / 2 := by
  rw [roughCount_singleton 2 n (by decide)]
  omega

end Pilz
