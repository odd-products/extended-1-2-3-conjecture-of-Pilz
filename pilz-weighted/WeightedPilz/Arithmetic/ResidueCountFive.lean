import Pilz.Sieve30
import Pilz.SieveEstimates

/-! The exact eight-residue formula for the count sifted by `2,3,5`. -/

namespace WeightedPilz.Arithmetic

open scoped BigOperators

/-- The reduced positive residue classes modulo thirty. -/
def fiveResidues : Finset ℕ := {1, 7, 11, 13, 17, 19, 23, 29}

@[simp] theorem fiveResidues_card : fiveResidues.card = 8 := by decide

theorem fiveResidues_bounds {a : ℕ} (ha : a ∈ fiveResidues) :
    1 ≤ a ∧ a < 30 := by
  simp only [fiveResidues, Finset.mem_insert, Finset.mem_singleton] at ha
  omega

private theorem residue_prefix_certificate : ∀ r : Fin 30,
    Pilz.sieve30Formula r.val = (fiveResidues.filter (fun a => a ≤ r.val)).card := by
  decide

private theorem residue_floor_certificate : ∀ r : Fin 30,
    (fiveResidues.filter (fun a => a ≤ r.val)).card =
      ∑ a ∈ fiveResidues, (r.val + 30 - a) / 30 := by
  decide

/-- The exact finite prefix count in a complete block plus a final partial block. -/
theorem roughCount_five_residues (n : ℕ) :
    Pilz.roughCount {2, 3, 5} n =
      8 * (n / 30) + (fiveResidues.filter (fun a => a ≤ n % 30)).card := by
  have h := Pilz.roughCount_five_add_multiple (n % 30) (n / 30)
  rw [Nat.mod_add_div, Pilz.roughCount_two_three_five_formula (n % 30)] at h
  have hp := residue_prefix_certificate ⟨n % 30, Nat.mod_lt n (by decide)⟩
  change Pilz.sieve30Formula (n % 30) =
    (fiveResidues.filter (fun a => a ≤ n % 30)).card at hp
  rw [hp] at h
  exact h.trans (Nat.add_comm _ _)

/-- Each residue contributes its exact number of positive representatives. -/
theorem roughCount_five_floor_sum (n : ℕ) :
    Pilz.roughCount {2, 3, 5} n =
      ∑ a ∈ fiveResidues, (n + 30 - a) / 30 := by
  rw [roughCount_five_residues]
  have hp := residue_floor_certificate ⟨n % 30, Nat.mod_lt n (by decide)⟩
  change (fiveResidues.filter (fun a => a ≤ n % 30)).card =
    ∑ a ∈ fiveResidues, (n % 30 + 30 - a) / 30 at hp
  rw [hp]
  calc
    8 * (n / 30) + ∑ a ∈ fiveResidues, (n % 30 + 30 - a) / 30 =
        ∑ a ∈ fiveResidues, (n / 30 + (n % 30 + 30 - a) / 30) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        fiveResidues_card]
      rfl
    _ = ∑ a ∈ fiveResidues, (n + 30 - a) / 30 := by
      apply Finset.sum_congr rfl
      intro a ha
      have hab := fiveResidues_bounds ha
      have hm := Nat.mod_lt n (by decide : 0 < 30)
      have hn := Nat.mod_add_div n 30
      omega

/-- Passing from a real input to its natural floor preserves every summand. -/
theorem five_residue_floor_transport (x : ℝ) (hx : 0 ≤ x)
    {a : ℕ} (ha : a ∈ fiveResidues) :
    ⌊(x + 30 - (a : ℝ)) / 30⌋ = ((⌊x⌋₊ + 30 - a) / 30 : ℕ) := by
  have hab := fiveResidues_bounds ha
  have ha30 : a ≤ 30 := by omega
  have heq : x + 30 - (a : ℝ) = x + ((30 - a : ℕ) : ℝ) := by
    rw [Nat.cast_sub ha30]
    push_cast
    ring
  have hnonneg : 0 ≤ (x + 30 - (a : ℝ)) / 30 := by
    rw [heq]
    positivity
  rw [← Int.natCast_floor_eq_floor hnonneg]
  congr 1
  have hfloor : ⌊(x + ((30 - a : ℕ) : ℝ)) / 30⌋₊ =
      ⌊x + ((30 - a : ℕ) : ℝ)⌋₊ / 30 := by
    simpa only [Nat.cast_ofNat] using
      (Nat.floor_div_natCast (x + ((30 - a : ℕ) : ℝ)) 30)
  rw [heq, hfloor, Nat.floor_add_natCast hx]
  congr 1
  omega

/-- The manuscript's exact eight-floor formula, including nonintegral inputs. -/
theorem roughRealCount_five_floor_sum (x : ℝ) (hx : 0 ≤ x) :
    Pilz.roughRealCount {2, 3, 5} x =
      ∑ a ∈ fiveResidues, (⌊(x + 30 - (a : ℝ)) / 30⌋ : ℝ) := by
  unfold Pilz.roughRealCount
  rw [roughCount_five_floor_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [five_residue_floor_transport x hx ha]
  simp only [Int.cast_natCast]

/-- The equivalent quotient-and-remainder version of the real formula. -/
theorem roughRealCount_five_residues (x : ℝ) :
    Pilz.roughRealCount {2, 3, 5} x =
      8 * (⌊x⌋₊ / 30 : ℕ) +
        ((fiveResidues.filter (fun a => a ≤ ⌊x⌋₊ % 30)).card : ℝ) := by
  unfold Pilz.roughRealCount
  rw [roughCount_five_residues]
  push_cast
  rfl

end WeightedPilz.Arithmetic
