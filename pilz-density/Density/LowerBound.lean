import Density.Partition
import Density.CutLimit
import Mathlib.Tactic.Linarith

/-! The elementary induction and prime split, factored so that each ingredient
can be checked independently before the unconditional assembly. -/

noncomputable section

namespace PilzDensity

theorem density_prime_cut_of
    (hD : ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → HasDensity A (density A))
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (p : ℕ) (hp : Nat.Prime p) :
    (1 - 2 / (p : ℝ)) * density (lowerSlice A p) + density (upperSlice A p)
      ≤ density A := by
  have hB : ∀ a ∈ lowerSlice A p, 0 < a :=
    fun a ha => hA a (lowerSlice_subset A p ha)
  have hC : ∀ a ∈ upperSlice A p, 0 < a :=
    fun a ha => hA a (upperSlice_subset A p ha)
  have hU : HasDensity (lowerSlice A p ∪ upperSlice A p) (density A) := by
    rw [slice_union]
    exact hD A hA
  exact hU.exact_cut (hD _ hB) (hD _ hC) p hp.pos (slice_disjoint A p)
    (fun a ha => hp.coprime_iff_not_dvd.mpr (Finset.mem_filter.mp ha).2)
    (fun a ha => (Finset.mem_filter.mp ha).2)

theorem baseline_lower_bound_of
    (hD : ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → HasDensity A (density A))
    (hN : ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → A.Nonempty →
      ∃ B : Finset ℕ, (∀ b ∈ B, 0 < b) ∧ B.Nonempty ∧ B.gcd id = 1 ∧
        B.card = A.card ∧ density B = density A ∧ (Exceptional B ↔ Exceptional A))
    (hS : ∀ a : ℕ, 0 < a → density {a} = 1)
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    (1 : ℝ) ≤ density A := by
  classical
  suffices H : ∀ k : ℕ, ∀ S : Finset ℕ, S.card = k →
      (∀ a ∈ S, 0 < a) → S.Nonempty → (1 : ℝ) ≤ density S by
    exact H A.card A rfl hA hne
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro S hcard hpos hne
    obtain ⟨B, hBpos, hBne, hBgcd, hBcard, hBdensity, _⟩ := hN S hpos hne
    rw [← hBdensity]
    by_cases hone : B.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hone
      rw [hS a (hBpos a (by simp))]
    · have hmany : 1 < B.card := by
        have := Finset.card_pos.mpr hBne
        omega
      obtain ⟨p, hp, hpa⟩ := exists_prime_divisor_of_one_lt_card B hmany
      have hlne := lowerSlice_nonempty B p hp hBgcd
      have hune := upperSlice_nonempty B p hpa
      have hlpos : ∀ a ∈ lowerSlice B p, 0 < a :=
        fun a ha => hBpos a (lowerSlice_subset B p ha)
      have hupos : ∀ a ∈ upperSlice B p, 0 < a :=
        fun a ha => hBpos a (upperSlice_subset B p ha)
      have hllt : (lowerSlice B p).card < k := by
        simpa only [hBcard, hcard] using lowerSlice_card_lt B p hune
      have hult : (upperSlice B p).card < k := by
        simpa only [hBcard, hcard] using upperSlice_card_lt B p hlne
      have hl := ih _ hllt _ rfl hlpos hlne
      have hu := ih _ hult _ rfl hupos hune
      have hcut := density_prime_cut_of hD B hBpos p hp
      have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
      have hquot : (2 : ℝ) / (p : ℝ) ≤ 1 := (div_le_one hp0).mpr hpr
      have hc : (0 : ℝ) ≤ 1 - 2 / (p : ℝ) := by linarith
      have hm := mul_le_mul_of_nonneg_left hl hc
      nlinarith

theorem odd_prime_lower_bound_of
    (hD : ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → HasDensity A (density A))
    (hbase : ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → A.Nonempty →
      (1 : ℝ) ≤ density A)
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hgcd : A.gcd id = 1)
    (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hpa : ∃ a ∈ A, p ∣ a) :
    (4 : ℝ) / 3 ≤ density A := by
  have hl := hbase (lowerSlice A p)
    (fun a ha => hA a (lowerSlice_subset A p ha))
    (lowerSlice_nonempty A p hp hgcd)
  have hu := hbase (upperSlice A p)
    (fun a ha => hA a (upperSlice_subset A p ha))
    (upperSlice_nonempty A p hpa)
  have hcut := density_prime_cut_of hD A hA p hp
  have hpr : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hquot : (2 : ℝ) / (p : ℝ) ≤ 2 / 3 := by
    apply (div_le_iff₀ hp0).mpr
    linarith
  have hc : (0 : ℝ) ≤ 1 - 2 / (p : ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_left hl hc
  nlinarith

theorem sharp_lower_bound_of
    (hD : ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → HasDensity A (density A))
    (hN : ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → A.Nonempty →
      ∃ B : Finset ℕ, (∀ b ∈ B, 0 < b) ∧ B.Nonempty ∧ B.gcd id = 1 ∧
        B.card = A.card ∧ density B = density A ∧ (Exceptional B ↔ Exceptional A))
    (hS : ∀ a : ℕ, 0 < a → density {a} = 1)
    (hdyadic : ∀ A : Finset ℕ, A.Nonempty →
      (∀ a ∈ A, ∃ k : ℕ, a = 2 ^ k) → ¬ Exceptional A →
      (3 : ℝ) / 2 ≤ density A)
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty)
    (hnot : ¬ Exceptional A) : (4 : ℝ) / 3 ≤ density A := by
  classical
  obtain ⟨B, hBpos, hBne, hBgcd, _, hBdensity, hBexcept⟩ := hN A hA hne
  rw [← hBdensity]
  by_cases hodd : ∃ p, Nat.Prime p ∧ 3 ≤ p ∧ ∃ a ∈ B, p ∣ a
  · obtain ⟨p, hp, hp3, hpa⟩ := hodd
    exact odd_prime_lower_bound_of hD (baseline_lower_bound_of hD hN hS)
      B hBpos hBgcd p hp hp3 hpa
  · have hpow := powers_two_of_no_odd_prime B hBpos hodd
    have hBnot : ¬ Exceptional B := fun h => hnot (hBexcept.mp h)
    have hd := hdyadic B hBne hpow hBnot
    linarith

end PilzDensity
