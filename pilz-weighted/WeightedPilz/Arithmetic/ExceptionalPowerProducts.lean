import WeightedPilz.ProductPowerCoefficients
import WeightedPilz.Arithmetic.UniqueProducts

/-! Exact unique-power-product witnesses for the frozen exceptional core bounds.
These finite certificates give an alternate proof of the same lower bounds. -/

namespace WeightedPilz.Arithmetic
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem persistent_power_unique {a n b j m : ℕ}
    (han : a ≤ n) (hnb : n ≤ b)
    (hlo : 0 < (powerRepresentations (core a) j m).card)
    (hhi : (powerRepresentations (core b) j m).card = 1) :
    (powerRepresentations (core n) j m).card = 1 := by
  have h1 := Finset.card_le_card (powerRepresentations_mono (core_mono han) j m)
  have h2 := Finset.card_le_card (powerRepresentations_mono (core_mono hnb) j m)
  omega

private def powerCore26 : Finset ℕ := ⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26] : List ℕ), by decide⟩
private theorem powerCore26_eq : core 26 = powerCore26 := by decide +kernel

private def powerCore28 : Finset ℕ := ⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28] : List ℕ), by decide⟩
private theorem powerCore28_eq : core 28 = powerCore28 := by decide +kernel

private def powerCore27 : Finset ℕ := ⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27] : List ℕ), by decide⟩
private theorem powerCore27_eq : core 27 = powerCore27 := by decide +kernel

private def powerCore40 : Finset ℕ := ⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 32, 33, 34, 35, 36, 38, 39, 40] : List ℕ), by decide⟩
private theorem powerCore40_eq : core 40 = powerCore40 := by decide +kernel

private def cube28Products : Finset ℕ := ⟨([1, 2, 3, 5, 7, 11, 13, 33, 35, 39, 49, 55, 65, 77, 91, 121, 143, 169, 245, 343, 363, 385, 429, 455, 507, 539, 605, 637, 686, 715, 845, 847, 875, 1001, 1029, 1089, 1183, 1225, 1287, 1331, 1375, 1521, 1573, 1617] : List ℕ), by decide⟩

private theorem cube28_card : cube28Products.card = 44 := by decide +kernel

private theorem cube28_checked :
    ∀ m ∈ cube28Products, 0 < m ∧
      0 < (powerRepresentations powerCore26 3 m).card ∧
      (powerRepresentations powerCore28 3 m).card = 1 := by
  decide +kernel

private theorem cube28_unique {n : ℕ} (hn : 26 ≤ n) (hn' : n ≤ 28) :
    ∀ m ∈ cube28Products, 0 < m ∧
      (powerRepresentations (core n) 3 m).card = 1 := by
  intro m hm
  obtain ⟨hmpos, hlo, hhi⟩ := cube28_checked m hm
  rw [← powerCore26_eq] at hlo
  rw [← powerCore28_eq] at hhi
  exact ⟨hmpos, persistent_power_unique hn hn' hlo hhi⟩

private def quartic28Products : Finset ℕ := ⟨([1, 2, 3, 5, 7, 11, 13, 33, 35, 39, 49, 55, 65, 77, 91] : List ℕ), by decide⟩

private theorem quartic28_card : quartic28Products.card = 15 := by decide +kernel

private theorem quartic28_checked :
    ∀ m ∈ quartic28Products, 0 < m ∧
      0 < (powerRepresentations powerCore27 4 m).card ∧
      (powerRepresentations powerCore28 4 m).card = 1 := by
  decide +kernel

private theorem quartic28_unique {n : ℕ} (hn : 27 ≤ n) (hn' : n ≤ 28) :
    ∀ m ∈ quartic28Products, 0 < m ∧
      (powerRepresentations (core n) 4 m).card = 1 := by
  intro m hm
  obtain ⟨hmpos, hlo, hhi⟩ := quartic28_checked m hm
  rw [← powerCore27_eq] at hlo
  rw [← powerCore28_eq] at hhi
  exact ⟨hmpos, persistent_power_unique hn hn' hlo hhi⟩

private def cube40Products : Finset ℕ := ⟨([1, 2, 3, 5, 7, 11, 13, 17, 19, 49, 51, 55, 57, 65, 77, 85, 91, 95, 119, 121, 133, 143, 169, 187, 209, 221, 247, 289, 323, 343, 361, 539, 605, 637, 686, 715, 833, 845, 847, 867, 931, 935, 969, 1001, 1029, 1045, 1083, 1105, 1183, 1235, 1309, 1331, 1375, 1445, 1463, 1547] : List ℕ), by decide⟩

private theorem cube40_card : cube40Products.card = 56 := by decide +kernel

private theorem cube40_checked :
    ∀ m ∈ cube40Products, 0 < m ∧
      0 < (powerRepresentations powerCore40 3 m).card ∧
      (powerRepresentations powerCore40 3 m).card = 1 := by
  decide +kernel

private theorem cube40_unique {n : ℕ} (hn : 40 ≤ n) (hn' : n ≤ 40) :
    ∀ m ∈ cube40Products, 0 < m ∧
      (powerRepresentations (core n) 3 m).card = 1 := by
  intro m hm
  obtain ⟨hmpos, hlo, hhi⟩ := cube40_checked m hm
  rw [← powerCore40_eq] at hlo
  rw [← powerCore40_eq] at hhi
  exact ⟨hmpos, persistent_power_unique hn hn' hlo hhi⟩

/-- Forty-four persistent unique cubic products throughout the three small exceptions. -/
theorem exceptional_cube_products {n : ℕ} (hn : 26 ≤ n) (hn' : n ≤ 28) :
    ∃ T : Finset ℕ, T.card = 44 ∧
      ∀ m ∈ T, 0 < m ∧ (powerRepresentations (core n) 3 m).card = 1 :=
  ⟨cube28Products, cube28_card, cube28_unique hn hn'⟩

/-- Fifteen persistent unique quartic products at the two quartic exceptions. -/
theorem exceptional_quartic_products {n : ℕ} (hn : 27 ≤ n) (hn' : n ≤ 28) :
    ∃ T : Finset ℕ, T.card = 15 ∧
      ∀ m ∈ T, 0 < m ∧ (powerRepresentations (core n) 4 m).card = 1 :=
  ⟨quartic28Products, quartic28_card, quartic28_unique hn hn'⟩

/-- Fifty-six unique cubic products of the core at forty. -/
theorem exceptional_cube_products_forty :
    ∃ T : Finset ℕ, T.card = 56 ∧
      ∀ m ∈ T, 0 < m ∧ (powerRepresentations (core 40) 3 m).card = 1 :=
  ⟨cube40Products, cube40_card, cube40_unique (by decide) (by decide)⟩

end WeightedPilz.Arithmetic

