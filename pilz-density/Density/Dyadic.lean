import Density.CutLimit
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! The elementary powers-of-two case of the density gap. -/

noncomputable section
namespace PilzDensity

private def powers (E : Finset ℕ) : Finset ℕ := E.image (fun k => 2 ^ k)

private theorem powers_positive (E : Finset ℕ) :
    ∀ a ∈ powers E, 0 < a := by
  intro a ha
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
  positivity

private theorem powers_card (E : Finset ℕ) : (powers E).card = E.card :=
  Finset.card_image_of_injective _ (Nat.pow_right_injective (by omega))

private theorem mul_shift_pow {k j : ℕ} (h : k ≤ j) :
    2 ^ k * 2 ^ (j - k) = 2 ^ j := by
  rw [← pow_add, Nat.add_sub_of_le h]

section Abstract

variable
  (hD : ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → HasDensity A (density A))
  (hScale : ∀ (A : Finset ℕ) (c : ℕ), 0 < c →
    density (A.image (c * ·)) = density A)
  (hPair : ∀ (a q : ℕ), 0 < a → 4 ≤ q →
    (3 : ℝ) / 2 ≤ density {a, a * q})
  (hTriple : ∀ (u v : ℕ), 2 ≤ u → 2 ≤ v →
    (3 : ℝ) / 2 ≤ density {1, u, u * v})

include hD hScale in
private theorem powers_erase_min_le (E : Finset ℕ) (hne : E.Nonempty) :
    density (powers (E.erase (E.min' hne))) ≤ density (powers E) := by
  classical
  let k := E.min' hne
  let C := (E.erase k).image (fun j => 2 ^ (j - k))
  have hk : k ∈ E := E.min'_mem hne
  have hkj : ∀ j ∈ E, k ≤ j := fun j hj => E.min'_le j hj
  have hcpos : ∀ c ∈ C, 0 < c := by
    intro c hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
    positivity
  have hcdvd : ∀ c ∈ C, 2 ∣ c := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    have hjk : k < j := by
      have hmem := Finset.mem_of_mem_erase hj
      have hne' := (Finset.mem_erase.mp hj).1
      have := hkj j hmem
      omega
    exact dvd_pow_self 2 (by omega : j - k ≠ 0)
  have hdis : Disjoint ({1} : Finset ℕ) C := by
    simp only [Finset.disjoint_singleton_left]
    intro hc
    have := hcdvd 1 hc
    norm_num at this
  have hpos : ∀ a ∈ ({1} : Finset ℕ) ∪ C, 0 < a := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · simp only [Finset.mem_singleton] at ha
      subst a
      omega
    · exact hcpos a ha
  have hcut := HasDensity.exact_cut (hD _ hpos)
    (hD {1} (by simp)) (hD C hcpos) 2 (by omega) hdis
    (by simp) hcdvd
  norm_num at hcut
  have himC : C.image (2 ^ k * ·) = powers (E.erase k) := by
    simp only [C, Finset.image_image, powers]
    apply Finset.image_congr
    intro j hj
    exact mul_shift_pow (hkj j (Finset.mem_of_mem_erase hj))
  have himA : (({1} : Finset ℕ) ∪ C).image (2 ^ k * ·) = powers E := by
    rw [Finset.image_union, himC]
    simp only [Finset.image_singleton, mul_one]
    change {2 ^ k} ∪ (E.erase k).image (fun j => 2 ^ j) = E.image (fun j => 2 ^ j)
    rw [Finset.singleton_union, ← Finset.image_insert, Finset.insert_erase hk]
  rw [← hScale C (2 ^ k) (by positivity), himC] at hcut
  simp only [Finset.singleton_union] at himA
  rw [← hScale (insert 1 C) (2 ^ k) (by positivity), himA] at hcut
  exact hcut

include hScale hTriple in
private theorem powers_triple_sorted (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    (3 : ℝ) / 2 ≤ density (powers {a, b, c}) := by
  let u := 2 ^ (b - a)
  let v := 2 ^ (c - b)
  have hu : 2 ≤ u := by
    change 2 ^ 1 ≤ 2 ^ (b - a)
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hv : 2 ≤ v := by
    change 2 ^ 1 ≤ 2 ^ (c - b)
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have heq : ({1, u, u * v} : Finset ℕ).image (2 ^ a * ·) = powers {a, b, c} := by
    have hu' : 2 ^ a * u = 2 ^ b := mul_shift_pow (by omega)
    have hv' : 2 ^ b * v = 2 ^ c := mul_shift_pow (by omega)
    simp only [Finset.image_insert, Finset.image_singleton, powers, mul_one]
    rw [← mul_assoc, hu', hv']
  rw [← heq, hScale _ _ (by positivity)]
  exact hTriple u v hu hv

include hScale hTriple in
private theorem powers_triple (E : Finset ℕ) (hcard : E.card = 3) :
    (3 : ℝ) / 2 ≤ density (powers E) := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have hord : (a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨
      (b < a ∧ a < c) ∨ (b < c ∧ c < a) ∨
      (c < a ∧ a < b) ∨ (c < b ∧ b < a) := by omega
  rcases hord with h | h | h | h | h | h
  · exact powers_triple_sorted hScale hTriple a b c h.1 h.2
  · have hs : ({a, b, c} : Finset ℕ) = {a, c, b} := by
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hs]
    exact powers_triple_sorted hScale hTriple a c b h.1 h.2
  · have hs : ({a, b, c} : Finset ℕ) = {b, a, c} := by
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hs]
    exact powers_triple_sorted hScale hTriple b a c h.1 h.2
  · have hs : ({a, b, c} : Finset ℕ) = {b, c, a} := by
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hs]
    exact powers_triple_sorted hScale hTriple b c a h.1 h.2
  · have hs : ({a, b, c} : Finset ℕ) = {c, a, b} := by
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hs]
    exact powers_triple_sorted hScale hTriple c a b h.1 h.2
  · have hs : ({a, b, c} : Finset ℕ) = {c, b, a} := by
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hs]
    exact powers_triple_sorted hScale hTriple c b a h.1 h.2

include hD hScale hTriple in
private theorem powers_large (E : Finset ℕ) (hcard : 3 ≤ E.card) :
    (3 : ℝ) / 2 ≤ density (powers E) := by
  classical
  induction hn : E.card using Nat.strong_induction_on generalizing E with
  | h n ih =>
    by_cases heq : E.card = 3
    · exact powers_triple hScale hTriple E heq
    have hne : E.Nonempty := Finset.card_pos.mp (by omega)
    have hk := E.min'_mem hne
    have hcl : (E.erase (E.min' hne)).card = E.card - 1 := Finset.card_erase_of_mem hk
    have hsmall := ih (E.erase (E.min' hne)).card (by omega)
      (E.erase (E.min' hne)) (by omega) rfl
    exact hsmall.trans (powers_erase_min_le hD hScale E hne)

include hPair in
private theorem powers_pair_sorted (a b : ℕ) (hab : a < b)
    (hn : ¬ Exceptional (powers {a, b})) :
    (3 : ℝ) / 2 ≤ density (powers {a, b}) := by
  have hgap : 2 ≤ b - a := by
    by_contra h
    have hb : b = a + 1 := by omega
    apply hn
    refine ⟨2 ^ a, by positivity, Or.inr ?_⟩
    simp [powers, hb, pow_succ, Nat.mul_comm]
  have hq : 4 ≤ 2 ^ (b - a) := by
    change 2 ^ 2 ≤ 2 ^ (b - a)
    exact Nat.pow_le_pow_right (by omega) hgap
  have hp := hPair (2 ^ a) (2 ^ (b - a)) (by positivity) hq
  simpa only [powers, Finset.image_insert, Finset.image_singleton,
    mul_shift_pow (Nat.le_of_lt hab)] using hp

include hD hScale hPair hTriple in
/-- The dyadic argument, separated from the proofs of its basic counting inputs. -/
theorem dyadic_lower_bound_of (A : Finset ℕ) (hne : A.Nonempty)
    (hpow : ∀ a ∈ A, ∃ k : ℕ, a = 2 ^ k) (hn : ¬ Exceptional A) :
    (3 : ℝ) / 2 ≤ density A := by
  classical
  let E := A.preimage (fun k : ℕ => 2 ^ k)
    (Nat.pow_right_injective (by omega)).injOn
  have heq : powers E = A := by
    ext a
    simp only [powers, E, Finset.mem_image, Finset.mem_preimage]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro ha
      obtain ⟨k, rfl⟩ := hpow a ha
      exact ⟨k, ha, rfl⟩
  rw [← heq] at hn ⊢
  have hE : E.Nonempty := by
    have : (powers E).Nonempty := heq.symm ▸ hne
    exact Finset.image_nonempty.mp this
  by_cases hlarge : 3 ≤ E.card
  · exact powers_large hD hScale hTriple E hlarge
  have hpos := Finset.card_pos.mpr hE
  by_cases hone : E.card = 1
  · obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hone
    rw [hk] at hn ⊢
    exact False.elim (hn ⟨2 ^ k, by positivity, Or.inl (by simp [powers])⟩)
  have htwo : E.card = 2 := by omega
  obtain ⟨a, b, hab, habE⟩ := Finset.card_eq_two.mp htwo
  rw [habE] at hn ⊢
  rcases lt_or_gt_of_ne hab with h | h
  · exact powers_pair_sorted hPair a b h hn
  · have hs : ({a, b} : Finset ℕ) = {b, a} := Finset.pair_comm a b
    rw [hs] at hn ⊢
    exact powers_pair_sorted hPair b a h hn

end Abstract
end PilzDensity
