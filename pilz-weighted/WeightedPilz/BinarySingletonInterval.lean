import WeightedPilz.BinarySingletonClasses
import WeightedPilz.ParityCore

/-! The singleton parity count excludes every single-class binary input of
at least three terms in the middle range. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]

theorem exists_single_residue_of_card_le_one (q : ℕ) (D : Poly K) (hD : D ≠ 0)
    (hclasses : (residueIndices q D).card ≤ 1) :
    ∃β, D = residuePart q D β := by
  classical
  obtain ⟨α, hα⟩ := exists_nonzero_residuePart q D hD
  have hmem := mem_residueIndices_of_part_ne_zero q D hα
  have hpos := Finset.card_pos.mpr ⟨α, hmem⟩
  obtain ⟨β, hβ⟩ := Finset.card_eq_one.mp (show (residueIndices q D).card = 1 by omega)
  refine ⟨β, ?_⟩
  have h := sum_residueParts q D
  change (∑γ∈residueIndices q D, residuePart q D γ) = D at h
  rw [hβ, Finset.sum_singleton] at h
  exact h.symm

private theorem singleton_parity_sqrt {n s : ℕ}
    (hs : n / 4 < s) (hsn : s ≤ n) : Nat.sqrt (n / s) = 1 := by
  have hspos : 0 < s := by omega
  apply (Nat.eq_sqrt.mpr ?_).symm
  constructor
  · change 1 ≤ n / s
    exact Nat.div_pos hsn hspos
  · have h4 : n < s * 4 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mp hs
    apply (Nat.div_lt_iff_lt_mul hspos).mpr
    simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.mul_comm] using h4

theorem intervalFreshData_single_class_impossible (n : ℕ) (hn25 : 25 ≤ n) (hn66 : n ≤ 66)
    (c : ℕ → K) (hc : NonzeroWeights n c) (hr : (intervalFreshPrimes n).Nonempty)
    (W : (intervalFreshData n c (by omega) hc hr).ResidueCapacityWitness 2 n)
    (hu : 3 ≤ weight (W.A 1)) (hclasses : (residueIndices 2 (W.A 1)).card ≤ 1) : False := by
  classical
  let S := intervalFreshData n c (by omega) hc hr
  obtain ⟨β, hβ⟩ := exists_single_residue_of_card_le_one 2 (W.A 1)
    (W.binary_input_ne_zero S) hclasses
  let Q := Arithmetic.singletonParityNumbers n
  let T := Q.image Nat.factorization
  have hQ : ∀s∈Q, n / 4 < s ∧ s ≤ n ∧ Squarefree s := by
    intro s hs
    exact (Arithmetic.mem_singletonParityNumbers n s).mp hs
  have hT : ∀α∈T, residueExponent 2 α = α := by
    intro α hα
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hα
    exact residue_factorization_squarefree (hQ s hs).2.2
  have hsupport : S.F.support = (interval n c).support := by
    change (intervalCore n c + ∑ p∈intervalFreshPrimes n, X p).support = _
    rw [← rescale_interval_eq_core_add_fresh n c hc, support_rescale]
  have hsingle : ∀α∈T, residueWeight 2 S.F α = 1 := by
    intro α hα
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hα
    have heq : residueWeight 2 S.F s.factorization = residueWeight 2 (interval n c) s.factorization := by
      simp only [residueWeight, weight, support_residuePart, hsupport]
    rw [heq, interval_parity_class_weight n s c hc (hQ s hs).2.2]
    exact singleton_parity_sqrt (hQ s hs).1 (hQ s hs).2.1
  have hinj : Set.InjOn Nat.factorization (Q : Set ℕ) := by
    intro s hs t ht heq
    exact Nat.factorization_inj (hQ s hs).2.2.ne_zero (hQ t ht).2.2.ne_zero heq
  have hcard : T.card = Q.card := Finset.card_image_of_injOn hinj
  have hbound := W.singleton_class_lower S (Finset.card_pos.mpr hr) β hβ T hT hsingle
  rw [hcard] at hbound
  have hcount := Arithmetic.singletonParity_budget hn25 hn66
  change n ≤ 3 * Q.card at hcount
  have hshort := W.short
  nlinarith

end WeightedPilz
