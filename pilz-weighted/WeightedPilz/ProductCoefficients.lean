import WeightedPilz.Basic
import WeightedPilz.Support

/-! Actual uniquely represented integer products give nonzero coefficients in
the square of a weighted core in characteristic different from two. -/

noncomputable section
namespace WeightedPilz

open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K]

theorem polynomialOf_mul_eq_pair_sum (A B : Finset ℕ) (c d : ℕ → K)
    (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b) :
    polynomialOf A c * polynomialOf B d =
      ∑ p ∈ A ×ˢ B, monomial (p.1 * p.2).factorization (c p.1 * d p.2) := by
  classical
  simp only [polynomialOf, Finset.sum_mul, Finset.mul_sum, Finset.sum_product,
    MvPolynomial.monomial_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [Nat.factorization_mul (ne_of_gt (hA a ha)) (ne_of_gt (hB b hb))]

/-- The coefficient at `X(m)` is the sum over actual ordered integer products. -/
theorem coeff_polynomialOf_mul (A B : Finset ℕ) (c d : ℕ → K)
    (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b) {m : ℕ} (hm : 0 < m) :
    coeff m.factorization (polynomialOf A c * polynomialOf B d) =
      ∑ p ∈ (A ×ˢ B).filter (fun p => p.1 * p.2 = m), c p.1 * d p.2 := by
  classical
  rw [polynomialOf_mul_eq_pair_sum A B c d hA hB, coeff_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpA := (Finset.mem_product.mp hp).1
  have hpB := (Finset.mem_product.mp hp).2
  have hprod : 0 < p.1 * p.2 := Nat.mul_pos (hA _ hpA) (hB _ hpB)
  have heq : (p.1 * p.2).factorization = m.factorization ↔ p.1 * p.2 = m :=
    ⟨Nat.factorization_inj (ne_of_gt hprod) (ne_of_gt hm), congrArg Nat.factorization⟩
  simp only [coeff_monomial, heq]

/-- Exactly one unordered representation gives exactly one diagonal ordered
pair or the two transposed off-diagonal pairs. -/
theorem ordered_pairs_of_unique_representation (A : Finset ℕ) (m : ℕ)
    (hrep : ((A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ p.1 * p.2 = m)).card = 1) :
    ∃ a ∈ A, ∃ b ∈ A, a ≤ b ∧ a * b = m ∧
      (A ×ˢ A).filter (fun p => p.1 * p.2 = m) = {(a, b), (b, a)} := by
  classical
  obtain ⟨⟨a, b⟩, hab⟩ := Finset.card_eq_one.mp hrep
  have hmem : (a, b) ∈ (A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ p.1 * p.2 = m) := by
    rw [hab]
    exact Finset.mem_singleton_self _
  obtain ⟨⟨ha, hb⟩, hle, hprod⟩ :=
    (by simpa only [Finset.mem_filter, Finset.mem_product] using hmem)
  refine ⟨a, ha, b, hb, hle, hprod, ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨⟨hpA, hpB⟩, hpProd⟩ :=
      (by simpa only [Finset.mem_filter, Finset.mem_product] using hp)
    rcases le_total p.1 p.2 with hpLe | hpGe
    · have hpin : p ∈ (A ×ˢ A).filter (fun q => q.1 ≤ q.2 ∧ q.1 * q.2 = m) :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpA, hpB⟩, hpLe, hpProd⟩
      rw [hab] at hpin
      exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hpin))
    · have hpin : (p.2, p.1) ∈
          (A ×ˢ A).filter (fun q => q.1 ≤ q.2 ∧ q.1 * q.2 = m) :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpB, hpA⟩,
          hpGe, by simpa only [Nat.mul_comm] using hpProd⟩
      rw [hab] at hpin
      have hpEq := congrArg Prod.swap (Finset.mem_singleton.mp hpin)
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by simpa using hpEq)))
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hprod⟩
    · obtain rfl := Finset.mem_singleton.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩,
        by simpa only [Nat.mul_comm] using hprod⟩

/-- In odd characteristic, a unique unordered product has coefficient `c_a²`
or `2*c_a*c_b`, so cannot cancel for any nonzero choice of weights. -/
theorem coeff_square_ne_zero_of_unique_product (A : Finset ℕ) (c : ℕ → K)
    (hA : ∀ a ∈ A, 0 < a) (hc : ∀ a ∈ A, c a ≠ 0) (h2 : (2 : K) ≠ 0)
    {m : ℕ}
    (hrep : ((A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ p.1 * p.2 = m)).card = 1) :
    coeff m.factorization (polynomialOf A c ^ 2) ≠ 0 := by
  classical
  obtain ⟨a, ha, b, hb, hab, hprod, hpairs⟩ :=
    ordered_pairs_of_unique_representation A m hrep
  have hm : 0 < m := hprod ▸ Nat.mul_pos (hA a ha) (hA b hb)
  rw [pow_two, coeff_polynomialOf_mul A A c c hA hA hm, hpairs]
  by_cases heq : a = b
  · subst b
    simpa only [Finset.pair_eq_singleton, Finset.sum_singleton] using
      mul_ne_zero (hc a ha) (hc a ha)
  · have hpair : (a, b) ≠ (b, a) := fun h => heq (congrArg Prod.fst h)
    rw [Finset.sum_pair hpair]
    change c a * c b + c b * c a ≠ 0
    rw [mul_comm (c b) (c a), ← two_mul]
    exact mul_ne_zero h2 (mul_ne_zero (hc a ha) (hc b hb))


end WeightedPilz

