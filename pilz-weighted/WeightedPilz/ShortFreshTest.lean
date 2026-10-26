import WeightedPilz.ShortFreshRows
import Mathlib.Algebra.Ring.Parity

/-! The short fresh-row test, with arbitrary base-only coefficient polynomials. -/
noncomputable section
namespace WeightedPilz.FreshData
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

def occupiedPositiveRows (t : Finset ℕ) (A : ℕ → MvPolynomial σ K) : Finset ℕ :=
  by classical exact t.filter (fun j => 0 < j ∧ A j ≠ 0)

theorem sum_split_occupiedPositiveRows {R : Type*} [AddCommMonoid R]
    (t : Finset ℕ) (A : ℕ → MvPolynomial σ K) (hzero : 0 ∈ t)
    (f : ℕ → R) (hf : ∀ j, A j = 0 → f j = 0) :
    (∑ j ∈ t, f j) = f 0 + ∑ j ∈ occupiedPositiveRows t A, f j := by
  classical
  have hsub : occupiedPositiveRows t A ⊆ t.erase 0 := by
    intro j hj
    obtain ⟨hjt, hjpos, _⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_erase.mpr ⟨by omega, hjt⟩
  have heq : (∑ j ∈ occupiedPositiveRows t A, f j) = ∑ j ∈ t.erase 0, f j := by
    apply Finset.sum_subset hsub
    intro j hj hnot
    apply hf
    by_contra hAj
    apply hnot
    exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hj).2,
      by have := (Finset.mem_erase.mp hj).1; omega, hAj⟩
  rw [heq, add_comm]
  exact (Finset.sum_erase_add t f hzero).symm

theorem aggregate_positive_data (S : FreshData σ K) (t : Finset ℕ)
    (A : ℕ → MvPolynomial σ K) (hbase : ∀ j ∈ t, S.BaseOnly (A j))
    (hdiv : S.F ∣ ∑ j ∈ t, S.freshSum ^ j * A j)
    (hzero : 0 ∈ t) (hA0 : A 0 ≠ 0) :
    (occupiedPositiveRows t A).Nonempty ∧
    weight (∑ j ∈ t, S.freshSum ^ j * A j) = weight (A 0) +
      ∑ j ∈ occupiedPositiveRows t A, weight (S.freshSum ^ j * A j) ∧
    A 0 + (∑ j ∈ occupiedPositiveRows t A, (-S.C) ^ j * A j) = 0 := by
  classical
  have hrel := S.aggregate_relation_of_dvd t A hbase hdiv
  rw [sum_split_occupiedPositiveRows t A hzero _ (fun j h => by simp [h]),
    pow_zero, one_mul] at hrel
  refine ⟨?_, ?_, hrel⟩
  · by_contra hn
    have he : occupiedPositiveRows t A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    exact hA0 (by simpa [he] using hrel)
  · rw [S.base_rows_weight t A hbase,
      sum_split_occupiedPositiveRows t A hzero _ (fun j h => by simp [h, weight]),
      pow_zero, one_mul]

theorem weight_mul_of_weight_one (P Q : MvPolynomial σ K) (hQ : weight Q = 1) :
    weight (P * Q) = weight P := by
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hQ
  have hc : coeff d Q ≠ 0 := mem_support_iff.mp (by rw [hd]; simp)
  have hmono : Q = monomial d (coeff d Q) := (Finsupp.support_eq_singleton.mp hd).2
  rw [hmono, mul_comm]
  exact weight_scalar_monomial_mul d hc P

theorem weight_negative_power (P : MvPolynomial σ K) (j : ℕ) :
    weight ((-P) ^ j) = weight (P ^ j) := by
  rcases Nat.even_or_odd j with h | h
  · rw [h.neg_pow]
  · rw [h.neg_pow]
    simp only [weight, support_neg]

theorem negative_distinguished_power (P : MvPolynomial σ K) (p e : ℕ) [ExpChar K p] :
    (-P) ^ p ^ e = -(P ^ p ^ e) := by
  letI : ExpChar (MvPolynomial σ K) p :=
    expChar_of_injective_ringHom (MvPolynomial.C_injective (σ := σ) (R := K)) p
  rw [neg_pow, neg_one_pow_expChar_pow, neg_one_mul]

/-- The three tests from the manuscript imply the full core-plus-fresh distance. -/
theorem short_fresh_test (S : FreshData σ K) (p κ : ℕ) [ExpChar K p]
    (hr : 2 ≤ S.vars.card) (hκ : κ ≤ distance S.C)
    (hstart : weight S.C + S.vars.card ≤ S.vars.card * (κ + 1))
    (hbudget : weight S.C + S.vars.card - 1 - κ ≤ 2 * S.vars.card)
    (hpower : ∀ j, 0 < j → (∀ e : ℕ, j ≠ p ^ e) →
      weight (S.freshSum ^ j) ≤ weight S.C + S.vars.card - 1 - κ →
      weight S.C + S.vars.card ≤ weight (S.C ^ j) + weight (S.freshSum ^ j))
    (hbinomial : ∀ e (H : MvPolynomial σ K), weight H = 2 →
      weight S.C + S.vars.card - 2 * S.vars.card ≤ weight (S.C ^ p ^ e * H))
    (htwo : ∀ e f (M L : MvPolynomial σ K), p ^ e ≠ p ^ f →
      weight M = 1 → weight L = 1 →
      M * S.C ^ p ^ e + L * S.C ^ p ^ f ≠ 0 →
      weight S.C + S.vars.card - 2 * S.vars.card ≤
        weight (M * S.C ^ p ^ e + L * S.C ^ p ^ f)) :
    weight S.C + S.vars.card ≤ distance S.F := by
  classical
  by_contra hn
  have hdist : distance S.F < weight S.C + S.vars.card := Nat.lt_of_not_ge hn
  obtain ⟨t, A, hbase, hG, hdiv, hweight⟩ := S.exists_scalar_minimum
  have hw : weight (∑ j ∈ t, S.freshSum ^ j * A j) < weight S.C + S.vars.card := by
    rwa [hweight]
  obtain ⟨hzero, hA0, hκA⟩ := S.aggregate_lowest_row_zero t A hbase hG hdiv κ
    (weight S.C + S.vars.card) hκ hstart hw
  obtain ⟨ht, htotal, hrel⟩ := S.aggregate_positive_data t A hbase hdiv hzero hA0
  let u := occupiedPositiveRows t A
  have huj : ∀ j ∈ u, 0 < j := fun j hj => (Finset.mem_filter.mp hj).2.1
  have huA : ∀ j ∈ u, A j ≠ 0 := fun j hj => (Finset.mem_filter.mp hj).2.2
  have hubase : ∀ j ∈ u, S.BaseOnly (A j) :=
    fun j hj => hbase j (Finset.mem_filter.mp hj).1
  change weight (∑ j ∈ t, S.freshSum ^ j * A j) =
    weight (A 0) + ∑ j ∈ u, weight (S.freshSum ^ j * A j) at htotal
  have hposbudget : (∑ j ∈ u, weight (S.freshSum ^ j * A j)) ≤
      weight S.C + S.vars.card - 1 - κ := by omega
  have hshort := S.short_positive_rows p u A hr ht huj huA hubase (hposbudget.trans hbudget)
  change A 0 + (∑ j ∈ u, (-S.C) ^ j * A j) = 0 at hrel
  rcases hshort with ⟨j, hu, hAj⟩ | ⟨j, e, hu, hAj, he⟩ | ⟨i, j, e, f, hij, hu, hAi, hAj, he, hf⟩
  · have hj : j ∈ u := by rw [hu]; simp
    rw [hu, Finset.sum_singleton] at hrel htotal hposbudget
    have hAeq : A 0 = -((-S.C) ^ j * A j) := eq_neg_of_add_eq_zero_left hrel
    have hAweight : weight (A 0) = weight (S.C ^ j) := by
      rw [hAeq]
      simp only [weight, support_neg]
      change weight ((-S.C) ^ j * A j) = weight (S.C ^ j)
      rw [weight_mul_of_weight_one _ _ hAj, weight_negative_power]
    rw [S.weight_freshSum_pow_mul_baseOnly j (A j) (hubase j hj), hAj, mul_one] at htotal hposbudget
    rw [hAweight] at htotal
    by_cases hdistj : ∃ e, j = p ^ e
    · obtain ⟨e, rfl⟩ := hdistj
      rw [weight_pow_expChar p e S.C, S.fresh_distinguished_degree_cost p e] at htotal
      omega
    · have hnd : ∀ e, j ≠ p ^ e := by simpa only [not_exists] using hdistj
      have := hpower j (huj j hj) hnd hposbudget
      omega
  · have hj : j ∈ u := by rw [hu]; simp
    rw [hu, Finset.sum_singleton, he, negative_distinguished_power,
      neg_mul] at hrel
    have hAeq : A 0 = S.C ^ p ^ e * A j := eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, he] using hrel)
    have hbound := hbinomial e (A j) hAj
    rw [← hAeq] at hbound
    rw [hu, Finset.sum_singleton, S.weight_freshSum_pow_mul_baseOnly j (A j) (hubase j hj),
      hAj, he, S.fresh_distinguished_degree_cost] at htotal
    omega
  · have hi : i ∈ u := by rw [hu]; simp
    have hj : j ∈ u := by rw [hu]; simp
    rw [hu, Finset.sum_pair hij, he, hf, negative_distinguished_power,
      negative_distinguished_power, neg_mul, neg_mul] at hrel
    have hAeq : A 0 = A i * S.C ^ p ^ e + A j * S.C ^ p ^ f := by
      rw [he, hf]
      linear_combination hrel
    have hbound := htwo e f (A i) (A j) (by simpa only [← he, ← hf] using hij) hAi hAj
      (by simpa only [← hAeq] using hA0)
    rw [← hAeq] at hbound
    rw [hu, Finset.sum_pair hij, S.weight_freshSum_pow_mul_baseOnly i (A i) (hubase i hi),
      S.weight_freshSum_pow_mul_baseOnly j (A j) (hubase j hj), hAi, hAj,
      mul_one, mul_one, he, hf, S.fresh_distinguished_degree_cost,
      S.fresh_distinguished_degree_cost] at htotal
    omega

end WeightedPilz.FreshData
