import WeightedPilz.Completion
import WeightedPilz.RowWeights
import WeightedPilz.ShortFreshTest

/-! The one-fresh-variable short-multiple test used for the tenth interval. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

private theorem signed_power_product_weight (A B : MvPolynomial σ K) (j : ℕ) :
    weight (B * (-A) ^ j) = weight (A ^ j * B) := by
  rcases Nat.even_or_odd j with h | h
  · rw [h.neg_pow, mul_comm]
  · rw [h.neg_pow, mul_neg]
    simp only [weight, support_neg, mul_comm]

/-- A seven-term core minimum together with the three power tests rules out
all completion multiples of weight at most nine. -/
theorem freshCompletion_distance_ten (A : MvPolynomial σ K)
    (hdist : 7 ≤ distance A)
    (hpower : ∀ j : ℕ, 0 < j → 9 ≤ weight (A ^ j))
    (hbinomial : ∀ j : ℕ, 0 < j → ∀ B : MvPolynomial σ K,
      weight B = 2 → 8 ≤ weight (A ^ j * B))
    (htwo : ∀ i j : ℕ, 0 < i → i < j → ∀ M N : MvPolynomial σ K,
      weight M = 1 → weight N = 1 → M * A ^ i + N * A ^ j ≠ 0 →
      8 ≤ weight (M * A ^ i + N * A ^ j)) :
    10 ≤ distance (freshCompletion A) := by
  classical
  have hA : A ≠ 0 := by intro hz; simp [hz] at hdist
  apply (le_distance_iff _ _).mpr
  intro H hH
  by_contra hnot
  have hsmall : weight (freshCompletion A * H) < 10 := Nat.lt_of_not_ge hnot
  obtain ⟨k, F, _, hweight, hF, hdiv, hzero⟩ := freshCompletion_normalize A hA
    (freshCompletion A * H) (mul_ne_zero (freshCompletion_ne_zero A) hH) (dvd_mul_right _ _)
  have hwF : weight F < 10 := by omega
  let W := optionEquivLeft K σ F
  let t := W.support.erase 0
  have hmem : 0 ∈ W.support := Polynomial.mem_support_iff.mpr hzero
  have hbase : 7 ≤ weight (W.coeff 0) := by
    obtain ⟨Q, hQ⟩ := freshCompletion_constant_dvd A F hdiv
    have hQ0 : Q ≠ 0 := by intro hz; rw [hQ, hz, mul_zero] at hzero; exact hzero rfl
    exact hdist.trans (by simpa only [W, hQ] using distance_le_weight_mul A Q hQ0)
  have hsum : weight (W.coeff 0) + (∑ j ∈ t, weight (W.coeff j)) ≤ weight F := by
    have h := weight_option_slices_le F W.support
    change (∑ j ∈ W.support, weight (W.coeff j)) ≤ weight F at h
    rw [← Finset.sum_erase_add W.support (fun j => weight (W.coeff j)) hmem] at h
    simpa only [t, add_comm] using h
  have hbudget : (∑ j ∈ t, weight (W.coeff j)) ≤ 2 := by omega
  have hrel : W.coeff 0 + (∑ j ∈ t, W.coeff j * (-A) ^ j) = 0 := by
    have h := (freshCompletion_dvd_iff A F).mp hdiv
    change W.eval (-A) = 0 at h
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def,
      ← Finset.sum_erase_add W.support (fun j => W.coeff j * (-A) ^ j) hmem] at h
    simpa only [t, pow_zero, mul_one, add_comm] using h
  have ht : t.Nonempty := by
    by_contra hn
    have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he, Finset.sum_empty, add_zero] at hrel
    exact hzero hrel
  have hjpos (j : ℕ) (hj : j ∈ t) : 0 < j := by
    have h := (Finset.mem_erase.mp hj).1
    omega
  have hjweight (j : ℕ) (hj : j ∈ t) : 1 ≤ weight (W.coeff j) := by
    have hne := Polynomial.mem_support_iff.mp (Finset.mem_erase.mp hj).2
    exact Nat.succ_le_iff.mpr (by simpa [weight, Finset.card_pos, support_nonempty] using hne)
  have hcard : t.card ≤ 2 := by
    calc
      t.card = ∑ _j ∈ t, 1 := by simp
      _ ≤ ∑ j ∈ t, weight (W.coeff j) := Finset.sum_le_sum hjweight
      _ ≤ 2 := hbudget
  by_cases hone : t.card = 1
  · obtain ⟨j, htj⟩ := Finset.card_eq_one.mp hone
    have hj : j ∈ t := by rw [htj]; simp
    have hjp := hjpos j hj
    have hjw := hjweight j hj
    rw [htj, Finset.sum_singleton] at hsum hbudget hrel
    have hzeroeq : W.coeff 0 = -(W.coeff j * (-A) ^ j) := eq_neg_of_add_eq_zero_left hrel
    have hzeroWeight : weight (W.coeff 0) = weight (A ^ j * W.coeff j) := by
      rw [hzeroeq]
      simpa only [weight, support_neg] using signed_power_product_weight A (W.coeff j) j
    by_cases hwone : weight (W.coeff j) = 1
    · rw [FreshData.weight_mul_of_weight_one _ _ hwone] at hzeroWeight
      have hb := hpower j hjp
      omega
    · have hwtwo : weight (W.coeff j) = 2 := by omega
      have hb := hbinomial j hjp (W.coeff j) hwtwo
      omega
  · have htwoCard : t.card = 2 := by have := ht.card_pos; omega
    obtain ⟨i, j, hij, htij⟩ := Finset.card_eq_two.mp htwoCard
    have hi : i ∈ t := by rw [htij]; simp
    have hj : j ∈ t := by rw [htij]; simp
    have hip := hjpos i hi
    have hjp := hjpos j hj
    have hiw := hjweight i hi
    have hjw := hjweight j hj
    rw [htij, Finset.sum_pair hij] at hsum hbudget hrel
    have hi1 : weight (W.coeff i) = 1 := by omega
    have hj1 : weight (W.coeff j) = 1 := by omega
    let signed (m : ℕ) : MvPolynomial σ K := C ((-1 : K) ^ m) * W.coeff m
    have hsignWeight (m : ℕ) : weight (signed m) = weight (W.coeff m) :=
      weight_scalar_monomial_mul 0 (pow_ne_zero m (neg_ne_zero.mpr one_ne_zero)) _
    have hsign (m : ℕ) : signed m * A ^ m = W.coeff m * (-A) ^ m := by
      dsimp [signed]
      rw [map_pow, map_neg, map_one, neg_pow]
      ring
    have hzeroeq : W.coeff 0 = -(signed i * A ^ i + signed j * A ^ j) := by
      rw [hsign, hsign]
      exact eq_neg_of_add_eq_zero_left hrel
    have hne : signed i * A ^ i + signed j * A ^ j ≠ 0 := by
      intro hz
      rw [hz, neg_zero] at hzeroeq
      exact hzero hzeroeq
    have hb : 8 ≤ weight (signed i * A ^ i + signed j * A ^ j) := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact htwo i j hip h _ _ (by rwa [hsignWeight]) (by rwa [hsignWeight]) hne
      · simpa only [add_comm] using htwo j i hjp h (signed j) (signed i)
          (by rwa [hsignWeight]) (by rwa [hsignWeight]) (by simpa only [add_comm] using hne)
    have hzeroWeight : weight (W.coeff 0) = weight (signed i * A ^ i + signed j * A ^ j) := by
      rw [hzeroeq]
      simp only [weight, support_neg]
    omega

end WeightedPilz
