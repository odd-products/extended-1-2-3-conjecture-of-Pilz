import WeightedPilz.InitialExtension

/-! Quantitative two-row extraction used by the exceptional initial-ten case. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K]

theorem linear_divisor_two_rows_of_card_le_two
    (R D : MvPolynomial σ K) (hR : R ≠ 0) (hD : D ≠ 0)
    (W : Polynomial (MvPolynomial σ K)) (hW : W ≠ 0)
    (hdiv : (Polynomial.C R + Polynomial.C D * Polynomial.X) ∣ W)
    (hrows : W.support.card ≤ 2) : W.support.card = 2 := by
  classical
  have hc0 : W.support.card ≠ 0 := fun hz => hW (Polynomial.card_support_eq_zero.mp hz)
  have hc1 : W.support.card ≠ 1 := by
    intro hone
    obtain ⟨i, U, hU, hrepr⟩ := Polynomial.card_support_eq_one.mp hone
    have hd : (Polynomial.C R + Polynomial.C D * Polynomial.X) ∣ Polynomial.C U :=
      (linear_isRelPrime_X R D hR).pow_right.dvd_of_dvd_mul_right (hrepr ▸ hdiv)
    have hdegree : (Polynomial.C R + Polynomial.C D * Polynomial.X).natDegree = 1 := by
      simpa only [add_comm] using Polynomial.natDegree_linear hD (b := R)
    have hz : (Polynomial.C U : Polynomial (MvPolynomial σ K)) = 0 :=
      Polynomial.eq_zero_of_dvd_of_natDegree_lt hd (by rw [Polynomial.natDegree_C, hdegree]; decide)
    exact hU (Polynomial.C_eq_zero.mp hz)
  omega

private theorem signed_power_product_weight (R M : MvPolynomial σ K) (k : ℕ) :
    weight (-((-R) ^ k * M)) = weight (R ^ k * M) := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_pow]
    simp only [weight, support_neg]
  · rw [hk.neg_pow, neg_mul, neg_neg]

/-- A small two-row multiple has lower-row cost `b` and upper-row cost two.
The preliminary distance `a` makes the top row have at most three terms,
so the common cofactor lies in one outside-variable slice. -/
theorem small_two_row_linear_multiple_weight [DecidableEq σ] (S : Set σ)
    (R D : MvPolynomial σ K) (hR : R ≠ 0)
    (hDvars : (D.vars : Set σ) ⊆ S) (hD : 2 ≤ weight D)
    (hcop : IsRelPrime R D) (a b : ℕ) (hbase : a ≤ distance R)
    (hpower : ∀ (k : ℕ), 0 < k → ∀ M : MvPolynomial σ K,
      M ≠ 0 → (M.vars : Set σ) ⊆ S → b ≤ weight (R ^ k * M))
    (G : MvPolynomial (Option σ) K)
    (hdiv : (Polynomial.C R + Polynomial.C D * Polynomial.X) ∣ optionEquivLeft K σ G)
    (hrows : (optionEquivLeft K σ G).support.card = 2)
    (hw : weight G ≤ a + 3) : b + 2 ≤ weight G := by
  classical
  let W := optionEquivLeft K σ G
  have hD0 : D ≠ 0 := by intro hz; simp [hz, weight] at hD
  obtain ⟨i, j, hij, U, V, hU, hV, hrepr⟩ := Polynomial.card_support_eq_two.mp hrows
  have hcoeffU : W.coeff i = U := by
    rw [show W = Polynomial.C U * Polynomial.X ^ i + Polynomial.C V * Polynomial.X ^ j from hrepr]
    simp [Polynomial.coeff_C_mul_X_pow, hij.ne, hij.ne.symm]
  have hcoeffV : W.coeff j = V := by
    rw [show W = Polynomial.C U * Polynomial.X ^ i + Polynomial.C V * Polynomial.X ^ j from hrepr]
    simp [Polynomial.coeff_C_mul_X_pow, hij.ne, hij.ne.symm]
  have hsum := weight_two_slices G i j hij.ne
  change weight (W.coeff i) + weight (W.coeff j) ≤ _ at hsum
  rw [hcoeffU, hcoeffV] at hsum
  obtain ⟨M, hM, hVM, hUM⟩ := coprime_linear_shifted_two_row_extraction R D U V
    hR hD0 hV hcop i j hij (hrepr ▸ hdiv)
  have hk : 0 < j - i := Nat.sub_pos_of_lt hij
  have hbottom : a ≤ weight U := by
    rw [hUM, signed_power_product_weight]
    obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [hk', pow_succ', mul_assoc]
    exact hbase.trans (distance_le_weight_mul R (R ^ k * M)
      (mul_ne_zero (pow_ne_zero k hR) hM))
  have htop : weight V ≤ 3 := by omega
  obtain ⟨β, M₀, hM₀, hfactor, hM₀vars⟩ := small_power_product_single_base_slice S D M
    hDvars hD hM (j - i) hk (hVM ▸ htop)
  have hstrong : b ≤ weight U := by
    rw [hUM, signed_power_product_weight, hfactor, mul_left_comm, weight_monomial_mul]
    exact hpower (j - i) hk M₀ hM₀ hM₀vars
  have htoplow : 2 ≤ weight V := by
    rw [hVM]
    obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [hk', pow_succ', mul_assoc]
    exact nonmonomial_weight_mul_two D (D ^ k * M) hD
      (mul_ne_zero (pow_ne_zero k hD0) hM)
  omega

/-- A multiple below both quantitative thresholds must have at least three
occupied rows. For initial ten the parameters are `a = 4`, `b = 6`. -/
theorem small_linear_multiple_three_rows [DecidableEq σ] (S : Set σ)
    (R D : MvPolynomial σ K) (hR : R ≠ 0)
    (hDvars : (D.vars : Set σ) ⊆ S) (hD : 2 ≤ weight D)
    (hcop : IsRelPrime R D) (a b : ℕ) (hbase : a ≤ distance R)
    (hpower : ∀ (k : ℕ), 0 < k → ∀ M : MvPolynomial σ K,
      M ≠ 0 → (M.vars : Set σ) ⊆ S → b ≤ weight (R ^ k * M))
    (G : MvPolynomial (Option σ) K) (hG : G ≠ 0)
    (hdiv : (Polynomial.C R + Polynomial.C D * Polynomial.X) ∣ optionEquivLeft K σ G)
    (hw : weight G ≤ a + 3) (hsmall : weight G < b + 2) :
    3 ≤ (optionEquivLeft K σ G).support.card := by
  by_contra hn
  have hG' : optionEquivLeft K σ G ≠ 0 := by
    intro hz
    exact hG ((optionEquivLeft K σ).injective (hz.trans (map_zero _).symm))
  have hD0 : D ≠ 0 := by intro hz; simp [hz, weight] at hD
  have htwo := linear_divisor_two_rows_of_card_le_two R D hR hD0 _ hG' hdiv (by omega)
  have h := small_two_row_linear_multiple_weight S R D hR hDvars hD hcop a b hbase hpower G hdiv htwo hw
  omega

end WeightedPilz
