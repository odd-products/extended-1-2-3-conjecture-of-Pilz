import WeightedPilz.LinearTwoPowers

/-! Arbitrary monomial translations in the two-power exclusion. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K]

theorem monomial_split_none (a : Option σ →₀ ℕ) (u : K) :
    monomial a u = monomial (Finsupp.single none (a none)) 1 * rename some (monomial a.some u) := by
  apply (optionEquivLeft K σ).injective
  simp [optionEquivLeft_monomial, optionEquivLeft_rename_some,
    Finsupp.some_single_none, Polynomial.monomial_mul_C]

theorem optionEquiv_monomial_mul_pow (R D : MvPolynomial σ K)
    (a : Option σ →₀ ℕ) (u : K) (n : ℕ) :
    optionEquivLeft K σ (monomial a u * linearExtension R D ^ n) =
      (Polynomial.C (monomial a.some u) *
        (Polynomial.C R + Polynomial.C D * Polynomial.X) ^ n) * Polynomial.X ^ (a none) := by
  rw [map_mul, map_pow, optionEquiv_linearExtension, optionEquivLeft_monomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem linearExtension_two_monomial_powers_eight [DecidableEq σ]
    (R D : MvPolynomial σ K) (hR : R ≠ 0) (hD : D ≠ 0)
    (hRd : 4 ≤ distance R) (hDd : 2 ≤ distance D)
    (hRpower : ∀ k : ℕ, 0 < k → 6 ≤ weight (R ^ k))
    (p : ℕ) [ExpChar K p]
    (hDpower : ∀ k : ℕ, 0 < k → weight (D ^ k) ≤ 2 → ∃ e : ℕ, k = p ^ e)
    (hrows : ∀ G : MvPolynomial (Option σ) K, G ≠ 0 → linearExtension R D ∣ G →
      weight G ≤ 7 → 3 ≤ (optionEquivLeft K σ G).support.card)
    (M N : MvPolynomial (Option σ) K) (hM : weight M = 1) (hN : weight N = 1)
    {i j : ℕ} (hi : 0 < i) (hij : i < j)
    (hG : M * linearExtension R D ^ i + N * linearExtension R D ^ j ≠ 0) :
    8 ≤ weight (M * linearExtension R D ^ i + N * linearExtension R D ^ j) := by
  classical
  have mono (L : MvPolynomial (Option σ) K) (hL : weight L = 1) :
      ∃ a u, u ≠ 0 ∧ L = monomial a u := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hL
    exact ⟨a, coeff a L, mem_support_iff.mp (by rw [ha]; simp),
      (Finsupp.support_eq_singleton.mp ha).2⟩
  obtain ⟨a, u, hu, rfl⟩ := mono M hM
  obtain ⟨b, v, hv, rfl⟩ := mono N hN
  let E := linearExtension R D
  let G := monomial a u * E ^ i + monomial b v * E ^ j
  let Q : Polynomial (MvPolynomial σ K) := Polynomial.C R + Polynomial.C D * Polynomial.X
  have hj : 0 < j := by omega
  have hdiv : E ∣ G := by
    apply dvd_add
    · exact dvd_mul_of_dvd_right (dvd_pow_self E (Nat.ne_of_gt hi)) _
    · exact dvd_mul_of_dvd_right (dvd_pow_self E (Nat.ne_of_gt hj)) _
  by_contra hn
  have hw : weight G ≤ 7 := by change ¬8 ≤ weight G at hn; omega
  have hG' : G ≠ 0 := hG
  obtain ⟨_, _, _, _, htc, _, _⟩ := linearExtension_small_multiple_shape R D hR hD hRd hDd
    G hG' hdiv (hrows G hG' hdiv hw) hw
  have unequal (a b : Option σ →₀ ℕ) (u v : K) (hu : u ≠ 0)
      (i j : ℕ) (hi : 0 < i) (hab : a none < b none) :
      6 ≤ weight (optionEquivLeft K σ
        (monomial a u * E ^ i + monomial b v * E ^ j)).trailingCoeff := by
    have hmap : optionEquivLeft K σ (monomial a u * E ^ i + monomial b v * E ^ j) =
        (Polynomial.C (monomial a.some u) * Q ^ i) * Polynomial.X ^ (a none) +
        (Polynomial.C (monomial b.some v) * Q ^ j) * Polynomial.X ^ (b none) := by
      rw [map_add, optionEquiv_monomial_mul_pow, optionEquiv_monomial_mul_pow]
    have hconst : (Polynomial.C (monomial a.some u) * Q ^ i).coeff 0 =
        monomial a.some u * R ^ i := by
      rw [Polynomial.coeff_C_mul, polynomial_coeff_zero_pow]
      simp [Q]
    have hconst0 : (Polynomial.C (monomial a.some u) * Q ^ i).coeff 0 ≠ 0 := by
      rw [hconst]
      exact mul_ne_zero (by simpa using hu) (pow_ne_zero i hR)
    have h := (trailingDegree_shifted_sum (Polynomial.C (monomial a.some u) * Q ^ i)
      (Polynomial.C (monomial b.some v) * Q ^ j) (a none) (b none) hab hconst0).2
    rw [hmap, h, hconst, weight_scalar_monomial_mul _ hu]
    exact hRpower i hi
  have hab : a none = b none := by
    rcases lt_trichotomy (a none) (b none) with h | h | h
    · have hbad := unequal a b u v hu i j hi h
      change weight (optionEquivLeft K σ G).trailingCoeff = 4 at htc
      change 6 ≤ weight (optionEquivLeft K σ G).trailingCoeff at hbad
      omega
    · exact h
    · have hbad := unequal b a v u hv j i hj h
      rw [add_comm] at hbad
      change weight (optionEquivLeft K σ G).trailingCoeff = 4 at htc
      change 6 ≤ weight (optionEquivLeft K σ G).trailingCoeff at hbad
      omega
  have hMa : weight (monomial a.some u : MvPolynomial σ K) = 1 := by
    simp only [weight, support_monomial, if_neg hu, Finset.card_singleton]
  have hNb : weight (monomial b.some v : MvPolynomial σ K) = 1 := by
    simp only [weight, support_monomial, if_neg hv, Finset.card_singleton]
  have hbound := linearExtension_two_base_powers_eight R D hR hD hRd hDd p hDpower hrows
    (monomial a.some u) (monomial b.some v) hMa hNb hi hij
  have hfactor : G = monomial (Finsupp.single none (a none)) 1 *
      (rename some (monomial a.some u) * E ^ i + rename some (monomial b.some v) * E ^ j) := by
    dsimp only [G]
    rw [monomial_split_none a u, monomial_split_none b v, ← hab]
    ring
  rw [hfactor, weight_monomial_mul] at hw
  change 8 ≤ weight (rename some (monomial a.some u) * E ^ i +
    rename some (monomial b.some v) * E ^ j) at hbound
  omega

end WeightedPilz
