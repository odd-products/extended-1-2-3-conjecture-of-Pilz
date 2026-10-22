import Pilz.FewMultipliers

/-!
# The compatibility budget at length 27

This proves equation `compat` in the paper. In its exceptional branch,
the two-term product `(1+x)E` forces `E` to occupy one y-row: two rows
would each cost at least two terms. Consequently adding `yE` loses no
terms. This is the slicing content of the paper's geometric-trinomial
classification, and avoids needing that stronger classification.
-/

noncomputable section

namespace Pilz

open MvPolynomial

private theorem two_le_one_add_X_mul {σ : Type*} [DecidableEq σ]
    (p : σ) (H : MvPolynomial σ (ZMod 2)) (hH : H ≠ 0) :
    2 ≤ termWeight (((1 : MvPolynomial σ (ZMod 2)) + X p) * H) := by
  have h0 : coeff 0 ((1 : MvPolynomial σ (ZMod 2)) + X p) ≠ 0 := by simp
  have hpure : ∀ q ∈ ({p} : Finset σ), ∃ k : ℕ, 0 < k ∧
      coeff (Finsupp.single q k) ((1 : MvPolynomial σ (ZMod 2)) + X p) ≠ 0 := by
    intro q hq
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    have hnz : (0 : σ →₀ ℕ) ≠ Finsupp.single p 1 := by
      intro h
      have hh := congrArg (fun d : σ →₀ ℕ => d p) h
      simp at hh
    exact ⟨1, by decide, by simp [MvPolynomial.coeff_one, hnz]⟩
  simpa using pure_endpoints_weight_mul ({p} : Finset σ) (1 + X p) H h0 hpure hH

private theorem two_coordinate_slices (p : ℕ) (P : Poly) (i j : ℕ) (hij : i ≠ j) :
    termWeight ((coordinateEquiv p P).coeff i) +
      termWeight ((coordinateEquiv p P).coeff j) ≤ weight P := by
  have h := termWeight_two_slices
    (renameEquiv (ZMod 2) (Equiv.optionSubtypeNe p).symm P) i j hij
  change termWeight ((coordinateEquiv p P).coeff i) +
    termWeight ((coordinateEquiv p P).coeff j) ≤
      termWeight (renameEquiv (ZMod 2) (Equiv.optionSubtypeNe p).symm P) at h
  rw [termWeight_renameEquiv] at h
  exact h

private def otherTwo : {q : ℕ // q ≠ 3} := ⟨2, by decide⟩

private theorem coordinate_three_F2 :
    coordinateEquiv 3 (interval 2) =
      Polynomial.C (1 + X otherTwo : MvPolynomial {q : ℕ // q ≠ 3} (ZMod 2)) := by
  rw [interval_two]
  simp [coordinateEquiv, otherTwo, Equiv.optionSubtypeNe_symm_of_ne (by decide : 2 ≠ 3),
    optionEquivLeft_X_some]

private theorem coordinate_three_X : coordinateEquiv 3 (X 3 : Poly) = Polynomial.X := by
  simp [coordinateEquiv, optionEquivLeft_X_none]

/-- A two-term multiple of `F₂` is homogeneous in the independent y
coordinate, so `F₂E` and `yE` have disjoint supports. -/
theorem interval_two_product_disjoint_X_three (E : Poly)
    (htwo : weight (interval 2 * E) = 2) :
    Disjoint (interval 2 * E).support (X 3 * E).support := by
  classical
  let Q := coordinateEquiv 3 E
  let A : MvPolynomial {q : ℕ // q ≠ 3} (ZMod 2) := 1 + X otherTwo
  have hcard : Q.support.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    have hci : Q.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hcj : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have hiw := two_le_one_add_X_mul otherTwo (Q.coeff i) hci
    have hjw := two_le_one_add_X_mul otherTwo (Q.coeff j) hcj
    have hslice := two_coordinate_slices 3 (interval 2 * E) i j hij
    rw [map_mul, coordinate_three_F2] at hslice
    simp only [Polynomial.coeff_C_mul] at hslice
    change 2 ≤ termWeight (A * Q.coeff i) at hiw
    change 2 ≤ termWeight (A * Q.coeff j) at hjw
    change termWeight (A * Q.coeff i) + termWeight (A * Q.coeff j) ≤ _ at hslice
    omega
  obtain ⟨k, T, hQ⟩ := Polynomial.card_support_le_one_iff_monomial.mp hcard
  have hG : coordinateEquiv 3 (interval 2 * E) = Polynomial.monomial k (A * T) := by
    rw [map_mul, coordinate_three_F2]
    change Polynomial.C A * Q = _
    rw [hQ, Polynomial.C_mul_monomial]
  have hY : coordinateEquiv 3 (X 3 * E) = Polynomial.monomial (k + 1) T := by
    rw [map_mul, coordinate_three_X]
    change Polynomial.X * Q = _
    rw [hQ, Polynomial.X_mul_monomial]
  apply Finset.disjoint_left.mpr
  intro d hdG hdY
  have hdsG : d 3 ∈ (coordinateEquiv 3 (interval 2 * E)).support := by
    rw [support_coordinateEquiv]
    exact Finset.mem_image.mpr ⟨d, hdG, rfl⟩
  have hdsY : d 3 ∈ (coordinateEquiv 3 (X 3 * E)).support := by
    rw [support_coordinateEquiv]
    exact Finset.mem_image.mpr ⟨d, hdY, rfl⟩
  rw [hG] at hdsG
  rw [hY] at hdsY
  have hg : d 3 = k := Finset.mem_singleton.mp (Polynomial.support_monomial' _ _ hdsG)
  have hy : d 3 = k + 1 := Finset.mem_singleton.mp (Polynomial.support_monomial' _ _ hdsY)
  omega

theorem weight_interval_three_mul_of_two_product (E : Poly)
    (htwo : weight (interval 2 * E) = 2) :
    weight (interval 3 * E) = 2 + weight E := by
  have hdis := interval_two_product_disjoint_X_three E htwo
  have heq : interval 3 * E = interval 2 * E + X 3 * E := by
    rw [interval_three, interval_two]
    ring
  rw [heq, weight_add_of_disjoint _ _ hdis, htwo]
  have hX : weight (X 3 * E) = weight E := by
    simp only [weight, support_X_mul, Finset.card_map]
  rw [hX]

/-- Equation `compat`: the two small intervals have a joint budget for
every multiplier with at most three terms. -/
theorem small_interval_compatibility (E : Poly) (hE : E ≠ 0) (hfew : weight E ≤ 3) :
    weight E + 4 ≤ weight (interval 2 * E) + weight (interval 3 * E) := by
  have hpos := weight_pos hE
  have h2 := conjectureAt_two E hE
  have h3 := conjectureAt_three E hE
  have hcases : weight E = 1 ∨ weight E = 2 ∨ weight E = 3 := by omega
  rcases hcases with hk | hk | hk
  · rw [weight_interval_mul_of_weight_one 2 E hk,
      weight_interval_mul_of_weight_one 3 E hk, hk]
  · have hm := weight_mul_mod_two (interval 3) E
    rw [weight_interval, hk] at hm
    norm_num at hm
    omega
  · by_cases hbig : 4 ≤ weight (interval 2 * E)
    · omega
    · have hm := weight_mul_mod_two (interval 2) E
      rw [weight_interval, hk] at hm
      norm_num at hm
      have ht : weight (interval 2 * E) = 2 := by omega
      rw [weight_interval_three_mul_of_two_product E ht, ht, hk]

end Pilz
