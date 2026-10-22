import Pilz.SmallRegular

/-! The exceptional small-case rows use at most one residual class. The
polynomial argument is common to the rows; the remaining capacity and
product thresholds are explicit finite numerical inputs. -/

noncomputable section

namespace Pilz

/-- A numerical core budget excludes two or more residual classes. -/
theorem small_residual_class_count_le_one (n r T M a m : ℕ)
    (hm : m ≤ T) (hcore : a * n + 4 * r ≤ m + a * M)
    (hnum : T + 2 * M < 2 * n + 4 * r) (hMn : M ≤ n) : a ≤ 1 := by
  by_contra hnot
  have ha : 2 ≤ a := by omega
  have hmul := Nat.mul_le_mul_right (n - M) ha
  have hsub : M + (n - M) = n := by omega
  have han : a * M + a * (n - M) = a * n := by rw [← Nat.mul_add, hsub]
  have htwo : 2 * M + 2 * (n - M) = 2 * n := by rw [← Nat.mul_add, hsub]
  omega

/-- The normal-form criterion used at lengths 27, 40, and 49 through 52.
The `u≤3` branch uses the ordinary product bound; the `u=4` branch uses a
stronger row-specific product bound and the one-residual-class protection. -/
theorem conjectureAt_small_exceptional (n κ r T M3 M4 B : ℕ)
    (hn : 11 ≤ n) (hsmall : n ≤ 66)
    (hr : (freshPrimes n).card = r) (hrpos : 0 < r)
    (hκ : κ ≤ distance (core n)) (hκpos : 2 ≤ κ)
    (hbound : ∀ m : ℕ, m < n → (Even n → Even m) → m ≤ T)
    (hreduce : ∀ m u : ℕ, 0 < u → r * u < m → 2 * u ≤ m → m ≤ T →
      u < κ ∧ (r * u + κ ≤ m → u ≤ 4))
    (hMthree : 3 * Nat.sqrt n ≤ M3 ∨
      (26 ≤ n ∧ n ≤ 29 ∧ 2 * Nat.sqrt n + Nat.sqrt (n / 2) ≤ M3))
    (hMfour : 3 * Nat.sqrt n + Nat.sqrt (n / 2) ≤ M4)
    (hNMthree : 2 * M3 ≤ n)
    (hclassNum : T + 2 * M4 < 2 * n + 4 * r) (hMfourN : M4 ≤ n)
    (hB : ∀ D : Poly, D ≠ 0 → weight D = 4 → B ≤ weight (interval n * D))
    (hBN : n ≤ B) (hBM : 2 * M4 ≤ B) : ConjectureAt n := by
  classical
  have hnpos : 0 < n := by omega
  have hfresh : (freshPrimes n).Nonempty := Finset.card_pos.mp (by omega)
  let S := intervalFreshData n hnpos hfresh
  have hF : S.F = interval n := intervalFreshData_F n hnpos hfresh
  intro H hH
  by_contra hnot
  have hshort : weight (interval n * H) < n := by omega
  have hex : ∃ G : Poly, ShortMultiple S.F n G := by
    refine ⟨S.F * H, mul_ne_zero S.prime_F.ne_zero hH, dvd_mul_right _ _, ?_⟩
    simpa only [hF] using hshort
  have hC : 2 ≤ weight S.C :=
    hκpos.trans (hκ.trans (distance_le_termWeight S.C))
  obtain ⟨nf⟩ := exists_normalForm S n hC hex
  have hm : weight nf.G < n := nf.extremal.1.2.2
  have hpar : Even n → Even (weight nf.G) := by
    intro hnEven
    obtain ⟨V, hV⟩ := nf.extremal.1.2.1
    have hp : Even (weight (S.F * V)) :=
      even_weight_mul (P := S.F) (by simpa [hF] using hnEven) V
    rwa [← hV] at hp
  have hmT := hbound (weight nf.G) hm hpar
  have hu : 0 < weight nf.D := weight_pos nf.D_ne_zero
  have hG₀ : 0 < weight nf.G₀ := weight_pos nf.G₀_ne_zero
  have hw := normalForm_weight S n nf
  change weight nf.G₀ + (freshPrimes n).card * weight nf.D = weight nf.G at hw
  rw [hr] at hw
  have hru : r * weight nf.D < weight nf.G := by omega
  obtain ⟨husmall, huFour⟩ := hreduce (weight nf.G) (weight nf.D) hu hru nf.half hmT
  have hcore := normalForm_core_budget S n nf (husmall.trans_le hκ)
  change (freshPrimes n).card * weight nf.D + distance (core n) ≤ weight nf.G at hcore
  rw [hr] at hcore
  have huFour' : weight nf.D ≤ 4 := huFour ((Nat.add_le_add_left hκ _).trans hcore)
  have hN : n ≤ weight S.C + S.vars.card := by
    rw [← S.weight_F, hF, weight_interval]
  have hbase : ∀ k : ℕ, weight nf.D ≤ k → ∀ ε : ℕ → ℕ,
      classWeight (S.C * nf.D) ε ≤ k * Nat.sqrt n := by
    intro k hk ε
    change classWeight (core n * nf.D) ε ≤ k * Nat.sqrt n
    have hcap := classWeight_mul_le (core n) nf.D (Nat.sqrt n)
      (fun η => (classWeight_le_sigma (core n) η).trans (sigma_core_le_sqrt n)) ε
    exact hcap.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (Nat.sqrt n) hk)
  by_cases hthree : weight nf.D ≤ 3
  · have hcap3 : ∀ ε : ℕ → ℕ, classWeight (S.C * nf.D) ε ≤ M3 := by
      intro ε
      rcases hMthree with huniform | ⟨hlo, hhi, hrefined⟩
      · exact (hbase 3 hthree ε).trans huniform
      · by_cases htwo : weight nf.D ≤ 2
        · have hcap := hbase 2 htwo ε
          omega
        · have huEq : weight nf.D = 3 := by omega
          have hclasses := normalForm_interval_at_least_two_classes_26_29 n hnpos hfresh nf
            hlo hhi (by omega : 3 ≤ weight nf.D)
          have hcap := classWeight_core_mul_dispersed_two n nf.D hclasses ε
          have hcap' : classWeight (core n * nf.D) ε ≤
              2 * Nat.sqrt n + Nat.sqrt (n / 2) := by simpa [huEq] using hcap
          exact hcap'.trans hrefined
    have hprod : n ≤ weight (S.F * nf.D) := by
      rw [hF]
      exact three_multipliers n nf.D nf.D_ne_zero hthree
    exact normalForm_excluded_of_twice_capacity S n nf hN M3 hcap3 hNMthree hprod
  · have huEq : weight nf.D = 4 := by omega
    have hclasses := normalForm_interval_at_least_two_classes n hnpos hfresh nf hsmall
      (by omega : 4 ≤ weight nf.D)
    have hcap4 : ∀ ε : ℕ → ℕ, classWeight (S.C * nf.D) ε ≤ M4 := by
      intro ε
      have hcap := classWeight_core_mul_dispersed_two n nf.D hclasses ε
      have hcap' : classWeight (core n * nf.D) ε ≤
          3 * Nat.sqrt n + Nat.sqrt (n / 2) := by simpa [huEq] using hcap
      exact hcap'.trans hMfour
    have hprotected := normalForm_protected_core S n nf hN M4 hcap4
    have hineq : (parityIndices (nf.G₀ + S.C * nf.D)).card * n + 4 * r ≤
        weight nf.G + (parityIndices (nf.G₀ + S.C * nf.D)).card * M4 := by
      rw [huEq] at hw
      omega
    have ha := small_residual_class_count_le_one n r T M4
      (parityIndices (nf.G₀ + S.C * nf.D)).card (weight nf.G)
      hmT hineq hclassNum hMfourN
    have hproduct : B ≤ weight (S.F * nf.D) := by
      rw [hF]
      exact hB nf.D nf.D_ne_zero huEq
    exact normalForm_excluded_of_one_class S n nf hN M4 hcap4 ha
      (hBN.trans hproduct) (hBM.trans hproduct)

end Pilz
