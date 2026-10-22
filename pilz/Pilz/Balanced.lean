import Pilz.Synchronization
import Pilz.BiParity

/-!
# The balanced-row step of fresh synchronization

The paper's balanced alternatives can be consolidated as follows. A nonzero
pair derivative is again extremal. If one of its odd rows still has half
the weight, the two single-odd blocks of the original vanish. The pair
derivative then factors through `X i + X j`; primality of `F` produces a
strictly smaller multiple, a contradiction. Hence the new row is strict.
-/

noncomputable section

namespace Pilz

open MvPolynomial

private theorem bi11_base_width_le (B : Finset ℕ) (G : Poly) (i j : ℕ)
    (hi : i ∉ B) (hj : j ∉ B) (hQ : bi11 G i j ≠ 0) :
    ∀ p ∈ B, widthOf p (bi11 G i j) ≤ widthOf p G := by
  intro p hp
  have hpi : p ≠ i := by rintro rfl; exact hi hp
  have hpj : p ≠ j := by rintro rfl; exact hj hp
  apply widthOf_mono_exponents p hQ
  intro d hd
  change d ∈ (pderiv i (pderiv j G)).support at hd
  obtain ⟨e, he, hde⟩ := pderiv_base_exponents hd
  obtain ⟨f, hf, hef⟩ := pderiv_base_exponents he
  exact ⟨f, hf, (hde p hpi).symm.trans (hef p hpj).symm⟩

/-- Step 3: a nonzero pair derivative of an extremal polynomial whose two
odd counts are bounded by half has a strictly smaller-than-half odd row. -/
theorem pair_pderiv_extremal_strict (S : FreshData) (B : Finset ℕ) (N : ℕ)
    (G : Poly) (hG : Extremal S.F B N G) (hdisjoint : Disjoint B S.vars)
    {i j : ℕ} (hi : i ∈ S.vars) (hj : j ∈ S.vars) (hij : i ≠ j)
    (hci : 2 * oddCount G i ≤ weight G) (hcj : 2 * oddCount G j ≤ weight G)
    (hQ : pderiv i G + pderiv j G ≠ 0) :
    Extremal S.F B N (pderiv i G + pderiv j G) ∧
      weight (pderiv i G + pderiv j G) = weight G ∧
      2 * oddCount (pderiv i G + pderiv j G) i <
        weight (pderiv i G + pderiv j G) := by
  have hBi : i ∉ B := fun h => Finset.disjoint_left.mp hdisjoint h hi
  have hBj : j ∉ B := fun h => Finset.disjoint_left.mp hdisjoint h hj
  have hdiv := S.dvd_pair_pderiv hi hj hG.1.2.1
  have hweight : weight (pderiv i G + pderiv j G) ≤ weight G := by
    have hw := weight_pair_pderiv_le G i j
    omega
  obtain ⟨hQext, hQweight, hQwidth⟩ :=
    extremal_stability S.F B N G _ hG hQ hdiv hweight
      (pair_pderiv_width_le B G i j hBi hBj hQ)
  refine ⟨hQext, hQweight, ?_⟩
  by_contra hnot
  have hodd := oddCount_bi_pair_pderiv G i j hij
  have hcounti := bi_oddCount_i G i j hij
  have hcountj := bi_oddCount_j G i j
  have h10weight : weight (bi10 G i j) = 0 := by omega
  have h01weight : weight (bi01 G i j) = 0 := by omega
  have h10 : bi10 G i j = 0 :=
    MvPolynomial.support_eq_empty.mp (Finset.card_eq_zero.mp h10weight)
  have h01 : bi01 G i j = 0 :=
    MvPolynomial.support_eq_empty.mp (Finset.card_eq_zero.mp h01weight)
  have hfactor : pderiv i G + pderiv j G = (X i + X j) * bi11 G i j := by
    rw [bi_pair_pderiv G i j hij, h10, h01, zero_add, zero_add]
  have h11nonzero : bi11 G i j ≠ 0 := by
    intro hz
    apply hQ
    rw [hfactor, hz, mul_zero]
  have h11div : S.F ∣ bi11 G i j := by
    rw [hfactor] at hdiv
    exact (S.prime_F.dvd_mul.mp hdiv).resolve_left (S.not_dvd_X_add_X hi hj hij)
  have hmpos : 0 < weight G := weight_pos hG.1.1
  have h11weight : weight (bi11 G i j) < weight G := by omega
  have hz := extremal_eq_zero_of_weight_lt S.F B N G (bi11 G i j) hG h11div
    h11weight (fun hn => bi11_base_width_le B G i j hBi hBj hn)
  exact h11nonzero hz

/-- Steps 1--3 of the paper: some extremal multiple has a common fresh
derivative, and that derivative has at most half its weight. Nonvanishing
of the common derivative is the subsequent square-root descent step. -/
theorem exists_extremal_common_derivative (S : FreshData) (B : Finset ℕ) (N : ℕ)
    (hdisjoint : Disjoint B S.vars) (hex : ∃ G : Poly, ShortMultiple S.F N G) :
    ∃ G D : Poly, Extremal S.F B N G ∧
      (∀ z ∈ S.vars, pderiv z G = D) ∧ 2 * weight D ≤ weight G := by
  classical
  obtain ⟨G, hG⟩ := exists_extremal S.F B N hex
  obtain ⟨E, hE, hEweight, hEcounts, hEoutside⟩ :=
    exists_oddCount_bounded_extremal S.F B S.vars N G hG
  obtain ⟨i, hi⟩ := S.nonempty
  by_cases hcommon : ∀ z ∈ S.vars, pderiv z E = pderiv i E
  · refine ⟨E, pderiv i E, hE, hcommon, ?_⟩
    simpa only [weight_pderiv] using hEcounts i hi
  · have hexj : ∃ j ∈ S.vars, pderiv j E ≠ pderiv i E := by
      by_contra hnot
      apply hcommon
      intro j hj
      by_contra hneq
      exact hnot ⟨j, hj, hneq⟩
    obtain ⟨j, hj, hneq⟩ := hexj
    have hij : i ≠ j := by
      intro h
      apply hneq
      rw [h]
    have hQ : pderiv i E + pderiv j E ≠ 0 := by
      intro hz
      exact hneq ((eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq _)).symm
    obtain ⟨hQext, hQweight, hQstrict⟩ :=
      pair_pderiv_extremal_strict S B N E hE hdisjoint hi hj hij
        (hEcounts i hi) (hEcounts j hj) hQ
    obtain ⟨R, hR, hRweight, hRcounts, hRoutside⟩ :=
      exists_oddCount_bounded_extremal S.F B (S.vars.erase i) N _ hQext
    have hRi : oddCount R i = oddCount (pderiv i E + pderiv j E) i :=
      hRoutside i (Finset.notMem_erase i S.vars)
    have hRstrict : 2 * oddCount R i < weight R := by
      rw [hRi, hRweight]
      exact hQstrict
    have hRall : ∀ z ∈ S.vars, 2 * oddCount R z ≤ weight R := by
      intro z hz
      by_cases hzi : z = i
      · subst z
        exact hRstrict.le
      · exact hRcounts z (Finset.mem_erase.mpr ⟨hzi, hz⟩)
    refine ⟨R, pderiv i R, hR,
      derivatives_eq_of_strict_oddCount S B N R hR hdisjoint hi hRstrict hRall, ?_⟩
    simpa only [weight_pderiv] using (hRall i hi)

end Pilz
