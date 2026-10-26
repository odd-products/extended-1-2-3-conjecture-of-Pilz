import WeightedPilz.Endpoints

/-! Occupied coordinate rows and the endpoint bound with an additional row. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K]

private def rowExponent (k : ℕ) (d : σ →₀ ℕ) : Option σ →₀ ℕ :=
  d.embDomain .some + Finsupp.single none k

@[simp] private theorem rowExponent_none (k : ℕ) (d : σ →₀ ℕ) :
    rowExponent k d none = k := by simp [rowExponent]

@[simp] private theorem rowExponent_some (k : ℕ) (d : σ →₀ ℕ) :
    (rowExponent k d).some = d := by ext i; simp [rowExponent]

private theorem rowExponent_injective (k : ℕ) : Function.Injective (rowExponent (σ := σ) k) := by
  intro a b h
  simpa only [rowExponent_some] using congrArg Finsupp.some h

private theorem rowExponent_coeff (P : MvPolynomial (Option σ) K) (k : ℕ) (d : σ →₀ ℕ) :
    coeff d ((optionEquivLeft K σ P).coeff k) = coeff (rowExponent k d) P := by
  simpa only [rowExponent_none, rowExponent_some] using
    optionEquivLeft_coeff_coeff K σ (rowExponent k d) P

theorem weight_option_slices_le (P : MvPolynomial (Option σ) K) (I : Finset ℕ) :
    ∑ k ∈ I, weight ((optionEquivLeft K σ P).coeff k) ≤ weight P := by
  classical
  let A : ℕ → Finset (Option σ →₀ ℕ) := fun k =>
    ((optionEquivLeft K σ P).coeff k).support.image (rowExponent k)
  have hcard (k : ℕ) : (A k).card = weight ((optionEquivLeft K σ P).coeff k) :=
    Finset.card_image_of_injective _ (rowExponent_injective k)
  have hsub (k : ℕ) : A k ⊆ P.support := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    apply mem_support_iff.mpr
    rw [← rowExponent_coeff]
    exact mem_support_iff.mp hd
  have hdis : I.toSet.PairwiseDisjoint A := by
    intro k hk l hl hkl
    apply Finset.disjoint_left.mpr
    intro e hek hel
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp hek
    obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp hel
    have heq := congrArg (fun e => e none) (hea.trans heb.symm)
    exact hkl (by simpa only [rowExponent_none] using heq)
  calc
    _ = ∑ k ∈ I, (A k).card := Finset.sum_congr rfl (fun k _ => (hcard k).symm)
    _ = (I.biUnion A).card := (Finset.card_biUnion hdis).symm
    _ ≤ P.support.card := Finset.card_le_card (by
      intro e he
      obtain ⟨k, hk, hek⟩ := Finset.mem_biUnion.mp he
      exact hsub k hek)

theorem weight_coordinate_slices_le [DecidableEq σ] (p : σ)
    (P : MvPolynomial σ K) (I : Finset ℕ) :
    ∑ k ∈ I, weight ((coordinateEquiv p P).coeff k) ≤ weight P := by
  have h := weight_option_slices_le (renameEquiv K (Equiv.optionSubtypeNe p).symm P) I
  change (∑ k ∈ I, weight ((coordinateEquiv p P).coeff k)) ≤
    weight (renameEquiv K (Equiv.optionSubtypeNe p).symm P) at h
  rwa [weight_renameEquiv] at h

theorem coordinate_row_count_le_weight [DecidableEq σ] (p : σ) (P : MvPolynomial σ K) :
    (coordinateEquiv p P).support.card ≤ weight P := by
  calc
    _ = ∑ k ∈ (coordinateEquiv p P).support, 1 := by simp
    _ ≤ ∑ k ∈ (coordinateEquiv p P).support, weight ((coordinateEquiv p P).coeff k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact Nat.succ_le_iff.mpr (by
        simpa [weight, Finset.card_pos, MvPolynomial.support_nonempty] using
          Polynomial.mem_support_iff.mp hk)
    _ ≤ _ := weight_coordinate_slices_le p P _

/-- Three distinct occupied rows allow the two endpoints to be counted with
their full distances and at least one term from a further row. -/
theorem endpoint_distance_option_of_three_rows (P : MvPolynomial (Option σ) K)
    (hspan : (optionEquivLeft K σ P).natTrailingDegree < (optionEquivLeft K σ P).natDegree)
    (hrows : ∀ H : MvPolynomial (Option σ) K, H ≠ 0 →
      3 ≤ (optionEquivLeft K σ (P * H)).support.card) :
    distance (optionEquivLeft K σ P).trailingCoeff +
      distance (optionEquivLeft K σ P).leadingCoeff + 1 ≤ distance P := by
  classical
  apply (le_distance_iff P _).mpr
  intro H hH
  let E := optionEquivLeft K σ
  let Q := E P
  let V := E H
  let W := E (P * H)
  let lo := Q.natTrailingDegree + V.natTrailingDegree
  let hi := Q.natDegree + V.natDegree
  have hV : V ≠ 0 := by
    intro hz
    exact hH (E.injective (hz.trans (map_zero E).symm))
  have hlow := distance_le_weight_mul Q.trailingCoeff V.trailingCoeff
    (mt Polynomial.trailingCoeff_eq_zero.mp hV)
  have hhigh := distance_le_weight_mul Q.leadingCoeff V.leadingCoeff
    (mt Polynomial.leadingCoeff_eq_zero.mp hV)
  have horder := Polynomial.natTrailingDegree_le_natDegree V
  have hne : lo ≠ hi := by
    change Q.natTrailingDegree < Q.natDegree at hspan
    dsimp [lo, hi]
    omega
  have hcard : ({lo, hi} : Finset ℕ).card < W.support.card := by
    have h := hrows H hH
    have hpair := Finset.card_le_two (a := lo) (b := hi)
    change 3 ≤ W.support.card at h
    omega
  obtain ⟨m, hm, hmout⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hmne : m ≠ lo ∧ m ≠ hi := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hmout
  have hmlo := hmne.1
  have hmhi := hmne.2
  have hmid : 1 ≤ weight (W.coeff m) := Nat.succ_le_iff.mpr (by
    simpa [weight, Finset.card_pos, MvPolynomial.support_nonempty] using
      Polynomial.mem_support_iff.mp hm)
  have hs := weight_option_slices_le (P * H) {lo, hi, m}
  have hs' : weight (W.coeff lo) + weight (W.coeff hi) + weight (W.coeff m) ≤
      weight (P * H) := by
    simpa only [Finset.sum_insert, Finset.sum_singleton,
      Finset.mem_insert, Finset.mem_singleton, hne, hmlo.symm, hmhi.symm,
      or_self, not_false_eq_true, add_assoc] using hs
  have hmap : W = Q * V := map_mul E P H
  have hl : W.coeff lo = Q.trailingCoeff * V.trailingCoeff := by
    rw [hmap]
    exact Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree
  have hh : W.coeff hi = Q.leadingCoeff * V.leadingCoeff := by
    rw [hmap]
    exact Polynomial.coeff_mul_degree_add_degree Q V
  rw [hl, hh] at hs'
  change distance Q.trailingCoeff + distance Q.leadingCoeff + 1 ≤ weight (P * H)
  omega

theorem endpoint_distance_of_three_rows [DecidableEq σ] (p : σ) (P : MvPolynomial σ K)
    (hspan : (coordinateEquiv p P).natTrailingDegree < (coordinateEquiv p P).natDegree)
    (hrows : ∀ H : MvPolynomial σ K, H ≠ 0 →
      3 ≤ (coordinateEquiv p (P * H)).support.card) :
    distance (coordinateEquiv p P).trailingCoeff +
      distance (coordinateEquiv p P).leadingCoeff + 1 ≤ distance P := by
  let R := renameEquiv K (Equiv.optionSubtypeNe p).symm
  have hrows' : ∀ H, H ≠ 0 →
      3 ≤ (optionEquivLeft K {q : σ // q ≠ p} (R P * H)).support.card := by
    intro H hH
    have hH' : R.symm H ≠ 0 := by
      intro hz
      apply hH
      have hzero := congrArg R hz
      simpa using hzero
    have h := hrows (R.symm H) hH'
    change 3 ≤ (optionEquivLeft K {q : σ // q ≠ p} (R (P * R.symm H))).support.card at h
    rwa [map_mul, R.apply_symm_apply] at h
  have h := endpoint_distance_option_of_three_rows (R P) hspan hrows'
  simpa only [R, distance_renameEquiv] using h

end WeightedPilz
