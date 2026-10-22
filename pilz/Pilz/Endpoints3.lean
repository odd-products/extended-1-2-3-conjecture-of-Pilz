import Pilz.Endpoints

/-! Three occupied coefficient rows strengthen the endpoint distance budget
by one term. This isolates the support-counting part of the quadratic
obstruction from its algebraic proof. -/

noncomputable section

namespace Pilz

open MvPolynomial

private def liftRow {σ : Type*} (k : ℕ) (d : σ →₀ ℕ) : Option σ →₀ ℕ :=
  d.embDomain .some + Finsupp.single none k

@[simp] private theorem liftRow_none {σ : Type*} (k : ℕ) (d : σ →₀ ℕ) :
    liftRow k d none = k := by simp [liftRow]

@[simp] private theorem liftRow_some {σ : Type*} (k : ℕ) (d : σ →₀ ℕ) :
    (liftRow k d).some = d := by ext i; simp [liftRow]

private theorem liftRow_injective {σ : Type*} (k : ℕ) :
    Function.Injective (liftRow (σ := σ) k) := by
  intro a b hab
  simpa only [liftRow_some] using congrArg Finsupp.some hab

private theorem optionCoeff_liftRow {σ : Type*}
    (P : MvPolynomial (Option σ) (ZMod 2)) (k : ℕ) (d : σ →₀ ℕ) :
    MvPolynomial.coeff d ((optionEquivLeft (ZMod 2) σ P).coeff k) =
      MvPolynomial.coeff (liftRow k d) P := by
  simpa only [liftRow_none, liftRow_some] using
    optionEquivLeft_coeff_coeff (ZMod 2) σ (liftRow k d) P

private def rowSupport {σ : Type*}
    (P : MvPolynomial (Option σ) (ZMod 2)) (k : ℕ) : Finset (Option σ →₀ ℕ) := by
  classical
  exact ((optionEquivLeft (ZMod 2) σ P).coeff k).support.image (liftRow k)

private theorem rowSupport_subset {σ : Type*}
    (P : MvPolynomial (Option σ) (ZMod 2)) (k : ℕ) : rowSupport P k ⊆ P.support := by
  classical
  intro d hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  apply MvPolynomial.mem_support_iff.mpr
  have hc := MvPolynomial.mem_support_iff.mp ha
  rwa [optionCoeff_liftRow] at hc

private theorem rowSupport_card {σ : Type*}
    (P : MvPolynomial (Option σ) (ZMod 2)) (k : ℕ) :
    (rowSupport P k).card = termWeight ((optionEquivLeft (ZMod 2) σ P).coeff k) := by
  classical
  exact Finset.card_image_of_injective _ (liftRow_injective k)

private theorem rowSupport_disjoint {σ : Type*}
    (P : MvPolynomial (Option σ) (ZMod 2)) (i j : ℕ) (hij : i ≠ j) :
    Disjoint (rowSupport P i) (rowSupport P j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hdi hdj
  obtain ⟨a, _, hda⟩ := Finset.mem_image.mp hdi
  obtain ⟨b, _, hdb⟩ := Finset.mem_image.mp hdj
  apply hij
  have heq : liftRow i a = liftRow j b := hda.trans hdb.symm
  simpa only [liftRow_none] using congrArg (fun e => e none) heq

/-- Three distinct coefficient slices occupy disjoint parts of the support. -/
theorem termWeight_three_slices {σ : Type*}
    (P : MvPolynomial (Option σ) (ZMod 2)) (i j k : ℕ)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    termWeight ((optionEquivLeft (ZMod 2) σ P).coeff i) +
      termWeight ((optionEquivLeft (ZMod 2) σ P).coeff j) +
      termWeight ((optionEquivLeft (ZMod 2) σ P).coeff k) ≤ termWeight P := by
  classical
  have hij' := rowSupport_disjoint P i j hij
  have hk' : Disjoint (rowSupport P i ∪ rowSupport P j) (rowSupport P k) :=
    Finset.disjoint_union_left.mpr
      ⟨rowSupport_disjoint P i k hik, rowSupport_disjoint P j k hjk⟩
  calc
    _ = (rowSupport P i).card + (rowSupport P j).card + (rowSupport P k).card := by
      rw [rowSupport_card, rowSupport_card, rowSupport_card]
    _ = ((rowSupport P i ∪ rowSupport P j) ∪ rowSupport P k).card := by
      rw [Finset.card_union_of_disjoint hk', Finset.card_union_of_disjoint hij']
    _ ≤ P.support.card := Finset.card_le_card
      (Finset.union_subset (Finset.union_subset (rowSupport_subset P i) (rowSupport_subset P j))
        (rowSupport_subset P k))

/-- If every nonzero multiple occupies at least three rows, its two endpoint
budgets leave at least one further term in an intermediate row. -/
theorem endpoint_distance_option_three {σ : Type*}
    (P : MvPolynomial (Option σ) (ZMod 2))
    (hspan : (optionEquivLeft (ZMod 2) σ P).natTrailingDegree <
      (optionEquivLeft (ZMod 2) σ P).natDegree)
    (hrows : ∀ H : MvPolynomial (Option σ) (ZMod 2), H ≠ 0 →
      3 ≤ (optionEquivLeft (ZMod 2) σ (P * H)).support.card) :
    distance (optionEquivLeft (ZMod 2) σ P).trailingCoeff +
      distance (optionEquivLeft (ZMod 2) σ P).leadingCoeff + 1 ≤ distance P := by
  classical
  apply (le_distance_iff P _).mpr
  intro H hH
  let E := optionEquivLeft (ZMod 2) σ
  let Q := E P
  let V := E H
  have hV : V ≠ 0 := by
    intro hz
    apply hH
    exact E.injective (hz.trans (map_zero E).symm)
  have hVt : V.trailingCoeff ≠ 0 := mt Polynomial.trailingCoeff_eq_zero.mp hV
  have hVl : V.leadingCoeff ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.mp hV
  have hlow := distance_le_weight_mul Q.trailingCoeff V.trailingCoeff hVt
  have hhigh := distance_le_weight_mul Q.leadingCoeff V.leadingCoeff hVl
  have horder := Polynomial.natTrailingDegree_le_natDegree V
  have hneq : Q.natTrailingDegree + V.natTrailingDegree ≠ Q.natDegree + V.natDegree := by
    change Q.natTrailingDegree < Q.natDegree at hspan
    omega
  let lo := Q.natTrailingDegree + V.natTrailingDegree
  let hi := Q.natDegree + V.natDegree
  have hcard : ({lo, hi} : Finset ℕ).card < (E (P * H)).support.card := by
    have htwo : ({lo, hi} : Finset ℕ).card ≤ 2 := Finset.card_le_two
    have hthree : 3 ≤ (E (P * H)).support.card := hrows H hH
    omega
  obtain ⟨k, hk, hkne⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hlk : lo ≠ k := by intro heq; apply hkne; simp [← heq]
  have hhk : hi ≠ k := by intro heq; apply hkne; simp [← heq]
  have hkcoeff : (E (P * H)).coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
  have hkweight := termWeight_pos hkcoeff
  have hthree := termWeight_three_slices (P * H) lo hi k hneq hlk hhk
  change termWeight ((E (P * H)).coeff lo) + termWeight ((E (P * H)).coeff hi) +
    termWeight ((E (P * H)).coeff k) ≤ termWeight (P * H) at hthree
  have hmap : E (P * H) = Q * V := map_mul E P H
  dsimp [lo, hi] at hthree
  rw [hmap, Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree,
    Polynomial.coeff_mul_degree_add_degree] at hthree
  rw [hmap] at hkweight
  change distance Q.trailingCoeff + distance Q.leadingCoeff + 1 ≤ termWeight (P * H)
  omega

/-- The three-row endpoint budget in a named coordinate. -/
theorem endpoint_distance_three {σ : Type*} [DecidableEq σ] (p : σ)
    (P : MvPolynomial σ (ZMod 2))
    (hspan : (coordinateEquiv p P).natTrailingDegree < (coordinateEquiv p P).natDegree)
    (hrows : ∀ H : MvPolynomial σ (ZMod 2), H ≠ 0 →
      3 ≤ (coordinateEquiv p (P * H)).support.card) :
    distance (coordinateEquiv p P).trailingCoeff +
      distance (coordinateEquiv p P).leadingCoeff + 1 ≤ distance P := by
  let E := renameEquiv (ZMod 2) (Equiv.optionSubtypeNe p).symm
  have hrows' : ∀ H : MvPolynomial (Option {q : σ // q ≠ p}) (ZMod 2), H ≠ 0 →
      3 ≤ (optionEquivLeft (ZMod 2) {q : σ // q ≠ p} (E P * H)).support.card := by
    intro H hH
    have hEH : E.symm H ≠ 0 := fun hz => hH (by
      have := congrArg E hz
      simpa using this)
    have h := hrows (E.symm H) hEH
    change 3 ≤ (optionEquivLeft (ZMod 2) {q : σ // q ≠ p} (E (P * E.symm H))).support.card at h
    simpa only [map_mul, E.apply_symm_apply] using h
  have h := endpoint_distance_option_three (E P) hspan hrows'
  have hdist : distance (E P) = distance P :=
    distance_renameEquiv (Equiv.optionSubtypeNe p).symm P
  rw [hdist] at h
  exact h

end Pilz
