import Pilz.Support
import Pilz.Width
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Field.ZMod

/-!
# Minimal weight and endpoint slicing

The distance is the exact minimum over nonzero multipliers. It is generic in
the variable type so that the endpoint coefficients, which omit one variable,
have the same definition of distance as the original polynomial.
-/

noncomputable section

namespace Pilz

open MvPolynomial

/-- The number of terms, allowing any type of variables. On `Poly` this is
definitionally equal to `weight`. -/
def termWeight {σ : Type*} (P : MvPolynomial σ (ZMod 2)) : ℕ := P.support.card

private theorem exists_multiple_weight {σ : Type*} (P : MvPolynomial σ (ZMod 2)) :
    ∃ m : ℕ, ∃ H : MvPolynomial σ (ZMod 2), H ≠ 0 ∧ termWeight (P * H) = m :=
  ⟨termWeight P, 1, one_ne_zero, by simp⟩

/-- The exact minimum weight of a product with a nonzero multiplier. -/
def distance {σ : Type*} (P : MvPolynomial σ (ZMod 2)) : ℕ := by
  classical
  exact Nat.find (exists_multiple_weight P)

theorem exists_weight_eq_distance {σ : Type*} (P : MvPolynomial σ (ZMod 2)) :
    ∃ H : MvPolynomial σ (ZMod 2), H ≠ 0 ∧ termWeight (P * H) = distance P := by
  classical
  exact Nat.find_spec (exists_multiple_weight P)

theorem distance_le_weight_mul {σ : Type*} (P H : MvPolynomial σ (ZMod 2))
    (hH : H ≠ 0) : distance P ≤ termWeight (P * H) := by
  classical
  exact Nat.find_min' (exists_multiple_weight P) ⟨H, hH, rfl⟩

theorem le_distance_iff {σ : Type*} (P : MvPolynomial σ (ZMod 2)) (k : ℕ) :
    k ≤ distance P ↔ ∀ H : MvPolynomial σ (ZMod 2), H ≠ 0 → k ≤ termWeight (P * H) := by
  constructor
  · intro hk H hH
    exact hk.trans (distance_le_weight_mul P H hH)
  · intro h
    obtain ⟨H, hH, heq⟩ := exists_weight_eq_distance P
    rw [← heq]
    exact h H hH

theorem distance_le_termWeight {σ : Type*} (P : MvPolynomial σ (ZMod 2)) :
    distance P ≤ termWeight P := by
  simpa using distance_le_weight_mul P 1 one_ne_zero

@[simp] theorem termWeight_zero {σ : Type*} : termWeight (0 : MvPolynomial σ (ZMod 2)) = 0 := by
  simp [termWeight]

theorem termWeight_pos {σ : Type*} {P : MvPolynomial σ (ZMod 2)} (hP : P ≠ 0) :
    0 < termWeight P := by
  simpa [termWeight, Finset.card_pos, MvPolynomial.support_nonempty] using hP

theorem distance_pos {σ : Type*} {P : MvPolynomial σ (ZMod 2)} (hP : P ≠ 0) :
    0 < distance P := by
  obtain ⟨H, hH, heq⟩ := exists_weight_eq_distance P
  rw [← heq]
  exact termWeight_pos (mul_ne_zero hP hH)

@[simp] theorem distance_zero {σ : Type*} : distance (0 : MvPolynomial σ (ZMod 2)) = 0 := by
  have h := distance_le_termWeight (0 : MvPolynomial σ (ZMod 2))
  simpa using h

/-- Relabeling variables by an equivalence preserves the number of terms. -/
theorem termWeight_renameEquiv {σ τ : Type*} (e : σ ≃ τ)
    (P : MvPolynomial σ (ZMod 2)) :
    termWeight (MvPolynomial.renameEquiv (ZMod 2) e P) = termWeight P := by
  classical
  rw [termWeight, MvPolynomial.renameEquiv_apply,
    MvPolynomial.support_rename_of_injective e.injective]
  apply Finset.card_image_iff.mpr
  exact (Finsupp.mapDomain_injective e.injective).injOn

/-- Relabeling variables preserves the exact minimum, including attainability. -/
theorem distance_renameEquiv {σ τ : Type*} (e : σ ≃ τ)
    (P : MvPolynomial σ (ZMod 2)) :
    distance (MvPolynomial.renameEquiv (ZMod 2) e P) = distance P := by
  let E := MvPolynomial.renameEquiv (ZMod 2) e
  apply Nat.le_antisymm
  · obtain ⟨H, hH, heq⟩ := exists_weight_eq_distance P
    have hEH : E H ≠ 0 := fun hz => hH (E.injective (by simpa using hz))
    have hle := distance_le_weight_mul (E P) (E H) hEH
    rw [← map_mul, termWeight_renameEquiv, heq] at hle
    exact hle
  · obtain ⟨H, hH, heq⟩ := exists_weight_eq_distance (E P)
    have hEH : E.symm H ≠ 0 := fun hz => hH (by
      have := congrArg E hz
      simpa using this)
    have hle := distance_le_weight_mul P (E.symm H) hEH
    have hw : termWeight (P * E.symm H) = termWeight (E P * H) := by
      have hmap : E (P * E.symm H) = E P * H := by simp only [map_mul, E.apply_symm_apply]
      rw [← hmap]
      exact (termWeight_renameEquiv e (P * E.symm H)).symm
    rw [hw, heq] at hle
    exact hle

private def liftExponent {σ : Type*} (k : ℕ) (d : σ →₀ ℕ) : Option σ →₀ ℕ :=
  d.embDomain .some + Finsupp.single none k

@[simp] private theorem liftExponent_none {σ : Type*} (k : ℕ) (d : σ →₀ ℕ) :
    liftExponent k d none = k := by simp [liftExponent]

@[simp] private theorem liftExponent_some {σ : Type*} (k : ℕ) (d : σ →₀ ℕ) :
    (liftExponent k d).some = d := by
  ext i
  simp [liftExponent]

private theorem liftExponent_injective {σ : Type*} (k : ℕ) :
    Function.Injective (liftExponent (σ := σ) k) := by
  intro a b hab
  have h := congrArg Finsupp.some hab
  simpa only [liftExponent_some] using h

private theorem optionCoeff_lift {σ : Type*}
    (P : MvPolynomial (Option σ) (ZMod 2)) (k : ℕ) (d : σ →₀ ℕ) :
    MvPolynomial.coeff d ((optionEquivLeft (ZMod 2) σ P).coeff k) =
      MvPolynomial.coeff (liftExponent k d) P := by
  simpa only [liftExponent_none, liftExponent_some] using
    optionEquivLeft_coeff_coeff (ZMod 2) σ (liftExponent k d) P

/-- Two distinct slices occupy disjoint subsets of the original support. -/
theorem termWeight_two_slices {σ : Type*}
    (P : MvPolynomial (Option σ) (ZMod 2)) (i j : ℕ) (hij : i ≠ j) :
    termWeight ((optionEquivLeft (ZMod 2) σ P).coeff i) +
      termWeight ((optionEquivLeft (ZMod 2) σ P).coeff j) ≤ termWeight P := by
  classical
  let A := ((optionEquivLeft (ZMod 2) σ P).coeff i).support.image (liftExponent i)
  let B := ((optionEquivLeft (ZMod 2) σ P).coeff j).support.image (liftExponent j)
  have hA : A ⊆ P.support := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    apply MvPolynomial.mem_support_iff.mpr
    have hc := MvPolynomial.mem_support_iff.mp ha
    rwa [optionCoeff_lift] at hc
  have hB : B ⊆ P.support := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    apply MvPolynomial.mem_support_iff.mpr
    have hc := MvPolynomial.mem_support_iff.mp ha
    rwa [optionCoeff_lift] at hc
  have hAc : A.card = termWeight ((optionEquivLeft (ZMod 2) σ P).coeff i) :=
    Finset.card_image_of_injective _ (liftExponent_injective i)
  have hBc : B.card = termWeight ((optionEquivLeft (ZMod 2) σ P).coeff j) :=
    Finset.card_image_of_injective _ (liftExponent_injective j)
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro d hdA hdB
    obtain ⟨a, ha, hda⟩ := Finset.mem_image.mp hdA
    obtain ⟨b, hb, hdb⟩ := Finset.mem_image.mp hdB
    have heq : liftExponent i a = liftExponent j b := hda.trans hdb.symm
    apply hij
    simpa only [liftExponent_none] using congrArg (fun e => e none) heq
  calc
    _ = A.card + B.card := by rw [hAc, hBc]
    _ = (A ∪ B).card := (Finset.card_union_of_disjoint hdis).symm
    _ ≤ P.support.card := Finset.card_le_card (Finset.union_subset hA hB)

/-- The endpoint inequality in one separated variable, allowing arbitrary
lowest degree. This is the slicing argument of `lem:endpoints`. -/
theorem endpoint_distance_option {σ : Type*}
    (P : MvPolynomial (Option σ) (ZMod 2))
    (hspan : (optionEquivLeft (ZMod 2) σ P).natTrailingDegree <
      (optionEquivLeft (ZMod 2) σ P).natDegree) :
    distance (optionEquivLeft (ZMod 2) σ P).trailingCoeff +
      distance (optionEquivLeft (ZMod 2) σ P).leadingCoeff ≤ distance P := by
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
  have horder : V.natTrailingDegree ≤ V.natDegree := Polynomial.natTrailingDegree_le_natDegree V
  have hneq : Q.natTrailingDegree + V.natTrailingDegree ≠ Q.natDegree + V.natDegree := by
    change Q.natTrailingDegree < Q.natDegree at hspan
    omega
  have htwo := termWeight_two_slices (P * H)
    (Q.natTrailingDegree + V.natTrailingDegree) (Q.natDegree + V.natDegree) hneq
  change termWeight ((E (P * H)).coeff (Q.natTrailingDegree + V.natTrailingDegree)) +
    termWeight ((E (P * H)).coeff (Q.natDegree + V.natDegree)) ≤ termWeight (P * H) at htwo
  have hmap : E (P * H) = Q * V := map_mul E P H
  rw [hmap, Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree,
    Polynomial.coeff_mul_degree_add_degree] at htwo
  exact (Nat.add_le_add hlow hhigh).trans htwo

/-- Endpoint slicing in any named variable. -/
theorem endpoint_distance {σ : Type*} [DecidableEq σ] (p : σ)
    (P : MvPolynomial σ (ZMod 2))
    (hspan : (coordinateEquiv p P).natTrailingDegree < (coordinateEquiv p P).natDegree) :
    distance (coordinateEquiv p P).trailingCoeff +
      distance (coordinateEquiv p P).leadingCoeff ≤ distance P := by
  have h := endpoint_distance_option
    (renameEquiv (ZMod 2) (Equiv.optionSubtypeNe p).symm P) hspan
  simpa only [distance_renameEquiv] using h

/-- Coefficient correspondence when a variable is separated off. -/
theorem coordinate_coeff_coeff {σ : Type*} [DecidableEq σ] (p : σ)
    (P : MvPolynomial σ (ZMod 2)) (d : σ →₀ ℕ) :
    MvPolynomial.coeff
        ((d.mapDomain (Equiv.optionSubtypeNe p).symm).some)
        ((coordinateEquiv p P).coeff (d p)) = MvPolynomial.coeff d P := by
  let e := (Equiv.optionSubtypeNe p).symm
  let m := d.mapDomain e
  have hnone : m none = d p := by
    dsimp [m, e]
    rw [← Equiv.optionSubtypeNe_symm_self p, Finsupp.mapDomain_apply]
    exact (Equiv.optionSubtypeNe p).symm.injective
  have h := optionEquivLeft_coeff_coeff (ZMod 2) {q : σ // q ≠ p}
    m (renameEquiv (ZMod 2) e P)
  have hr : MvPolynomial.coeff m (renameEquiv (ZMod 2) e P) = MvPolynomial.coeff d P := by
    rw [renameEquiv_apply]
    exact coeff_rename_mapDomain e e.injective P d
  rw [hnone, hr] at h
  exact h

theorem coordinate_coeff_zero {σ : Type*} [DecidableEq σ] (p : σ)
    (P : MvPolynomial σ (ZMod 2)) :
    MvPolynomial.coeff 0 ((coordinateEquiv p P).coeff 0) = MvPolynomial.coeff 0 P := by
  simpa using coordinate_coeff_coeff p P 0

theorem coordinate_coeff_pure_self {σ : Type*} [DecidableEq σ] (p : σ)
    (P : MvPolynomial σ (ZMod 2)) (k : ℕ) :
    MvPolynomial.coeff 0 ((coordinateEquiv p P).coeff k) =
      MvPolynomial.coeff (Finsupp.single p k) P := by
  simpa [Finsupp.mapDomain_single, Equiv.optionSubtypeNe_symm_self,
    Finsupp.some_single_none] using coordinate_coeff_coeff p P (Finsupp.single p k)

theorem coordinate_coeff_pure_of_ne {σ : Type*} [DecidableEq σ] (p q : σ)
    (hqp : q ≠ p) (P : MvPolynomial σ (ZMod 2)) (k : ℕ) :
    MvPolynomial.coeff (Finsupp.single (⟨q, hqp⟩ : {q : σ // q ≠ p}) k)
      ((coordinateEquiv p P).coeff 0) = MvPolynomial.coeff (Finsupp.single q k) P := by
  simpa [Finsupp.mapDomain_single, Equiv.optionSubtypeNe_symm_of_ne hqp,
    Finsupp.some_single_some, hqp, hqp.symm] using
      coordinate_coeff_coeff p P (Finsupp.single q k)

universe u

private theorem pure_endpoints_distance_by_card (n : ℕ) :
    ∀ {σ : Type u} [DecidableEq σ] (S : Finset σ), S.card = n →
      ∀ P : MvPolynomial σ (ZMod 2), MvPolynomial.coeff 0 P ≠ 0 →
        (∀ p ∈ S, ∃ k : ℕ, 0 < k ∧ MvPolynomial.coeff (Finsupp.single p k) P ≠ 0) →
        S.card + 1 ≤ distance P := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro σ inst S hcard P h0 hpure
    by_cases hS : S.Nonempty
    · obtain ⟨p, hp⟩ := hS
      let T := S.subtype (fun q => q ≠ p)
      let Q := coordinateEquiv p P
      let A := Q.coeff 0
      have hTcard : T.card + 1 = S.card := by
        dsimp [T]
        rw [Finset.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem hp]
        have hSp : 0 < S.card := Finset.card_pos.mpr ⟨p, hp⟩
        omega
      have hTlt : T.card < n := by omega
      have hA0 : MvPolynomial.coeff 0 A ≠ 0 := by
        change MvPolynomial.coeff 0 ((coordinateEquiv p P).coeff 0) ≠ 0
        rw [coordinate_coeff_zero]
        exact h0
      have hApure : ∀ q ∈ T, ∃ k : ℕ, 0 < k ∧
          MvPolynomial.coeff (Finsupp.single q k) A ≠ 0 := by
        intro q hq
        have hqS : q.val ∈ S := Finset.mem_subtype.mp hq
        obtain ⟨k, hk, hc⟩ := hpure q.val hqS
        refine ⟨k, hk, ?_⟩
        change MvPolynomial.coeff (Finsupp.single q k) ((coordinateEquiv p P).coeff 0) ≠ 0
        rw [coordinate_coeff_pure_of_ne p q.val q.property P k]
        exact hc
      have hAbound := ih T.card hTlt T rfl A hA0 hApure
      have hQ0 : Q.coeff 0 ≠ 0 := by
        intro hz
        apply hA0
        change MvPolynomial.coeff 0 (Q.coeff 0) = 0
        rw [hz, MvPolynomial.coeff_zero]
      have hQne : Q ≠ 0 := by
        intro hz
        exact hQ0 (by rw [hz, Polynomial.coeff_zero])
      obtain ⟨k, hk, hc⟩ := hpure p hp
      have hQk : Q.coeff k ≠ 0 := by
        intro hz
        have hco := coordinate_coeff_pure_self p P k
        change MvPolynomial.coeff 0 (Q.coeff k) = _ at hco
        rw [hz, MvPolynomial.coeff_zero] at hco
        exact hc hco.symm
      have hdeg := Polynomial.le_natDegree_of_ne_zero hQk
      have htrail : Q.natTrailingDegree = 0 :=
        Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hQ0)
      have hspan : Q.natTrailingDegree < Q.natDegree := by omega
      have hend := endpoint_distance p P hspan
      have htc : Q.trailingCoeff = A := by
        rw [Polynomial.trailingCoeff, htrail]
      have hlead : Q.leadingCoeff ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.mp hQne
      have hleadbound := distance_pos hlead
      change distance Q.trailingCoeff + distance Q.leadingCoeff ≤ distance P at hend
      rw [htc] at hend
      omega
    · have hSempt : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have hP : P ≠ 0 := by
        intro hz
        exact h0 (by rw [hz, MvPolynomial.coeff_zero])
      have hbound := distance_pos hP
      have hScard : S.card = 0 := by rw [hSempt]; rfl
      omega

/-- Paper, endpoint bound: a nonzero constant and positive pure powers in
`s` distinct variables force every nonzero multiple to have at least `s+1`
terms. Mixed monomials in the polynomial are allowed. -/
theorem pure_endpoints_distance {σ : Type*} [DecidableEq σ] (S : Finset σ)
    (P : MvPolynomial σ (ZMod 2)) (h0 : MvPolynomial.coeff 0 P ≠ 0)
    (hpure : ∀ p ∈ S, ∃ k : ℕ, 0 < k ∧
      MvPolynomial.coeff (Finsupp.single p k) P ≠ 0) :
    S.card + 1 ≤ distance P :=
  pure_endpoints_distance_by_card S.card S rfl P h0 hpure

theorem pure_endpoints_weight_mul {σ : Type*} [DecidableEq σ] (S : Finset σ)
    (P H : MvPolynomial σ (ZMod 2)) (h0 : MvPolynomial.coeff 0 P ≠ 0)
    (hpure : ∀ p ∈ S, ∃ k : ℕ, 0 < k ∧
      MvPolynomial.coeff (Finsupp.single p k) P ≠ 0)
    (hH : H ≠ 0) : S.card + 1 ≤ termWeight (P * H) :=
  (pure_endpoints_distance S P h0 hpure).trans (distance_le_weight_mul P H hH)

/-- A polynomial with at least two terms has distance at least two. -/
theorem nonmonomial_distance_two {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ (ZMod 2)) (hP : 2 ≤ termWeight P) :
    2 ≤ distance P := by
  classical
  have hcard : 1 < P.support.card := by change 2 ≤ P.support.card at hP; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  have hdiff : ¬ ∀ q, a q = b q := fun h => hab (Finsupp.ext h)
  obtain ⟨q, hq⟩ := not_forall.mp hdiff
  let Q := coordinateEquiv q P
  have haQ : a q ∈ Q.support := by
    rw [support_coordinateEquiv]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hbQ : b q ∈ Q.support := by
    rw [support_coordinateEquiv]
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have halo := Polynomial.natTrailingDegree_le_of_mem_supp (a q) haQ
  have hblo := Polynomial.natTrailingDegree_le_of_mem_supp (b q) hbQ
  have hahi := Polynomial.le_natDegree_of_mem_supp (a q) haQ
  have hbhi := Polynomial.le_natDegree_of_mem_supp (b q) hbQ
  have hspan : Q.natTrailingDegree < Q.natDegree := by omega
  have hQ : Q ≠ 0 := by
    intro hz
    simpa [hz] using haQ
  have hlow : 0 < distance Q.trailingCoeff :=
    distance_pos (mt Polynomial.trailingCoeff_eq_zero.mp hQ)
  have hhigh : 0 < distance Q.leadingCoeff :=
    distance_pos (mt Polynomial.leadingCoeff_eq_zero.mp hQ)
  have hend := endpoint_distance q P hspan
  change distance Q.trailingCoeff + distance Q.leadingCoeff ≤ distance P at hend
  omega

/-- Paper, elementary reductions (c): a nonzero multiple of a nonmonomial
has at least two terms. -/
theorem nonmonomial_weight_mul_two {σ : Type*} [DecidableEq σ]
    (P H : MvPolynomial σ (ZMod 2)) (hP : 2 ≤ termWeight P) (hH : H ≠ 0) :
    2 ≤ termWeight (P * H) :=
  (nonmonomial_distance_two P hP).trans (distance_le_weight_mul P H hH)

private theorem pure_powers_distance_by_card (n : ℕ) :
    ∀ {σ : Type u} [DecidableEq σ] (S : Finset σ), S.card = n →
      ∀ P : MvPolynomial σ (ZMod 2),
        (∀ p ∈ S, ∃ k : ℕ, 0 < k ∧ MvPolynomial.coeff (Finsupp.single p k) P ≠ 0) →
        S.card ≤ distance P := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro σ inst S hcard P hpure
    by_cases hS : S.Nonempty
    · obtain ⟨p, hp⟩ := hS
      obtain ⟨k, hk, hc⟩ := hpure p hp
      have hPne : P ≠ 0 := by
        intro hz
        exact hc (by rw [hz, MvPolynomial.coeff_zero])
      by_cases hsmall : S.card ≤ 1
      · exact hsmall.trans (Nat.succ_le_iff.mpr (distance_pos hPne))
      · let T := S.subtype (fun q => q ≠ p)
        let Q := coordinateEquiv p P
        let A := Q.coeff 0
        have hTcard : T.card + 1 = S.card := by
          dsimp [T]
          rw [Finset.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem hp]
          have hSp : 0 < S.card := Finset.card_pos.mpr ⟨p, hp⟩
          omega
        have hTlt : T.card < n := by omega
        have hApure : ∀ q ∈ T, ∃ k : ℕ, 0 < k ∧
            MvPolynomial.coeff (Finsupp.single q k) A ≠ 0 := by
          intro q hq
          have hqS : q.val ∈ S := Finset.mem_subtype.mp hq
          obtain ⟨j, hj, hcj⟩ := hpure q.val hqS
          refine ⟨j, hj, ?_⟩
          change MvPolynomial.coeff (Finsupp.single q j) ((coordinateEquiv p P).coeff 0) ≠ 0
          rw [coordinate_coeff_pure_of_ne p q.val q.property P j]
          exact hcj
        have hAbound := ih T.card hTlt T rfl A hApure
        have hTpos : 0 < T.card := by omega
        obtain ⟨q, hq⟩ := Finset.card_pos.mp hTpos
        obtain ⟨j, hj, hcj⟩ := hApure q hq
        have hQ0 : Q.coeff 0 ≠ 0 := by
          intro hz
          exact hcj (by change MvPolynomial.coeff _ (Q.coeff 0) = 0; rw [hz, MvPolynomial.coeff_zero])
        have hQne : Q ≠ 0 := by
          intro hz
          exact hQ0 (by rw [hz, Polynomial.coeff_zero])
        have hQk : Q.coeff k ≠ 0 := by
          intro hz
          have hco := coordinate_coeff_pure_self p P k
          change MvPolynomial.coeff 0 (Q.coeff k) = _ at hco
          rw [hz, MvPolynomial.coeff_zero] at hco
          exact hc hco.symm
        have hdeg := Polynomial.le_natDegree_of_ne_zero hQk
        have htrail : Q.natTrailingDegree = 0 :=
          Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hQ0)
        have hspan : Q.natTrailingDegree < Q.natDegree := by omega
        have hend := endpoint_distance p P hspan
        have htc : Q.trailingCoeff = A := by rw [Polynomial.trailingCoeff, htrail]
        have hlead : Q.leadingCoeff ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.mp hQne
        have hleadbound := distance_pos hlead
        change distance Q.trailingCoeff + distance Q.leadingCoeff ≤ distance P at hend
        rw [htc] at hend
        omega
    · have hSempt : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [hSempt]

/-- Positive pure powers in `s` distinct variables force distance at least
`s`, without requiring a constant term. This includes a sum of fresh variables. -/
theorem pure_powers_distance {σ : Type*} [DecidableEq σ] (S : Finset σ)
    (P : MvPolynomial σ (ZMod 2))
    (hpure : ∀ p ∈ S, ∃ k : ℕ, 0 < k ∧
      MvPolynomial.coeff (Finsupp.single p k) P ≠ 0) :
    S.card ≤ distance P :=
  pure_powers_distance_by_card S.card S rfl P hpure

theorem pure_powers_weight_mul {σ : Type*} [DecidableEq σ] (S : Finset σ)
    (P H : MvPolynomial σ (ZMod 2))
    (hpure : ∀ p ∈ S, ∃ k : ℕ, 0 < k ∧
      MvPolynomial.coeff (Finsupp.single p k) P ≠ 0)
    (hH : H ≠ 0) : S.card ≤ termWeight (P * H) :=
  (pure_powers_distance S P hpure).trans (distance_le_weight_mul P H hH)

end Pilz
