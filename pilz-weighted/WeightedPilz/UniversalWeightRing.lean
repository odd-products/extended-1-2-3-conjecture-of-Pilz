import Mathlib.Algebra.MonoidAlgebra.Lift

/-! The universal Laurent weight ring and evaluation at arbitrary units. -/

noncomputable section
namespace WeightedPilz
open scoped BigOperators

abbrev UniversalWeightRing (n : ℕ) := AddMonoidAlgebra ℤ (Fin n →₀ ℤ)

def universalWeightGenerator (n : ℕ) (i : Fin n) : (UniversalWeightRing n)ˣ where
  val := AddMonoidAlgebra.single (Finsupp.single i 1) 1
  inv := AddMonoidAlgebra.single (-Finsupp.single i 1) 1
  val_inv := by simp [AddMonoidAlgebra.one_def]
  inv_val := by simp [AddMonoidAlgebra.one_def]

def universalWeights (n a : ℕ) : UniversalWeightRing n :=
  if h : a - 1 < n then universalWeightGenerator n ⟨a - 1, h⟩ else 1

theorem universalWeights_isUnit (n a : ℕ) : IsUnit (universalWeights n a) := by
  unfold universalWeights
  split_ifs
  · exact Units.isUnit _
  · exact isUnit_one

def universalExponentEvaluation {R : Type*} [CommRing R] {n : ℕ}
    (u : Fin n → Rˣ) : Multiplicative (Fin n →₀ ℤ) →* Rˣ where
  toFun e := ∏ i, u i ^ (Multiplicative.toAdd e) i
  map_one' := by simp
  map_mul' e f := by
    simp only [toAdd_mul, Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]

def universalWeightSpecialization {R : Type*} [CommRing R] {n : ℕ}
    (u : Fin n → Rˣ) : UniversalWeightRing n →+* R :=
  AddMonoidAlgebra.liftNCRingHom (Int.castRingHom R)
    ((Units.coeHom R).comp (universalExponentEvaluation u)) (fun _ _ => Commute.all _ _)

@[simp] theorem universalWeightSpecialization_generator {R : Type*} [CommRing R] {n : ℕ}
    (u : Fin n → Rˣ) (i : Fin n) :
    universalWeightSpecialization u (universalWeightGenerator n i) = u i := by
  classical
  simp [universalWeightSpecialization, universalWeightGenerator, universalExponentEvaluation,
    Finsupp.single_apply]

@[simp] theorem universalWeightSpecialization_weight {R : Type*} [CommRing R] {n : ℕ}
    (u : Fin n → Rˣ) (a : ℕ) :
    universalWeightSpecialization u (universalWeights n a) =
      if h : a - 1 < n then (u ⟨a - 1, h⟩ : R) else 1 := by
  unfold universalWeights
  split_ifs <;> simp

theorem universalWeightSpecialization_index {R : Type*} [CommRing R] {n : ℕ}
    (u : Fin n → Rˣ) (i : Fin n) :
    universalWeightSpecialization u (universalWeights n (i.val + 1)) = u i := by
  rw [universalWeightSpecialization_weight]
  simp only [Nat.add_sub_cancel, dif_pos i.isLt]

end WeightedPilz

