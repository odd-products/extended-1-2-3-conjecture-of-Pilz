import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maximal

/-!
A general algebraic step towards the universal erasure inverse in the frozen
manuscript. A finite matrix which is injective over every maximal residue field
has a left inverse over the original commutative ring.

This file proves the matrix criterion itself. Application to the interval
matrix requires the weighted field theorem and is a separate obligation.
-/

namespace WeightedPilz

open Matrix

variable {R K m n : Type*}

/-- Scalar multiples of the identity obtainable as left products with `Q`. -/
def leftInverseIdeal [CommRing R] [Fintype m] [Fintype n] [DecidableEq n]
    (Q : Matrix m n R) : Ideal R where
  carrier := {r | ∃ L : Matrix n m R, L * Q = r • (1 : Matrix n n R)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨A, hA⟩ ⟨B, hB⟩
    exact ⟨A + B, by rw [Matrix.add_mul, hA, hB, add_smul]⟩
  smul_mem' := by
    rintro a b ⟨B, hB⟩
    exact ⟨a • B, by rw [Matrix.smul_mul, hB, smul_smul]; rfl⟩

/-- Adjugates put every determinant of a square left product in the ideal. -/
theorem det_mul_mem_leftInverseIdeal [CommRing R] [Fintype m] [Fintype n]
    [DecidableEq n] (Q : Matrix m n R) (B : Matrix n m R) :
    (B * Q).det ∈ leftInverseIdeal Q := by
  refine ⟨(B * Q).adjugate * B, ?_⟩
  rw [Matrix.mul_assoc, Matrix.adjugate_mul]

/-- An injective finite matrix over a field admits a left inverse. -/
theorem matrix_exists_left_inverse_of_injective [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (Q : Matrix m n K)
    (hQ : Function.Injective Q.mulVec) :
    ∃ L : Matrix n m K, L * Q = 1 := by
  obtain ⟨g, hg⟩ := Q.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hQ)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
  exact hg

/-- Injectivity over every maximal residue field gives a left inverse over the
ring. No domain or Noetherian hypothesis is required. -/
theorem matrix_exists_left_inverse_of_residue_injective [CommRing R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Q : Matrix m n R)
    (hQ : ∀ (I : Ideal R), I.IsMaximal →
      Function.Injective (Q.map (Ideal.Quotient.mk I)).mulVec) :
    ∃ L : Matrix n m R, L * Q = 1 := by
  classical
  have htop : leftInverseIdeal Q = ⊤ := by
    by_contra hproper
    obtain ⟨I, hI, hle⟩ := (leftInverseIdeal Q).exists_le_maximal hproper
    letI : I.IsMaximal := hI
    letI : Field (R ⧸ I) := Ideal.Quotient.field I
    obtain ⟨B, hB⟩ := matrix_exists_left_inverse_of_injective
      (Q.map (Ideal.Quotient.mk I)) (hQ I hI)
    have hlift : ∀ i j, ∃ b : R, Ideal.Quotient.mk I b = B i j := by
      intro i j
      exact Ideal.Quotient.mk_surjective (B i j)
    choose B' hB' using hlift
    have hmap : (Matrix.of B').map (Ideal.Quotient.mk I) = B := by
      ext i j
      exact hB' i j
    have hdet : Ideal.Quotient.mk I ((Matrix.of B' * Q).det) = 1 := by
      rw [RingHom.map_det]
      change ((Matrix.of B' * Q).map (Ideal.Quotient.mk I)).det = 1
      rw [Matrix.map_mul, hmap, hB, Matrix.det_one]
    have hmem := hle (det_mul_mem_leftInverseIdeal Q (Matrix.of B'))
    have hzero := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    exact one_ne_zero (hdet.symm.trans hzero)
  have hmem : (1 : R) ∈ leftInverseIdeal Q := by rw [htop]; trivial
  obtain ⟨L, hL⟩ := hmem
  exact ⟨L, by simpa only [one_smul] using hL⟩

/-- Matrix action on vectors with values in any module. -/
def matrixModuleAction {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Fintype n] (Q : Matrix m n R) (v : n → M) : m → M :=
  fun i => ∑ j, Q i j • v j

theorem matrixModuleAction_mul {M k : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Fintype m] [Fintype n]
    (A : Matrix k m R) (B : Matrix m n R) (v : n → M) :
    matrixModuleAction (A * B) v = matrixModuleAction A (matrixModuleAction B v) := by
  ext i
  simp only [matrixModuleAction, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, MulAction.mul_smul]
  exact Finset.sum_comm

@[simp]
theorem matrixModuleAction_one {M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Fintype n] [DecidableEq n] (v : n → M) :
    matrixModuleAction (1 : Matrix n n R) v = v := by
  ext i
  simp [matrixModuleAction, Matrix.one_apply]

/-- A left inverse recovers arbitrary module-valued input vectors. -/
theorem matrixModuleAction_leftInverse {M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Fintype m] [Fintype n] [DecidableEq n]
    (Q : Matrix m n R) (L : Matrix n m R) (hL : L * Q = 1) :
    Function.LeftInverse (matrixModuleAction L : (m → M) → (n → M))
      (matrixModuleAction Q) := by
  intro v
  rw [← matrixModuleAction_mul, hL, matrixModuleAction_one]

/-- Consequently the matrix acts injectively on every module. -/
theorem matrixModuleAction_injective_of_left_inverse {M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] [Fintype m] [Fintype n]
    [DecidableEq n] (Q : Matrix m n R) (L : Matrix n m R) (hL : L * Q = 1) :
    Function.Injective (matrixModuleAction Q : (n → M) → (m → M)) :=
  (matrixModuleAction_leftInverse Q L hL).injective

/-- Specializing a left inverse along any coefficient homomorphism preserves it. -/
theorem matrix_left_inverse_map {S : Type*} [Semiring R] [Semiring S]
    [Fintype m] [Fintype n] [DecidableEq n]
    (f : R →+* S) (Q : Matrix m n R) (L : Matrix n m R) (hL : L * Q = 1) :
    L.map f * Q.map f = 1 := by
  rw [← Matrix.map_mul, hL]
  exact Matrix.map_one f f.map_zero f.map_one

/-- The residue-field criterion gives injectivity with arbitrary module
coefficients. The hypothesis is explicit and has no interval-specific content. -/
theorem matrixModuleAction_injective_of_residue_injective {M : Type*}
    [CommRing R] [AddCommMonoid M] [Module R M]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Q : Matrix m n R)
    (hQ : ∀ (I : Ideal R), I.IsMaximal →
      Function.Injective (Q.map (Ideal.Quotient.mk I)).mulVec) :
    Function.Injective (matrixModuleAction Q : (n → M) → (m → M)) := by
  obtain ⟨L, hL⟩ := matrix_exists_left_inverse_of_residue_injective Q hQ
  exact matrixModuleAction_injective_of_left_inverse Q L hL

end WeightedPilz
