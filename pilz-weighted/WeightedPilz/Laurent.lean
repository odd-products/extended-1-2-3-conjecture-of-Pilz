import WeightedPilz.Distance
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Data.Finset.Lattice.Fold

/-! Faithful Laurent embedding and clearing the finite negative exponent support. -/

noncomputable section
namespace WeightedPilz

variable {σ K : Type*} [DecidableEq σ] [Field K]

abbrev LaurentPoly (σ K : Type*) [Semiring K] := AddMonoidAlgebra K (σ →₀ ℤ)

def integerExponent : (σ →₀ ℕ) →+ (σ →₀ ℤ) where
  toFun d := Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) d
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] theorem integerExponent_apply (d : σ →₀ ℕ) (i : σ) :
    integerExponent d i = (d i : ℤ) := rfl

theorem integerExponent_injective : Function.Injective (integerExponent (σ := σ)) := by
  intro a b hab
  ext i
  exact Int.ofNat_inj.mp (congrArg (fun d : σ →₀ ℤ => d i) hab)

def toLaurent : MvPolynomial σ K →+* LaurentPoly σ K :=
  AddMonoidAlgebra.mapDomainRingHom K integerExponent

theorem toLaurent_eq_mapDomain (P : MvPolynomial σ K) :
    toLaurent P = Finsupp.mapDomain integerExponent P := rfl

theorem toLaurent_injective : Function.Injective (toLaurent (σ := σ) (K := K)) :=
  Finsupp.mapDomain_injective integerExponent_injective

@[simp] theorem toLaurent_eq_zero (P : MvPolynomial σ K) : toLaurent P = 0 ↔ P = 0 :=
  map_eq_zero_iff _ toLaurent_injective

theorem support_toLaurent (P : MvPolynomial σ K) :
    (toLaurent P).support = P.support.image integerExponent := by
  classical
  exact Finsupp.mapDomain_support_of_injective integerExponent_injective P

theorem card_support_toLaurent (P : MvPolynomial σ K) :
    (toLaurent P).support.card = weight P := by
  classical
  rw [support_toLaurent]
  exact Finset.card_image_of_injective _ integerExponent_injective

theorem card_support_laurent_translate (e : σ →₀ ℤ) (H : LaurentPoly σ K) :
    ((AddMonoidAlgebra.single e (1 : K)) * H).support.card = H.support.card := by
  rw [AddMonoidAlgebra.support_single_mul H 1 (by simp) e]
  exact Finset.card_map _

private theorem translate_eq_mapDomain (e : σ →₀ ℤ) (H : LaurentPoly σ K) :
    (AddMonoidAlgebra.single e (1 : K)) * H = Finsupp.mapDomain (e + ·) H := by
  classical
  induction H using Finsupp.induction with
  | zero => simp
  | @single_add d a H hd ha ih =>
      rw [mul_add, Finsupp.mapDomain_add, ih]
      simp only [AddMonoidAlgebra.single_mul_single, one_mul, Finsupp.mapDomain_single]

/-- A finite Laurent support can be translated into nonnegative exponents. -/
theorem exists_laurent_clearing (H : LaurentPoly σ K) (hH : H ≠ 0) :
    ∃ (e : σ →₀ ℤ) (Q : MvPolynomial σ K),
      Q ≠ 0 ∧ toLaurent Q = (AddMonoidAlgebra.single e (1 : K)) * H := by
  classical
  have hs : H.support.Nonempty := Finsupp.support_nonempty_iff.mpr hH
  let m : σ →₀ ℤ := H.support.inf' hs id
  let e : σ →₀ ℤ := -m
  let f : (σ →₀ ℤ) → (σ →₀ ℕ) := fun d =>
    Finsupp.mapRange Int.toNat (by simp) (e + d)
  let Q : MvPolynomial σ K := Finsupp.mapDomain f H
  have he : ∀ d ∈ H.support, ∀ i, 0 ≤ (e + d) i := by
    intro d hd i
    have hmd : m ≤ d := Finset.inf'_le id hd
    have hi := hmd i
    change 0 ≤ -m i + d i
    omega
  have hf : ∀ d ∈ H.support, integerExponent (f d) = e + d := by
    intro d hd
    ext i
    exact Int.toNat_of_nonneg (he d hd i)
  have hQ : toLaurent Q = (AddMonoidAlgebra.single e (1 : K)) * H := by
    rw [translate_eq_mapDomain, toLaurent_eq_mapDomain]
    change Finsupp.mapDomain integerExponent (Finsupp.mapDomain f H) = _
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr hf
  refine ⟨e, Q, ?_, hQ⟩
  intro hz
  have hcard := card_support_laurent_translate e H
  rw [← hQ, hz, map_zero, Finsupp.support_zero, Finset.card_empty] at hcard
  exact (Finset.card_ne_zero.mpr hs) hcard.symm

/-- Every polynomial support lower bound extends to all Laurent multipliers. -/
theorem laurent_bound_of_polynomial_bound (P : MvPolynomial σ K) (n : ℕ)
    (hbound : ∀ Q : MvPolynomial σ K, Q ≠ 0 → n ≤ weight (P * Q))
    (H : LaurentPoly σ K) (hH : H ≠ 0) :
    n ≤ (toLaurent P * H).support.card := by
  obtain ⟨e, Q, hQ, hclear⟩ := exists_laurent_clearing H hH
  have hb := hbound Q hQ
  rw [← card_support_toLaurent, map_mul, hclear, mul_left_comm,
    card_support_laurent_translate] at hb
  exact hb

private theorem exists_laurent_multiple_weight (P : LaurentPoly σ K) :
    ∃ m : ℕ, ∃ H : LaurentPoly σ K, H ≠ 0 ∧ (P * H).support.card = m :=
  ⟨P.support.card, 1, one_ne_zero, by simp⟩

def laurentDistance (P : LaurentPoly σ K) : ℕ := by
  classical
  exact Nat.find (exists_laurent_multiple_weight P)

theorem exists_weight_eq_laurentDistance (P : LaurentPoly σ K) :
    ∃ H : LaurentPoly σ K, H ≠ 0 ∧ (P * H).support.card = laurentDistance P := by
  classical
  exact Nat.find_spec (exists_laurent_multiple_weight P)

theorem laurentDistance_le_weight_mul (P H : LaurentPoly σ K) (hH : H ≠ 0) :
    laurentDistance P ≤ (P * H).support.card := by
  classical
  exact Nat.find_min' (exists_laurent_multiple_weight P) ⟨H, hH, rfl⟩

/-- Polynomial and Laurent distances agree, including their attained minima. -/
theorem laurentDistance_toLaurent (P : MvPolynomial σ K) :
    laurentDistance (toLaurent P) = distance P := by
  apply Nat.le_antisymm
  · obtain ⟨H, hH, hw⟩ := exists_weight_eq_distance P
    have hLH : toLaurent H ≠ 0 := by simpa using hH
    have h := laurentDistance_le_weight_mul (toLaurent P) (toLaurent H) hLH
    rw [← map_mul, card_support_toLaurent, hw] at h
    exact h
  · obtain ⟨H, hH, hw⟩ := exists_weight_eq_laurentDistance (toLaurent P)
    have h := laurent_bound_of_polynomial_bound P (distance P)
      (fun Q hQ => distance_le_weight_mul P Q hQ) H hH
    rwa [hw] at h

end WeightedPilz
