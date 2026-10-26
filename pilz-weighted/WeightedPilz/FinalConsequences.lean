import WeightedPilz.FieldTheorem
import WeightedPilz.ModuleConsequences
import WeightedPilz.GroupActions
import WeightedPilz.MonoidActions
import WeightedPilz.VectorConvolution
import WeightedPilz.VectorPrimeRigidity

/-! Unconditional erasure, module/action, rank and prime-equality conclusions. -/

noncomputable section
namespace WeightedPilz
universe u v

section Modules
variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [Module R M]

theorem intervalEndBound_scalar_iff_reflectsZero (n : ℕ) (c : ℕ → R) :
    IntervalEndBound (M := M) n (fun a => scalarWeightEnd (c a)) ↔
      ∀ a, 1 ≤ a → a ≤ n → ReflectsZero (scalarWeightEnd (M := M) (c a)) :=
  intervalEndBound_scalar_iff_reflectsZero_of_field_bounds n c
    (fun K _ d hc => intervalBound_all n d hc)

theorem intervalEndBound_scalar_iff_injective (n : ℕ) (c : ℕ → R) :
    IntervalEndBound (M := M) n (fun a => scalarWeightEnd (c a)) ↔
      ∀ a, 1 ≤ a → a ≤ n → Function.Injective (fun x : M => c a • x) :=
  intervalEndBound_scalar_iff_injective_of_field_bounds n c
    (fun K _ d hc => intervalBound_all n d hc)

/-- The inverse is over the original coefficient ring, so it also applies
to the universal ring of invertible weights and every specialization. -/
theorem intervalMatrix_units_erasure_inverse (n : ℕ) (c : ℕ → R)
    (hc : ∀ a, 1 ≤ a → a ≤ n → IsUnit (c a))
    (S : Finset ℕ+) (E : Finset (intervalOutputSet n S)) (hE : E.card < n) :
    ∃ L : Matrix S {i : intervalOutputSet n S // i ∉ E} R,
      L * (intervalMatrix n c S (intervalOutputSet n S)).submatrix
        (fun (i : {i : intervalOutputSet n S // i ∉ E}) => i.val) id = 1 :=
  intervalMatrix_units_erasure_inverse_of_field_bounds n c hc
    (fun K _ d hd => intervalBound_all n d hd) S E hE

end Modules

theorem intervalEndBound_commuting_group_iff {G : Type u} [AddCommGroup G]
    (n : ℕ) (φ : ℕ → AddMonoid.End G)
    (hcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n →
      Function.Commute (φ a) (φ b)) :
    IntervalEndBound n φ ↔ ∀ a, 1 ≤ a → a ≤ n → Function.Injective (φ a) :=
  intervalEndBound_commuting_group_iff_of_field_bounds n φ hcomm
    (fun K _ d hc => intervalBound_all n d hc)

theorem intervalEndBound_commuting_monoid_iff {M : Type u} [AddCommMonoid M]
    (n : ℕ) (φ : ℕ → AddMonoid.End M)
    (hcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n →
      Function.Commute (φ a) (φ b)) :
    IntervalEndBound n φ ↔ ∀ a, 1 ≤ a → a ≤ n → ReflectsZero (φ a) :=
  intervalEndBound_commuting_monoid_iff_of_field_bounds n φ hcomm
    (fun K _ d hc => intervalBound_all n d hc)

section Vector
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

theorem vectorInterval_rank_bound (n : ℕ) (c : ℕ → K) (hn : 0 < n)
    (hc : NonzeroWeights n c) (f : ℕ+ →₀ V) (hf : f ≠ 0) :
    n + Module.finrank K (coefficientSpan (K := K) f) ≤
      (vectorInterval n c f).support.card + 1 :=
  vectorInterval_rank_bound_of_intervalBound n c hn hc (intervalBound_all n c hc) f hf

theorem prime_index_multiplier_rigidity (p ℓ : ℕ) [ExpChar K p]
    (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ) (c : ℕ → K) (hc : NonzeroWeights ℓ c)
    (H : Poly K) (hH : H ≠ 0) (hw : weight (interval ℓ c * H) = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℕ) (a : K), a ≠ 0 ∧
      interval ℓ c * H = MvPolynomial.monomial d a * interval ℓ c ^ p ^ e ∧
      H = MvPolynomial.monomial d a * interval ℓ c ^ (p ^ e - 1) :=
  prime_index_multiplier_rigidity_of_predecessor_bound p ℓ hℓ hthree c hc
    (intervalBound_all (ℓ - 1) c (nonzeroWeights_restrict hc (Nat.sub_le _ _))) H hH hw

theorem prime_interval_laurent_rigidity (p ℓ : ℕ) [ExpChar K p]
    (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ) (c : ℕ → K) (hc : NonzeroWeights ℓ c)
    (H : LaurentPoly ℕ K) (hH : H ≠ 0)
    (hw : (toLaurent (interval ℓ c) * H).support.card = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℤ) (a : K), a ≠ 0 ∧
      toLaurent (interval ℓ c) * H =
        AddMonoidAlgebra.single d a * (toLaurent (interval ℓ c)) ^ p ^ e ∧
      H = AddMonoidAlgebra.single d a * (toLaurent (interval ℓ c)) ^ (p ^ e - 1) :=
  prime_interval_laurent_rigidity_of_predecessor_bound p ℓ hℓ hthree c hc
    (intervalBound_all (ℓ - 1) c (nonzeroWeights_restrict hc (Nat.sub_le _ _))) H hH hw

theorem vector_prime_laurent_rigidity (p ℓ : ℕ) [ExpChar K p]
    (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ) (c : ℕ → K) (hc : NonzeroWeights ℓ c)
    (H : (ℕ →₀ ℤ) →₀ V)
    (hw : (vectorMul (toLaurent (interval ℓ c)) H).support.card = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℤ) (v : V), v ≠ 0 ∧
      vectorMul (toLaurent (interval ℓ c)) H =
        coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) *
          (toLaurent (interval ℓ c)) ^ p ^ e) ∧
      H = coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) *
          (toLaurent (interval ℓ c)) ^ (p ^ e - 1)) ∧
      ((∀ a ∈ (vectorMul (toLaurent (interval ℓ c)) H).support, ∀ i, 0 ≤ a i) →
        ∀ i, 0 ≤ d i) :=
  vector_prime_laurent_rigidity_of_interval_bounds p ℓ hℓ hthree c hc
    (intervalBound_all (ℓ - 1) c (nonzeroWeights_restrict hc (Nat.sub_le _ _)))
    (intervalBound_all ℓ c hc) H hw

theorem vector_prime_polynomial_output_rigidity (p ℓ : ℕ) [ExpChar K p]
    (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ) (c : ℕ → K) (hc : NonzeroWeights ℓ c)
    (H : (ℕ →₀ ℤ) →₀ V) (Q : (ℕ →₀ ℕ) →₀ V)
    (hQ : vectorMul (toLaurent (interval ℓ c)) H = vectorToLaurent Q)
    (hw : (vectorMul (toLaurent (interval ℓ c)) H).support.card = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℤ) (v : V), v ≠ 0 ∧ (∀ i, 0 ≤ d i) ∧
      vectorMul (toLaurent (interval ℓ c)) H =
        coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) *
          (toLaurent (interval ℓ c)) ^ p ^ e) ∧
      H = coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) *
          (toLaurent (interval ℓ c)) ^ (p ^ e - 1)) :=
  vector_prime_polynomial_output_rigidity_of_interval_bounds p ℓ hℓ hthree c hc
    (intervalBound_all (ℓ - 1) c (nonzeroWeights_restrict hc (Nat.sub_le _ _)))
    (intervalBound_all ℓ c hc) H Q hQ hw

end Vector
end WeightedPilz
