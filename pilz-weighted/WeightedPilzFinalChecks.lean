import WeightedPilz
import Lean.Util.CollectAxioms

/-! Final acceptance tests for the weighted manuscript.

The examples spell out the mathematical interfaces rather than checking only
declaration names. The last command selects declarations by their originating
imported WeightedPilz or Pilz module, including private and generated declarations,
and traverses their transitive dependencies with a shared visited set. It also
reports the original namespace-based inventory for continuity.
This file is a completion check only when its complete build succeeds.
-/

noncomputable section
namespace WeightedPilz.Acceptance
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u v

section Field
variable {K : Type u} [Field K]

example (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (H : Poly K) (hH : H ≠ 0) : n ≤ (interval n c * H).support.card :=
  weighted_interval n c hc H hH

example (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (H : LaurentPoly ℕ K) (hH : H ≠ 0) :
    n ≤ (toLaurent (interval n c) * H).support.card :=
  weighted_interval_laurent n c hc H hH

example (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c) :
    distance (interval n c) = n := weighted_interval_distance n c hc

example (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c) :
    laurentDistance (toLaurent (interval n c)) = n :=
  weighted_interval_laurent_distance n c hc

example (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (f : ArithmeticFunction K) (hf : f ≠ 0) :
    n ≤ (arithmeticKernel n c * f).support.card := weighted_convolution n c hc f hf

example (n : ℕ) (c : ℕ → K) (f : ArithmeticFunction K) (m : ℕ+) :
    (arithmeticKernel n c * f) m = ∑ a ∈ Finset.range n,
      if (⟨a + 1, Nat.succ_pos a⟩ : ℕ+) ∣ m then
        c (a + 1) * f (PNat.divExact m ⟨a + 1, Nat.succ_pos a⟩) else 0 :=
  interval_convolution_apply n c f m

example (n : ℕ) (c : ℕ → K) :
    (∀ H : Poly K, H ≠ 0 → n ≤ (interval n c * H).support.card) ↔
      ∀ f : ArithmeticFunction K, f ≠ 0 → n ≤ (arithmeticKernel n c * f).support.card :=
  intervalBound_iff_convolution_bound n c

example (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c) (a : ℕ+) {x : K} (hx : x ≠ 0) :
    (arithmeticKernel n c * (MonoidAlgebra.single a x : ArithmeticFunction K)).support.card = n :=
  convolution_singleton_sharpness n c hc a hx

example (n : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    n ≤ (intervalSymmetricDifference n A).card := weighted_symmetric_difference n A hA hne

end Field

section GeneralPolynomials
variable {σ : Type u} {K : Type v} [Field K] [DecidableEq σ]

example (P : MvPolynomial σ K) :
    ∃ H : MvPolynomial σ K, H ≠ 0 ∧ (P * H).support.card = distance P :=
  exists_weight_eq_distance P

example {L : Type*} [Field L] (f : K →+* L)
    (P : MvPolynomial σ K) (H : MvPolynomial σ L)
    (hPH : MvPolynomial.map f P * H ≠ 0) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      J.support ⊆ H.support ∧ (P * J).support ⊆ (MvPolynomial.map f P * H).support :=
  exists_nonzero_multiple_descent_map f P H hPH

example {L : Type*} [Field L] (f : K →+* L) (P : MvPolynomial σ K) :
    distance (MvPolynomial.map f P) = distance P := distance_map f P

example (P : MvPolynomial σ K) (hP : P ≠ 0) (r : ℕ) :
    min (weight P + r) (distance P + 2 * r) ≤ distance (iteratedCompletion P r) :=
  sharp_completion P hP r

example (P : MvPolynomial σ K) (hP : P ≠ 0) (r : ℕ)
    (hr : weight P - distance P ≤ r) : distance (iteratedCompletion P r) = weight P + r :=
  distance_iteratedCompletion_eq_weight P hP r hr

example (p : ℕ) [ExpChar K p] (S : FreshData σ K)
    (hr : weight S.C - distance S.C < S.vars.card) (hsize : 3 ≤ weight S.C + S.vars.card)
    (G : MvPolynomial σ K) (hG : G ≠ 0) (hdvd : S.F ∣ G) (hmin : weight G = distance S.F) :
    ∃ (e : ℕ) (d : σ →₀ ℕ) (a : K), a ≠ 0 ∧ G = monomial d a * S.F ^ p ^ e :=
  S.sharp_completion_rigidity p hr hsize G hG hdvd hmin

example (V : Finset σ) (hV : V.Nonempty) (C₀ : MvPolynomial σ K)
    (hind : ∀ i ∈ V, i ∉ C₀.vars) (G : MvPolynomial σ K) (hG : G ≠ 0)
    (hdiv : (C₀ + ∑ i ∈ V, X i) ∣ G) :
    ∃ F : MvPolynomial σ K, F ≠ 0 ∧ (C₀ + ∑ i ∈ V, X i) ∣ F ∧
      weight F ≤ weight G ∧
      (∀ d ∈ F.support, ∃ e ∈ G.support, ∀ i ∉ V, d i = e i) ∧
      (∀ i ∉ V, widthOf i F ≤ widthOf i G) ∧
      ∃ (N : Finset ℕ) (A : ℕ → MvPolynomial σ K),
        (∀ n i, i ∈ V → i ∉ (A n).vars) ∧ F = ∑ n ∈ N, A n * (∑ i ∈ V, X i) ^ n :=
  Compression.scalar_support_compression V hV C₀ hind G hG hdiv

example (p e : ℕ) [ExpChar K p] (P E : MvPolynomial σ K) (α : σ →₀ ℕ)
    (hU : P ^ p ^ e * E ≠ 0)
    (hres : ∀ d ∈ (P ^ p ^ e * E).support, residueExponent (p ^ e) d = α) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      (∀ d ∈ J.support, α + scaleExponent (p ^ e) d ∈ E.support) ∧
      (∀ d ∈ (P * J).support, α + scaleExponent (p ^ e) d ∈ (P ^ p ^ e * E).support) :=
  frobenius_extraction p e P E α hU hres

example (p e : ℕ) [ExpChar K p] (P E : MvPolynomial σ K) (α : σ →₀ ℕ)
    (hU : P ^ p ^ e * E ≠ 0)
    (hres : ∀ d ∈ (P ^ p ^ e * E).support, residueExponent (p ^ e) d = α) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      (∀ i, p ^ e * widthOf i J ≤ widthOf i E) ∧
      (∀ i, p ^ e * widthOf i (P * J) ≤ widthOf i (P ^ p ^ e * E)) :=
  frobenius_extraction_width p e P E α hU hres

example (p e : ℕ) [ExpChar K p] (hq : 1 < p ^ e) (B : Finset σ)
    (P H E : MvPolynomial σ K) (α : σ →₀ ℕ) (hP : P ≠ 0) (hH : H ≠ 0)
    (hpos : 0 < totalWidth B H) (hclass : residuePart (p ^ e) (P ^ p ^ e * E) α ≠ 0)
    (hwidth : ∀ i ∈ B, widthOf i (P ^ p ^ e * E) ≤
      widthOf i (P * H) + (p ^ e - 1) * widthOf i P) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      weight (P * J) ≤ weight (residuePart (p ^ e) (P ^ p ^ e * E) α) ∧
      p ^ e * totalWidth B J ≤ totalWidth B H ∧ totalWidth B J < totalWidth B H :=
  frobenius_strict_width_extraction p e hq B P H E α hP hH hpos hclass hwidth

example (p e : ℕ) [ExpChar K p] (P : MvPolynomial σ K) :
    distance (P ^ p ^ e) = distance P := distance_pow_expChar p e P

example (p : σ) (P Q : MvPolynomial σ K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    widthOf p (P * Q) = widthOf p P + widthOf p Q := widthOf_mul p hP hQ

example (P : MvPolynomial σ K) (hP : P ≠ 0) :
    affineDimension P + 1 ≤ distance P := affineDimension_add_one_le_distance P hP

example (P : MvPolynomial σ K) (hP : P ≠ 0) (H : LaurentPoly σ K) (hH : H ≠ 0) :
    affineDimension P + 1 ≤ (toLaurent P * H).support.card :=
  affineDimension_add_one_le_laurent_weight P hP H hH

example (a b d e : σ →₀ ℕ) (j : σ) (hj : a j ≠ b j) :
    binomialLineProjection a b j d = binomialLineProjection a b j e ↔
      ∃ t : ℚ, rationalExponent d - rationalExponent e =
        t • (rationalExponent b - rationalExponent a) :=
  binomialLineProjection_eq_iff a b d e j hj

example (F : MvPolynomial σ K) (a b : σ →₀ ℕ) (u v : K)
    (hu : u ≠ 0) (hv : v ≠ 0) (hab : a ≠ b) (j : σ) :
    2 * (F.support.image (binomialLineProjection a b j)).card ≤
      weight (F * (monomial a u + monomial b v)) :=
  weight_mul_binomial_lines F a b u v hu hv hab j

example (p : σ) (P : MvPolynomial σ K)
    (hspan : (coordinateEquiv p P).natTrailingDegree < (coordinateEquiv p P).natDegree) :
    distance (coordinateEquiv p P).trailingCoeff + distance (coordinateEquiv p P).leadingCoeff ≤
      distance P := endpoint_distance p P hspan

example (p : ℕ) [ExpChar K p] (P : MvPolynomial σ K) (hP : 2 ≤ weight P)
    {n : ℕ} (hn : 0 < n) (hnpower : ∀ e : ℕ, n ≠ p ^ e) :
    distance P + 1 ≤ weight (P ^ n) := power_gap p P hP hn hnpower

example (d : ℕ) (A : Finset (Fin (d + 1))) :
    ∃ B : Finset (Fin (d + 1)), B.card = A.card ∧
      (∀ t : ℕ, (A.filter (fun a => t ≤ a.1)).card ≤ (B.filter (fun b => t ≤ b.1)).card) ∧
      (∀ (F : Fin (d + 1) → Polynomial K) (D : ℕ), (∀ j, (F j).natDegree ≤ D) →
        (fun k => algebraMap (Polynomial K) (RatFunc K) (F k)) ∈
          Submodule.span (RatFunc K)
            (Set.range (fun a : A => SupportShift.rationalShiftMatrix (K := K) d a.1)) →
        ∀ k, (F k).coeff D ≠ 0 → k ∈ B) ∧
      (B = A → Submodule.span (RatFunc K)
        (SupportShift.rationalShiftMatrix (K := K) d '' (A : Set (Fin (d + 1)))) =
        Submodule.span (RatFunc K)
          ((fun a => Pi.single a (1 : RatFunc K)) '' (A : Set (Fin (d + 1))))) :=
  SupportShift.two_variable_shift d A

end GeneralPolynomials

section Residues
variable {σ : Type u} {K : Type v} [Field K] [DecidableEq σ]

example (S : FreshData σ K) (p : ℕ) [Fact p.Prime] [CharP K p] (N : ℕ)
    (hN : N ≤ weight S.C + S.vars.card)
    (hcounter : ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (S.F * H) < N) :
    Nonempty (S.ResidueCapacityWitness p N) := S.residue_capacities p N hN hcounter

-- The witness fixes one chosen minimum, its scalar source and quotient, and
-- full exponent-residue capacities; it does not quantify over all minima.
example (S : FreshData σ K) (p N : ℕ) (W : S.ResidueCapacityWitness p N) :
    W.H ≠ 0 ∧ weight (S.F * W.H) < N ∧ 0 < totalWidth S.C.vars W.H ∧
    (∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth S.C.vars J < totalWidth S.C.vars W.H →
      N ≤ weight (S.F * J)) ∧
    (∀ k, S.BaseOnly (W.B k)) ∧
    S.F * W.H = ∑ k ∈ W.T, W.B k * S.freshSum ^ k ∧
    W.A = S.aggregateResidueRow p W.T W.B ∧
    S.F * W.H = ∑ j ∈ Finset.range p, S.freshSum ^ j * W.A j ∧
    (∀ j < p, S.PowersInFresh p (W.A j)) ∧
    weight (S.F * W.H) = weight (W.A 0) + S.positiveResidueCost p W.A ∧
    (∀ k, S.BaseOnly (W.Q.coeff k)) ∧
    S.correction p W.A = S.F ^ p * Polynomial.eval (S.freshSum ^ p) W.Q ∧
    S.F ∣ S.correction p W.A ∧ S.F ∣ S.F * W.H - S.correction p W.A ∧
    (∀ α ∈ residueIndices p (S.correction p W.A), N ≤ residueWeight p (S.correction p W.A) α) ∧
    (∀ α, residueWeight p (S.comparison p W.A) α ≤ S.comparisonCapacity p W.A) ∧
    weight (S.F * W.H - S.correction p W.A) +
        (residueIndices p (S.correction p W.A)).card * N ≤ weight (S.F * W.H) +
      2 * ∑ α ∈ residueIndices p (S.correction p W.A), residueWeight p (S.comparison p W.A) α ∧
    (∑ α ∈ residueIndices p (S.correction p W.A), (N - residueWeight p (S.comparison p W.A) α)) +
        S.positiveResidueCost p W.A ≤ weight (S.F * W.H) ∧
    weight (S.F * W.H - S.correction p W.A) + (residueIndices p (S.correction p W.A)).card * N ≤
      weight (S.F * W.H) + 2 * (residueIndices p (S.correction p W.A)).card * S.comparisonCapacity p W.A ∧
    (residueIndices p (S.correction p W.A)).card * (N - S.comparisonCapacity p W.A) +
        S.positiveResidueCost p W.A ≤ weight (S.F * W.H) ∧
    (∀ α, residueWeight p (S.comparison p W.A) α ≤ S.positiveResidueCost p W.A →
      residuePart p (S.correction p W.A) α = 0) ∧
    (∀ κ, κ ≤ distance S.C → N ≤ S.vars.card * κ →
      0 ∈ W.T ∧ W.B 0 ≠ 0 ∧ κ ≤ weight (W.A 0) ∧ S.positiveResidueCost p W.A ≤ N - 1 - κ) :=
  ⟨W.cofactor_ne_zero, W.short, W.width_positive, W.width_minimal, W.coefficients_baseOnly,
    W.scalar_expansion, W.rows_eq, W.residue_expansion, W.rows_powers, W.weight_split, W.quotient_baseOnly,
    W.correction_factor, W.correction_dvd, W.remainder_dvd, W.correction_class_cost, W.comparison_class_capacity,
    W.exact_capacity_gain, W.exact_capacity_cost, W.uniform_capacity_gain, W.uniform_capacity_cost,
    W.protected_class, W.zero_row_budget⟩

example (S : FreshData σ K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (hcapacity : ∀ j, 0 < j → j < p → residueSigma p (S.C ^ j) ≤
      (S.vars.card + j - 1).choose j) :
    IsLeast {n : ℕ | ∃ B : ℕ → MvPolynomial σ K,
      ((∀ j < p, S.BaseOnly (B j)) ∧ (∃ j < p, B j ≠ 0) ∧
        (∑ j ∈ Finset.range p, (-S.C) ^ j * B j) = 0) ∧
      (∑ j ∈ Finset.range p, (S.vars.card + j - 1).choose j * weight (B j)) = n}
      (distance S.F) := S.finite_residue_formula p hcapacity

example (S : FreshData σ K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j < p, S.PowersInFresh p (A j)) :
    weight (∑ j ∈ Finset.range p, S.freshSum ^ j * A j) =
      ∑ j ∈ Finset.range p, (S.vars.card + j - 1).choose j * weight (A j) :=
  S.weight_aggregate_rows_lt_char p A hA

example (S : FreshData σ K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) :
    weight (S.freshSum ^ d) =
      ((Nat.digits p d).map (fun j => (S.vars.card + j - 1).choose j)).prod :=
  S.weight_freshSum_pow_digits p d

example (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (hr : 2 ≤ S.vars.card) {j : ℕ} (hj : 0 < j) :
    weight (S.freshSum ^ j) = S.vars.card ↔ ∃ e, j = p ^ e :=
  S.fresh_cost_eq_card_iff p hr hj

example (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (hr : S.vars.card = 2) (j : ℕ) :
    weight (S.freshSum ^ j) = 3 ↔ p ≠ 2 ∧ ∃ e, j = 2 * p ^ e :=
  S.two_fresh_cost_three_iff p hr j

example (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (hr : S.vars.card = 3) (j : ℕ) :
    weight (S.freshSum ^ j) = 6 ↔ p ≠ 2 ∧ ∃ e, j = 2 * p ^ e :=
  S.three_fresh_cost_six_iff p hr j

end Residues

section ModulesAndActions
variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [Module R M]

example (n : ℕ) (c : ℕ → R) :
    (∀ f : ℕ+ →₀ M, f ≠ 0 →
      n ≤ (intervalEndAction n (fun a => scalarWeightEnd (c a)) f).support.card) ↔
    ∀ a, 1 ≤ a → a ≤ n → Function.Injective (fun x : M => c a • x) :=
  intervalEndBound_scalar_iff_injective n c

example (n : ℕ) (c : ℕ → R) (hc : ∀ a, 1 ≤ a → a ≤ n → IsUnit (c a))
    (S : Finset ℕ+) (E : Finset (intervalOutputSet n S)) (hE : E.card < n) :
    ∃ L : Matrix S {i : intervalOutputSet n S // i ∉ E} R,
      L * (intervalMatrix n c S (intervalOutputSet n S)).submatrix
        (fun (i : {i : intervalOutputSet n S // i ∉ E}) => i.val) id = 1 :=
  intervalMatrix_units_erasure_inverse n c hc S E hE

example {A : Type*} [Semiring A] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : R →+* A) (Q : Matrix ι κ R) (L : Matrix κ ι R) (hL : L * Q = 1) :
    L.map f * Q.map f = 1 := matrix_left_inverse_map f Q L hL

example {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (Q : Matrix ι κ R) (L : Matrix κ ι R) (hL : L * Q = 1) (v : κ → M) :
    matrixModuleAction L (matrixModuleAction Q v) = v :=
  matrixModuleAction_leftInverse Q L hL v

example (n : ℕ) (S : Finset ℕ+) (E : Finset (intervalOutputSet n S)) (hE : E.card < n) :
    ∃ L : Matrix S {i : intervalOutputSet n S // i ∉ E}
        (AddMonoidAlgebra ℤ (Fin n →₀ ℤ)),
      L * (intervalMatrix n (universalWeights n) S (intervalOutputSet n S)).submatrix
        (fun (i : {i : intervalOutputSet n S // i ∉ E}) => i.val) id = 1 :=
  universal_erasure_inverse n S E hE

example {n : ℕ} (u : Fin n → Rˣ) (i : Fin n) :
    universalWeightSpecialization u (universalWeights n (i.val + 1)) = u i :=
  universalWeightSpecialization_index u i

example (n : ℕ) (S : Finset ℕ+) (E : Finset (intervalOutputSet n S))
    (L : Matrix S {i : intervalOutputSet n S // i ∉ E} (UniversalWeightRing n))
    (hL : L * (intervalMatrix n (universalWeights n) S (intervalOutputSet n S)).submatrix
      (fun (i : {i : intervalOutputSet n S // i ∉ E}) => i.val) id = 1)
    (f : UniversalWeightRing n →+* R) :
    L.map f * (intervalMatrix n (fun a => f (universalWeights n a)) S (intervalOutputSet n S)).submatrix
      (fun (i : {i : intervalOutputSet n S // i ∉ E}) => i.val) id = 1 :=
  universal_erasure_inverse_specializes n S E L hL f

end ModulesAndActions

example {M : Type u} [AddCommMonoid M] (n : ℕ) (φ : ℕ → AddMonoid.End M)
    (f : ℕ+ →₀ M) (m : ℕ+) :
    intervalEndAction n φ f m = ∑ a ∈ Finset.range n,
      if intervalIndex a ∣ m then φ (a + 1) (f (PNat.divExact m (intervalIndex a))) else 0 :=
  intervalEndAction_apply n φ f m

example {G : Type u} [AddCommGroup G] (n : ℕ) (φ : ℕ → AddMonoid.End G)
    (hcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n → Function.Commute (φ a) (φ b)) :
    (∀ f : ℕ+ →₀ G, f ≠ 0 → n ≤ (intervalEndAction n φ f).support.card) ↔
      ∀ a, 1 ≤ a → a ≤ n → Function.Injective (φ a) :=
  intervalEndBound_commuting_group_iff n φ hcomm

example {M : Type u} [AddCommMonoid M] (n : ℕ) (φ : ℕ → AddMonoid.End M)
    (hcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n → Function.Commute (φ a) (φ b)) :
    (∀ f : ℕ+ →₀ M, f ≠ 0 → n ≤ (intervalEndAction n φ f).support.card) ↔
      ∀ a, 1 ≤ a → a ≤ n → ∀ x : M, φ a x = 0 → x = 0 :=
  intervalEndBound_commuting_monoid_iff n φ hcomm

example {M : Type u} [AddCommMonoid M] [Nontrivial M]
    (n : ℕ) (φ : ℕ → AddMonoid.End M)
    (hφ : ∀ a, 1 ≤ a → a ≤ n → ReflectsZero (φ a)) :
    ∃ f : ℕ+ →₀ M, f ≠ 0 ∧ (intervalEndAction n φ f).support.card = n :=
  intervalEndAction_sharp n φ hφ

example {M : Type u} [AddCommMonoid M] (n : ℕ) (φ : ℕ → AddMonoid.End M)
    (hφ : ∀ a, 1 ≤ a → a ≤ n → ReflectsZero (φ a)) (b : ℕ+) {x : M} (hx : x ≠ 0) :
    (intervalEndAction n φ (Finsupp.single b x)).support.card = n :=
  intervalEndAction_single_card_eq n φ hφ b hx

example : ReflectsZero sumToFirstEnd ∧ ¬Function.Injective sumToFirstEnd :=
  ⟨sumToFirstEnd_reflectsZero, sumToFirstEnd_not_injective⟩

example {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) (c : ℕ → R) :
    (∀ f : ℕ+ →₀ M, f ≠ 0 →
      n ≤ (intervalEndAction n (fun a => scalarWeightEnd (c a)) f).support.card) ↔
      ∀ a, 1 ≤ a → a ≤ n → ∀ x : M, c a • x = 0 → x = 0 :=
  intervalEndBound_semimodule_iff_reflectsZero n c

example :
    (∀ a, 1 ≤ a → a ≤ 4 → Function.Bijective (noncommutingWeights a)) ∧
    ¬Function.Commute (noncommutingWeights 2) (noncommutingWeights 3) ∧
    ∀ v : ℚ × ℚ, v ≠ 0 → noncommutingInput v ≠ 0 ∧
      (intervalEndAction 4 noncommutingWeights (noncommutingInput v)).support.card = 3 :=
  noncommuting_interval_counterexample

section Vector
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

example (n : ℕ) (c : ℕ → K) (hn : 0 < n) (hc : NonzeroWeights n c)
    (f : ℕ+ →₀ V) (hf : f ≠ 0) :
    n + Module.finrank K (coefficientSpan (K := K) f) ≤ (vectorInterval n c f).support.card + 1 :=
  vectorInterval_rank_bound n c hn hc f hf

example (n : ℕ) (c : ℕ → K) (hn : 0 < n) (hc : NonzeroWeights n c) (f : ℕ+ →₀ V) :
    coefficientSpan (K := K) (vectorInterval n c f) = coefficientSpan (K := K) f :=
  coefficientSpan_vectorInterval n c hn (hc 1 (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)) f

example (p ℓ : ℕ) [ExpChar K p] (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ)
    (c : ℕ → K) (hc : NonzeroWeights ℓ c) (H : Poly K) (hH : H ≠ 0)
    (hw : weight (interval ℓ c * H) = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℕ) (a : K), a ≠ 0 ∧
      interval ℓ c * H = monomial d a * interval ℓ c ^ p ^ e ∧
      H = monomial d a * interval ℓ c ^ (p ^ e - 1) :=
  prime_index_multiplier_rigidity p ℓ hℓ hthree c hc H hH hw

example (p ℓ : ℕ) [ExpChar K p] (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ)
    (c : ℕ → K) (hc : NonzeroWeights ℓ c) (H : LaurentPoly ℕ K) (hH : H ≠ 0)
    (hw : (toLaurent (interval ℓ c) * H).support.card = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℤ) (a : K), a ≠ 0 ∧
      toLaurent (interval ℓ c) * H = AddMonoidAlgebra.single d a * (toLaurent (interval ℓ c)) ^ p ^ e ∧
      H = AddMonoidAlgebra.single d a * (toLaurent (interval ℓ c)) ^ (p ^ e - 1) :=
  prime_interval_laurent_rigidity p ℓ hℓ hthree c hc H hH hw

example (p ℓ : ℕ) [ExpChar K p] (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ)
    (c : ℕ → K) (hc : NonzeroWeights ℓ c) (H : (ℕ →₀ ℤ) →₀ V)
    (hw : (vectorMul (toLaurent (interval ℓ c)) H).support.card = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℤ) (v : V), v ≠ 0 ∧
      vectorMul (toLaurent (interval ℓ c)) H =
        coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) * (toLaurent (interval ℓ c)) ^ p ^ e) ∧
      H = coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) *
        (toLaurent (interval ℓ c)) ^ (p ^ e - 1)) ∧
      ((∀ a ∈ (vectorMul (toLaurent (interval ℓ c)) H).support, ∀ i, 0 ≤ a i) → ∀ i, 0 ≤ d i) :=
  vector_prime_laurent_rigidity p ℓ hℓ hthree c hc H hw

example (p ℓ : ℕ) [ExpChar K p] (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ)
    (c : ℕ → K) (hc : NonzeroWeights ℓ c) (H : (ℕ →₀ ℤ) →₀ V) (Q : (ℕ →₀ ℕ) →₀ V)
    (hQ : vectorMul (toLaurent (interval ℓ c)) H = vectorToLaurent Q)
    (hw : (vectorMul (toLaurent (interval ℓ c)) H).support.card = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℤ) (v : V), v ≠ 0 ∧ (∀ i, 0 ≤ d i) ∧
      vectorMul (toLaurent (interval ℓ c)) H =
        coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) * (toLaurent (interval ℓ c)) ^ p ^ e) ∧
      H = coefficientEmbed v (AddMonoidAlgebra.single d (1 : K) *
        (toLaurent (interval ℓ c)) ^ (p ^ e - 1)) :=
  vector_prime_polynomial_output_rigidity p ℓ hℓ hthree c hc H Q hQ hw

example [CharZero K] (ℓ : ℕ) (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ)
    (c : ℕ → K) (hc : NonzeroWeights ℓ c) (H : Poly K) (hH : H ≠ 0)
    (hw : weight (interval ℓ c * H) = ℓ) : ∃ (d : ℕ →₀ ℕ) (a : K), a ≠ 0 ∧ H = monomial d a := by
  obtain ⟨e, d, a, ha, _, hform⟩ := prime_index_multiplier_rigidity 1 ℓ hℓ hthree c hc H hH hw
  exact ⟨d, a, ha, by simpa using hform⟩

end Vector

section Roundoff

example (ℓ : ℕ) (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ)
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    (intervalSymmetricDifference ℓ A).card = ℓ ↔
      ∃ b e : ℕ, 0 < b ∧ Pilz.polynomialOf A =
        monomialOf b * interval ℓ (fun _ => (1 : ZMod 2)) ^ (2 ^ e - 1) :=
  binary_prime_equality_iff ℓ hℓ hthree A hA hne

example (n : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (b e : ℕ) (hb : 0 < b)
    (hform : Pilz.polynomialOf A =
      monomialOf b * interval n (fun _ => (1 : ZMod 2)) ^ (2 ^ e - 1)) :
    intervalSymmetricDifference n A =
      (Finset.Icc 1 n).image (fun a => b * a ^ (2 ^ e)) :=
  binary_prime_equality_output n A hA b e hb hform

example (n : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    (intervalSymmetricDifference n A).card % 2 = (n * A.card) % 2 :=
  symmetric_difference_card_mod_two n A hA

example (n : ℕ) (hn : Odd n) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) (heven : Even A.card) :
    n + 1 ≤ (intervalSymmetricDifference n A).card :=
  symmetric_difference_odd_even_bound n hn A hA hne heven

example (n : ℕ) :
    (intervalSymmetricDifference n {1, 2}).card = 2 * n - 2 * (n / 2) :=
  symmetric_difference_one_two_card n

example (n : ℕ) (hn : Odd n) :
    (intervalSymmetricDifference n {1, 2}).card = n + 1 :=
  symmetric_difference_odd_even_sharpness n hn

example {K : Type*} [Field K] (n : ℕ) (c : ℕ → K) :
    (∀ H : Poly K, H ≠ 0 → n ≤ (interval n c * H).support.card) ↔
      (∀ a ∈ Finset.Icc 1 n, c a ≠ 0) :=
  intervalBound_iff_nonzeroWeights n c

example :
    let P : Poly (ZMod 2) := 1 + X 0 + X 0 ^ 2
    let H : Poly (ZMod 2) := 1 + X 0
    weight P = 3 ∧ H ≠ 0 ∧ weight (P * H) = 2 :=
  noninterval_binary_counterexample

example {K : Type*} [Field K] (n t : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (received : ℕ+ → K) (E : Finset ℕ+)
    (hbudget : 2 * t + E.card < n) (f g : ArithmeticFunction K)
    (hf : CompatibleWithErrors (arithmeticKernel n c * f) received E t)
    (hg : CompatibleWithErrors (arithmeticKernel n c * g) received E t) : f = g :=
  weighted_convolution_errors_erasures_unique n t c hc received E hbudget f g hf hg

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (n t : ℕ) (c : ℕ → R)
    (hinj : ∀ a, 1 ≤ a → a ≤ n → Function.Injective (fun x : M => c a • x))
    (received : ℕ+ → M) (E : Finset ℕ+) (hbudget : 2 * t + E.card < n)
    (f g : ℕ+ →₀ M)
    (hf : CompatibleWithErrors
      (intervalEndAction n (fun a => scalarWeightEnd (c a)) f) received E t)
    (hg : CompatibleWithErrors
      (intervalEndAction n (fun a => scalarWeightEnd (c a)) g) received E t) : f = g :=
  module_interval_errors_erasures_unique n t c hinj received E hbudget f g hf hg

example {M : Type*} [AddCommGroup M] (n t : ℕ) (φ : ℕ → AddMonoid.End M)
    (hcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n → Function.Commute (φ a) (φ b))
    (hinj : ∀ a, 1 ≤ a → a ≤ n → Function.Injective (φ a))
    (received : ℕ+ → M) (E : Finset ℕ+) (hbudget : 2 * t + E.card < n)
    (f g : ℕ+ →₀ M)
    (hf : CompatibleWithErrors (intervalEndAction n φ f) received E t)
    (hg : CompatibleWithErrors (intervalEndAction n φ g) received E t) : f = g :=
  commuting_interval_errors_erasures_unique n t φ hcomm hinj received E hbudget f g hf hg

end Roundoff
end WeightedPilz.Acceptance

set_option maxRecDepth 100000 in
run_cmd do
  let env ← Lean.getEnv
  let moduleNames := env.header.moduleNames
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let required : Array Lean.Name := #[
    ``WeightedPilz.weighted_interval, ``WeightedPilz.weighted_interval_laurent,
    ``WeightedPilz.weighted_convolution, ``WeightedPilz.weighted_symmetric_difference,
    ``WeightedPilz.Compression.scalar_support_compression,
    ``WeightedPilz.FreshData.residue_capacities, ``WeightedPilz.FreshData.finite_residue_formula,
    ``WeightedPilz.frobenius_extraction, ``WeightedPilz.frobenius_strict_width_extraction,
    ``WeightedPilz.FreshData.sharp_completion_rigidity,
    ``WeightedPilz.intervalMatrix_units_erasure_inverse,
    ``WeightedPilz.universal_erasure_inverse, ``WeightedPilz.universal_erasure_inverse_specializes,
    ``WeightedPilz.intervalEndBound_scalar_iff_injective,
    ``WeightedPilz.intervalEndBound_commuting_group_iff,
    ``WeightedPilz.intervalEndBound_commuting_monoid_iff,
    ``WeightedPilz.intervalEndBound_semimodule_iff_reflectsZero,
    ``WeightedPilz.noncommuting_interval_counterexample,
    ``WeightedPilz.vectorInterval_rank_bound, ``WeightedPilz.vector_prime_laurent_rigidity,
    ``WeightedPilz.binary_prime_equality_iff, ``WeightedPilz.binary_prime_equality_output,
    ``WeightedPilz.symmetric_difference_card_mod_two,
    ``WeightedPilz.symmetric_difference_odd_even_bound,
    ``WeightedPilz.symmetric_difference_one_two_card,
    ``WeightedPilz.symmetric_difference_odd_even_sharpness,
    ``WeightedPilz.intervalBound_iff_nonzeroWeights,
    ``WeightedPilz.noninterval_binary_counterexample,
    ``WeightedPilz.weighted_convolution_errors_erasures_unique,
    ``WeightedPilz.module_interval_errors_erasures_unique,
    ``WeightedPilz.commuting_interval_errors_erasures_unique]
  for name in required do
    unless env.contains name do
      throwError "Final root import is missing required declaration {name}"
  let mut count := 0
  let mut earlierCount := 0
  let mut namespaceDeclarations := 0
  let mut moduleDeclarations := 0
  let mut privateDeclarations := 0
  let mut audit : Lean.CollectAxioms.State := {}
  for (name, info) in env.constants.toList do
    let inProjectNamespace :=
      name.toString.startsWith "WeightedPilz." || name.toString.startsWith "Pilz."
    let fromProjectModule := match env.getModuleIdxFor? name with
      | some idx =>
        let moduleName := moduleNames[idx.toNat]!
        (`WeightedPilz).isPrefixOf moduleName || (`Pilz).isPrefixOf moduleName
      | none => false
    if inProjectNamespace then
      namespaceDeclarations := namespaceDeclarations + 1
      match info with
      | .thmInfo _ =>
        if name.toString.startsWith "WeightedPilz." then
          count := count + 1
        else
          earlierCount := earlierCount + 1
      | _ => pure ()
      unless fromProjectModule do
        throwError "Project namespace declaration is missing from the module-origin inventory: {name}"
    if fromProjectModule then
      moduleDeclarations := moduleDeclarations + 1
      if Lean.isPrivateName name then
        privateDeclarations := privateDeclarations + 1
      let (_, next) := ((Lean.CollectAxioms.collect name).run env).run audit
      audit := next
  if count == 0 then
    throwError "No WeightedPilz theorems were loaded."
  for axiomName in audit.axioms do
    unless allowed.contains axiomName do
      throwError "Project final acceptance rejected unexpected transitive axiom: {axiomName}"
  for axiomName in allowed do
    unless audit.axioms.contains axiomName do
      throwError "Project final acceptance did not encounter expected foundational axiom: {axiomName}"
  Lean.logInfo m!"Final acceptance namespace inventory: {count} WeightedPilz theorems, {earlierCount} Pilz theorems, and {namespaceDeclarations} declarations in the two named namespaces."
  Lean.logInfo m!"Final acceptance module-origin audit: all {moduleDeclarations} declarations from imported WeightedPilz and Pilz modules, including {privateDeclarations} private declarations, and their transitive dependencies; exactly propext, Classical.choice and Quot.sound."
