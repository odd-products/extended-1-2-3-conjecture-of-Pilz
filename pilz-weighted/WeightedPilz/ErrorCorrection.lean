import WeightedPilz.FinalConsequences

/-!
Errors-and-erasures uniqueness for weighted interval convolution.

Received values need not have finite support. A candidate output is compatible
when it agrees with the received values away from the erased set and a set of
at most `t` errors. The conclusions assert uniqueness, not an efficient decoder.
-/

noncomputable section
namespace WeightedPilz

/-- Agreement with received values outside finitely many erasures and at most
`t` corrupted coordinates. Values at erased coordinates are irrelevant. -/
def CompatibleWithErrors {ι M : Type*} [Zero M] (output : ι →₀ M)
    (received : ι → M) (E : Finset ι) (t : ℕ) : Prop :=
  ∃ B : Finset ι, B.card ≤ t ∧
    ∀ i, i ∉ E → i ∉ B → output i = received i

/-- The standard errors-and-erasures uniqueness argument for an additive code
whose nonzero words have support size at least `n`. -/
theorem eq_of_support_distance_of_errors_erasures {A ι M : Type*}
    [AddGroup A] [AddCommGroup M] (T : A →+ (ι →₀ M)) (n t : ℕ)
    (hdistance : ∀ x, x ≠ 0 → n ≤ (T x).support.card)
    (received : ι → M) (E : Finset ι) (hbudget : 2 * t + E.card < n)
    (f g : A) (hf : CompatibleWithErrors (T f) received E t)
    (hg : CompatibleWithErrors (T g) received E t) : f = g := by
  classical
  obtain ⟨Bf, hBf, hf⟩ := hf
  obtain ⟨Bg, hBg, hg⟩ := hg
  by_contra hne
  have hlower := hdistance (f - g) (sub_ne_zero.mpr hne)
  have hs : (T (f - g)).support ⊆ E ∪ Bf ∪ Bg := by
    intro i hi
    by_contra hnot
    have hnot' : (i ∉ E ∧ i ∉ Bf) ∧ i ∉ Bg := by
      simpa only [Finset.mem_union, not_or] using hnot
    have heq : T f i = T g i :=
      (hf i hnot'.1.1 hnot'.1.2).trans (hg i hnot'.1.1 hnot'.2).symm
    have hz : T (f - g) i = 0 := by
      rw [map_sub, Finsupp.sub_apply, heq, sub_self]
    exact (Finsupp.mem_support_iff.mp hi) hz
  have hcard := Finset.card_le_card hs
  have hfirst := Finset.card_union_le E Bf
  have hsecond := Finset.card_union_le (E ∪ Bf) Bg
  omega

/-- The interval endomorphism action as an additive homomorphism. -/
def intervalEndActionHom {M : Type*} [AddCommMonoid M] (n : ℕ)
    (φ : ℕ → AddMonoid.End M) : (ℕ+ →₀ M) →+ (ℕ+ →₀ M) where
  toFun := intervalEndAction n φ
  map_zero' := by simp [intervalEndAction]
  map_add' := by
    intro f g
    simp only [intervalEndAction, Finsupp.mapRange_add (map_add _),
      Finsupp.mapDomain_add, Finset.sum_add_distrib]

/-- An interval support bound implies errors-and-erasures uniqueness for
arbitrary finitely supported inputs in an additive group. -/
theorem intervalEndAction_errors_erasures_unique {M : Type*} [AddCommGroup M]
    (n t : ℕ) (φ : ℕ → AddMonoid.End M) (hbound : IntervalEndBound n φ)
    (received : ℕ+ → M) (E : Finset ℕ+) (hbudget : 2 * t + E.card < n)
    (f g : ℕ+ →₀ M)
    (hf : CompatibleWithErrors (intervalEndAction n φ f) received E t)
    (hg : CompatibleWithErrors (intervalEndAction n φ g) received E t) : f = g :=
  eq_of_support_distance_of_errors_erasures (intervalEndActionHom n φ)
    n t hbound received E hbudget f g hf hg

/-- Commuting injective additive weights permit unique correction whenever
twice the error budget plus the number of erasures is less than `n`. -/
theorem commuting_interval_errors_erasures_unique {M : Type*} [AddCommGroup M]
    (n t : ℕ) (φ : ℕ → AddMonoid.End M)
    (hcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n →
      Function.Commute (φ a) (φ b))
    (hinj : ∀ a, 1 ≤ a → a ≤ n → Function.Injective (φ a))
    (received : ℕ+ → M) (E : Finset ℕ+) (hbudget : 2 * t + E.card < n)
    (f g : ℕ+ →₀ M)
    (hf : CompatibleWithErrors (intervalEndAction n φ f) received E t)
    (hg : CompatibleWithErrors (intervalEndAction n φ g) received E t) : f = g :=
  intervalEndAction_errors_erasures_unique n t φ
    ((intervalEndBound_commuting_group_iff n φ hcomm).mpr hinj)
    received E hbudget f g hf hg

/-- The module version requires injectivity of the active scalar weights and
no restriction on the finite supports of the two candidate inputs. -/
theorem module_interval_errors_erasures_unique {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (n t : ℕ) (c : ℕ → R)
    (hinj : ∀ a, 1 ≤ a → a ≤ n → Function.Injective (fun x : M => c a • x))
    (received : ℕ+ → M) (E : Finset ℕ+) (hbudget : 2 * t + E.card < n)
    (f g : ℕ+ →₀ M)
    (hf : CompatibleWithErrors
      (intervalEndAction n (fun a => scalarWeightEnd (M := M) (c a)) f) received E t)
    (hg : CompatibleWithErrors
      (intervalEndAction n (fun a => scalarWeightEnd (M := M) (c a)) g) received E t) : f = g := by
  have hbound : IntervalEndBound (M := M) n (fun a => scalarWeightEnd (M := M) (c a)) :=
    (intervalEndBound_scalar_iff_injective (M := M) n c).mpr hinj
  exact intervalEndAction_errors_erasures_unique (M := M) n t
    (fun a => scalarWeightEnd (M := M) (c a)) hbound received E hbudget f g hf hg

/-- Weighted scalar convolution uniquely determines an arbitrary finite input
from received values with `t` errors and the erased set `E` if `2t + |E| < n`. -/
theorem weighted_convolution_errors_erasures_unique {K : Type*} [Field K]
    (n t : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (received : ℕ+ → K) (E : Finset ℕ+) (hbudget : 2 * t + E.card < n)
    (f g : ArithmeticFunction K)
    (hf : CompatibleWithErrors (arithmeticKernel n c * f) received E t)
    (hg : CompatibleWithErrors (arithmeticKernel n c * g) received E t) : f = g := by
  let T : ArithmeticFunction K →+ ArithmeticFunction K :=
    { toFun := fun f => arithmeticKernel n c * f
      map_zero' := mul_zero _
      map_add' := mul_add _ }
  exact eq_of_support_distance_of_errors_erasures T n t
    (weighted_convolution n c hc) received E hbudget f g hf hg

end WeightedPilz
