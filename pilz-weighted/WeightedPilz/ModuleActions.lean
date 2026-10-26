import WeightedPilz.UniversalInverse
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Finset.Card

/-!
Finitely supported interval actions with arbitrary additive monoid coefficients.
The indexing agrees with the scalar arithmetic convolution: the `a`th element
of `Finset.range n` represents the positive integer `a + 1`.

The exact singleton formula proves the necessary zero-reflection condition and
sharpness whenever every weight reflects zero. Sufficiency for general inputs
is a separate theorem and is not assumed here.
-/

namespace WeightedPilz

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {M : Type*}

/-- Positive integer corresponding to zero-based interval indexing. -/
def intervalIndex (a : ℕ) : ℕ+ := ⟨a + 1, Nat.succ_pos a⟩

theorem intervalIndex_injective : Function.Injective intervalIndex := by
  intro a b h
  have hval := congrArg (fun x : ℕ+ => (x : ℕ)) h
  exact Nat.add_right_cancel hval

/-- A map reflects zero if the only element it sends to zero is zero. -/
def ReflectsZero [AddCommMonoid M] (φ : AddMonoid.End M) : Prop :=
  ∀ x, φ x = 0 → x = 0

/-- The interval action of additive endomorphism weights on finite arithmetic inputs. -/
noncomputable def intervalEndAction [AddCommMonoid M] (n : ℕ)
    (φ : ℕ → AddMonoid.End M) (f : ℕ+ →₀ M) : ℕ+ →₀ M :=
  ∑ a ∈ Finset.range n,
    Finsupp.mapDomain (fun b => intervalIndex a * b)
      (Finsupp.mapRange (φ (a + 1)) (map_zero _) f)

/-- The support lower bound for every nonzero finite input. -/
def IntervalEndBound [AddCommMonoid M] (n : ℕ) (φ : ℕ → AddMonoid.End M) : Prop :=
  ∀ f : ℕ+ →₀ M, f ≠ 0 → n ≤ (intervalEndAction n φ f).support.card

theorem intervalEndAction_single [AddCommMonoid M] (n : ℕ)
    (φ : ℕ → AddMonoid.End M) (b : ℕ+) (v : M) :
    intervalEndAction n φ (Finsupp.single b v) =
      ∑ a ∈ Finset.range n, Finsupp.single (intervalIndex a * b) (φ (a + 1) v) := by
  simp only [intervalEndAction, Finsupp.mapRange_single, Finsupp.mapDomain_single]

/-- The divisor-sum formula for the interval endomorphism action. -/
theorem intervalEndAction_apply [AddCommMonoid M] (n : ℕ)
    (φ : ℕ → AddMonoid.End M) (f : ℕ+ →₀ M) (m : ℕ+) :
    intervalEndAction n φ f m =
      ∑ a ∈ Finset.range n, if intervalIndex a ∣ m then
        φ (a + 1) (f (PNat.divExact m (intervalIndex a))) else 0 := by
  classical
  rw [intervalEndAction, Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hd : intervalIndex a ∣ m
  · rw [if_pos hd]
    calc
      _ = Finsupp.mapDomain (fun b => intervalIndex a * b)
          (Finsupp.mapRange (φ (a + 1)) (map_zero _) f)
          (intervalIndex a * PNat.divExact m (intervalIndex a)) :=
        congrArg _ (PNat.mul_div_exact hd).symm
      _ = _ := Finsupp.mapDomain_apply (fun _ _ h => mul_left_cancel h) _ _
  · rw [if_neg hd]
    apply Finsupp.mapDomain_notin_range
    rintro ⟨b, hb⟩
    exact hd ⟨b, hb.symm⟩

/-- Coefficient maps intertwining the weights commute with the full interval action. -/
theorem intervalEndAction_naturality {V : Type*} [AddCommMonoid M] [AddCommMonoid V]
    (n : ℕ) (φ : ℕ → AddMonoid.End M) (η : ℕ → AddMonoid.End V)
    (ψ : M →+ V)
    (hψ : ∀ a ∈ Finset.range n, ∀ x, ψ (φ (a + 1) x) = η (a + 1) (ψ x))
    (f : ℕ+ →₀ M) :
    Finsupp.mapRange ψ ψ.map_zero (intervalEndAction n φ f) =
      intervalEndAction n η (Finsupp.mapRange ψ ψ.map_zero f) := by
  classical
  rw [intervalEndAction, Finsupp.mapRange_finset_sum, intervalEndAction]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finsupp.mapDomain_mapRange _ _ ψ ψ.map_zero ψ.map_add]
  apply congrArg (Finsupp.mapDomain (fun b => intervalIndex a * b))
  ext b
  exact hψ a ha (f b)

/-- A zero-reflecting coefficient homomorphism preserves exact support. -/
theorem support_mapRange_of_zeroReflecting {V α : Type*} [AddCommMonoid M]
    [AddCommMonoid V] (ψ : M →+ V) (hψ : ∀ x, ψ x = 0 → x = 0) (f : α →₀ M) :
    (Finsupp.mapRange ψ ψ.map_zero f).support = f.support := by
  ext b
  simp only [Finsupp.mem_support_iff, Finsupp.mapRange_apply]
  constructor
  · exact fun h hb => h (by rw [hb, map_zero])
  · exact fun h hb => h (hψ _ hb)

/-- Transfer a support bound back along a zero-reflecting coefficient map. This
applies in particular to injective localization maps. -/
theorem intervalEndBound_of_zeroReflecting_intertwiner {V : Type*}
    [AddCommMonoid M] [AddCommMonoid V] (n : ℕ)
    (φ : ℕ → AddMonoid.End M) (η : ℕ → AddMonoid.End V) (ψ : M →+ V)
    (hzero : ∀ x, ψ x = 0 → x = 0)
    (hψ : ∀ a ∈ Finset.range n, ∀ x, ψ (φ (a + 1) x) = η (a + 1) (ψ x))
    (hbound : IntervalEndBound n η) : IntervalEndBound n φ := by
  intro f hf
  have hf' : Finsupp.mapRange ψ ψ.map_zero f ≠ 0 := by
    intro hz
    apply hf
    ext b
    exact hzero _ (by have := congrArg (fun g : ℕ+ →₀ V => g b) hz; exact this)
  have h := hbound _ hf'
  rw [← intervalEndAction_naturality n φ η ψ hψ,
    support_mapRange_of_zeroReflecting ψ hzero] at h
  exact h

private theorem support_sum_single_injective {α β : Type*} [DecidableEq β]
    [AddCommMonoid M] (s : Finset α) (g : α → β) (hg : Function.Injective g)
    (v : α → M) :
    (∑ a ∈ s, Finsupp.single (g a) (v a)).support =
      (s.filter (fun a => v a ≠ 0)).image g := by
  classical
  rw [Finsupp.support_sum_eq_biUnion]
  · ext x
    simp only [Finset.mem_biUnion, Finsupp.mem_support_iff, Finsupp.single_apply_ne_zero,
      Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨a, ha, hxa, hva⟩
      exact ⟨a, ⟨ha, hva⟩, hxa.symm⟩
    · rintro ⟨a, ⟨ha, hva⟩, hax⟩
      exact ⟨a, ha, hax.symm, hva⟩
  · intro a b hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxa := (Finsupp.single_apply_ne_zero.mp (Finsupp.mem_support_iff.mp hx)).1
    have hxb := (Finsupp.single_apply_ne_zero.mp (Finsupp.mem_support_iff.mp hy)).1
    exact hab (hg (hxa.symm.trans hxb))

/-- Exact support of a singleton input; zero weight values are the only missing outputs. -/
theorem intervalEndAction_single_support [AddCommMonoid M] (n : ℕ)
    (φ : ℕ → AddMonoid.End M) (b : ℕ+) (v : M) :
    (intervalEndAction n φ (Finsupp.single b v)).support =
      ((Finset.range n).filter (fun a => φ (a + 1) v ≠ 0)).image
        (fun a => intervalIndex a * b) := by
  classical
  rw [intervalEndAction_single]
  apply support_sum_single_injective
  intro a a' h
  exact intervalIndex_injective (mul_right_cancel h)

/-- Exact number of outputs on a singleton input. -/
theorem intervalEndAction_single_card [AddCommMonoid M] (n : ℕ)
    (φ : ℕ → AddMonoid.End M) (b : ℕ+) (v : M) :
    (intervalEndAction n φ (Finsupp.single b v)).support.card =
      ((Finset.range n).filter (fun a => φ (a + 1) v ≠ 0)).card := by
  classical
  rw [intervalEndAction_single_support]
  apply Finset.card_image_of_injective
  intro a a' h
  exact intervalIndex_injective (mul_right_cancel h)

/-- Any sharp interval lower bound forces every active weight to reflect zero. -/
theorem reflectsZero_of_intervalEndBound [AddCommMonoid M] {n : ℕ}
    {φ : ℕ → AddMonoid.End M} (hbound : IntervalEndBound n φ)
    {a : ℕ} (ha : 1 ≤ a) (han : a ≤ n) : ReflectsZero (φ a) := by
  classical
  intro v hv
  by_contra hne
  have hinput : (Finsupp.single (1 : ℕ+) v) ≠ 0 := Finsupp.single_ne_zero.mpr hne
  have hb := hbound _ hinput
  rw [intervalEndAction_single_card] at hb
  have hlt : ((Finset.range n).filter (fun k => φ (k + 1) v ≠ 0)).card < n := by
    have hs : (Finset.range n).filter (fun k => φ (k + 1) v ≠ 0) ⊂ Finset.range n := by
      apply Finset.filter_ssubset.mpr
      refine ⟨a - 1, Finset.mem_range.mpr (by omega), ?_⟩
      simpa only [Nat.sub_add_cancel ha, not_not] using hv
    simpa only [Finset.card_range] using Finset.card_lt_card hs
  exact Nat.not_le_of_gt hlt hb

/-- Zero-reflecting weights give exactly `n` outputs on every nonzero singleton. -/
theorem intervalEndAction_single_card_eq [AddCommMonoid M] (n : ℕ)
    (φ : ℕ → AddMonoid.End M)
    (hφ : ∀ a, 1 ≤ a → a ≤ n → ReflectsZero (φ a))
    (b : ℕ+) {v : M} (hv : v ≠ 0) :
    (intervalEndAction n φ (Finsupp.single b v)).support.card = n := by
  classical
  rw [intervalEndAction_single_card]
  have hfilter : (Finset.range n).filter (fun a => φ (a + 1) v ≠ 0) = Finset.range n := by
    apply Finset.filter_eq_self.mpr
    intro a ha
    exact fun hz => hv (hφ (a + 1) (by omega) (by have := Finset.mem_range.mp ha; omega) v hz)
  rw [hfilter, Finset.card_range]

/-- Nontrivial coefficient monoids and zero-reflecting weights have a singleton
input attaining the interval size. -/
theorem intervalEndAction_sharp [AddCommMonoid M] [Nontrivial M] (n : ℕ)
    (φ : ℕ → AddMonoid.End M)
    (hφ : ∀ a, 1 ≤ a → a ≤ n → ReflectsZero (φ a)) :
    ∃ f : ℕ+ →₀ M, f ≠ 0 ∧ (intervalEndAction n φ f).support.card = n := by
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  exact ⟨Finsupp.single 1 v, Finsupp.single_ne_zero.mpr hv,
    intervalEndAction_single_card_eq n φ hφ 1 hv⟩

/-- On additive groups, reflection of zero is exactly injectivity. -/
theorem reflectsZero_iff_injective [AddCommGroup M] (φ : AddMonoid.End M) :
    ReflectsZero φ ↔ Function.Injective φ := by
  constructor
  · intro h x y hxy
    apply sub_eq_zero.mp
    apply h
    simp [map_sub, hxy]
  · intro h x hx
    exact h (hx.trans φ.map_zero.symm)

/-- Reflection of zero preserves the exact support under coefficientwise action. -/
theorem support_mapRange_of_reflectsZero [AddCommMonoid M] (φ : AddMonoid.End M)
    (hφ : ReflectsZero φ) (f : ℕ+ →₀ M) :
    (Finsupp.mapRange φ φ.map_zero f).support = f.support := by
  ext b
  simp only [Finsupp.mem_support_iff, Finsupp.mapRange_apply]
  constructor
  · exact fun h hb => h (by rw [hb, map_zero])
  · exact fun h hb => h (hφ _ hb)

/-- The one-weight interval criterion holds for arbitrary additive monoids. -/
theorem intervalEndBound_one_iff [AddCommMonoid M] (φ : ℕ → AddMonoid.End M) :
    IntervalEndBound 1 φ ↔ ReflectsZero (φ 1) := by
  constructor
  · intro h
    exact reflectsZero_of_intervalEndBound h (by decide) (by decide)
  · intro h f hf
    have haction : intervalEndAction 1 φ f = Finsupp.mapRange (φ 1) (map_zero _) f := by
      simp [intervalEndAction, intervalIndex]
      exact Finsupp.mapDomain_id
    rw [haction, support_mapRange_of_reflectsZero _ h]
    exact (Finset.card_pos.mpr (Finsupp.support_nonempty_iff.mpr hf))

/-- Scalar multiplication as an additive endomorphism. -/
def scalarWeightEnd {R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (c : R) : AddMonoid.End M where
  toFun := fun x => c • x
  map_zero' := smul_zero c
  map_add' := smul_add c

/-- The scalar-module version of the interval divisor-sum formula. -/
theorem intervalScalarAction_apply {R : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (n : ℕ) (c : ℕ → R) (f : ℕ+ →₀ M) (m : ℕ+) :
    intervalEndAction n (fun a => scalarWeightEnd (c a)) f m =
      ∑ a ∈ Finset.range n, if intervalIndex a ∣ m then
        c (a + 1) • f (PNat.divExact m (intervalIndex a)) else 0 :=
  intervalEndAction_apply n (fun a => scalarWeightEnd (c a)) f m

/-- Unit scalar weights reflect zero on every unital module. -/
theorem reflectsZero_scalarWeightEnd_of_isUnit {R : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] {c : R} (hc : IsUnit c) :
    ReflectsZero (scalarWeightEnd (M := M) c) := by
  obtain ⟨u, rfl⟩ := hc
  intro x hx
  change (↑u : R) • x = 0 at hx
  have h := congrArg (fun y : M => (↑u⁻¹ : R) • y) hx
  simpa only [← mul_smul, Units.inv_mul, one_smul, smul_zero] using h

/-- Scalar weights over a commutative semiring commute as endomorphisms. -/
theorem scalarWeightEnd_commute {R : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] (a b : R) :
    Function.Commute (scalarWeightEnd (M := M) a) (scalarWeightEnd b) := by
  intro x
  exact smul_comm a b x

/-- The manuscript's zero-reflecting, noninjective endomorphism of `ℕ²`. -/
def sumToFirstEnd : AddMonoid.End (ℕ × ℕ) where
  toFun x := (x.1 + x.2, 0)
  map_zero' := rfl
  map_add' := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    change (a + c + (b + d), 0) = (a + b + (c + d), 0 + 0)
    exact Prod.ext (by omega) rfl

theorem sumToFirstEnd_reflectsZero : ReflectsZero sumToFirstEnd := by
  rintro ⟨a, b⟩ h
  have hsum : a + b = 0 := congrArg Prod.fst h
  ext <;> dsimp <;> omega

theorem sumToFirstEnd_not_injective : ¬Function.Injective sumToFirstEnd := by
  intro h
  have heq : (1, 0) = (0, 1) := h (a₁ := (1, 0)) (a₂ := (0, 1)) rfl
  exact Nat.one_ne_zero (congrArg Prod.fst heq)

/-- The nonzero coordinates of a vector on a finite index type. -/
noncomputable def finiteVectorSupport {ι V : Type*} [Fintype ι] [Zero V] (v : ι → V) : Finset ι :=
  Finset.univ.filter (fun i => v i ≠ 0)

/-- Erasing fewer than the residue-field support bound leaves a matrix with a
left inverse over the ring itself. -/
theorem matrix_exists_erasure_left_inverse {R ι κ : Type*} [CommRing R]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Q : Matrix ι κ R) (N : ℕ)
    (hQ : ∀ (I : Ideal R), I.IsMaximal → ∀ v : κ → R ⧸ I, v ≠ 0 →
      N ≤ (finiteVectorSupport ((Q.map (Ideal.Quotient.mk I)).mulVec v)).card)
    (E : Finset ι) (hE : E.card < N) :
    ∃ L : Matrix κ {i : ι // i ∉ E} R,
      L * Q.submatrix (fun (i : {i : ι // i ∉ E}) => i.val) id = 1 := by
  classical
  let Qe : Matrix {i : ι // i ∉ E} κ R := fun i j => Q i.val j
  apply matrix_exists_left_inverse_of_residue_injective Qe
  intro I hI
  letI : I.IsMaximal := hI
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  apply (injective_iff_map_eq_zero (Qe.map (Ideal.Quotient.mk I)).mulVecLin).mpr
  intro v hv
  by_contra hvne
  have hbound := hQ I hI v hvne
  have hs : finiteVectorSupport ((Q.map (Ideal.Quotient.mk I)).mulVec v) ⊆ E := by
    intro i hi
    by_contra hin
    have hvi : (Q.map (Ideal.Quotient.mk I)).mulVec v i ≠ 0 := by
      simpa only [finiteVectorSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact hvi (congrFun hv (⟨i, hin⟩ : {i : ι // i ∉ E}))
  have hcard := Finset.card_le_card hs
  omega

/-- A residue-field support bound transfers to arbitrary module coefficients.
This is a general finite-matrix theorem; the field bound is an explicit premise
to be established separately for any concrete interval matrix. -/
theorem matrixModuleAction_support_bound {R ι κ : Type*} [CommRing R]
    [AddCommMonoid M] [Module R M] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (Q : Matrix ι κ R) (N : ℕ)
    (hQ : ∀ (I : Ideal R), I.IsMaximal → ∀ v : κ → R ⧸ I, v ≠ 0 →
      N ≤ (finiteVectorSupport ((Q.map (Ideal.Quotient.mk I)).mulVec v)).card)
    (v : κ → M) (hv : v ≠ 0) :
    N ≤ (finiteVectorSupport (matrixModuleAction Q v)).card := by
  classical
  by_contra! hshort
  let S := {i : ι // matrixModuleAction Q v i = 0}
  let Qs : Matrix S κ R := fun i j => Q i.val j
  have hres : ∀ (I : Ideal R), I.IsMaximal →
      Function.Injective (Qs.map (Ideal.Quotient.mk I)).mulVec := by
    intro I hI
    letI : I.IsMaximal := hI
    letI : Field (R ⧸ I) := Ideal.Quotient.field I
    apply (injective_iff_map_eq_zero (Qs.map (Ideal.Quotient.mk I)).mulVecLin).mpr
    intro w hw
    by_contra hwne
    have hbound := hQ I hI w hwne
    have hs : finiteVectorSupport ((Q.map (Ideal.Quotient.mk I)).mulVec w) ⊆
        finiteVectorSupport (matrixModuleAction Q v) := by
      intro i hi
      have hwi : (Q.map (Ideal.Quotient.mk I)).mulVec w i ≠ 0 := by
        simpa only [finiteVectorSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      intro hvi
      have hzero := congrFun hw (⟨i, hvi⟩ : S)
      exact hwi hzero
    have hcard := Finset.card_le_card hs
    omega
  have hinj := matrixModuleAction_injective_of_residue_injective (M := M) Qs hres
  apply hv
  apply hinj
  ext i
  change matrixModuleAction Q v i.val = ∑ j, Q i.val j • (0 : M)
  simpa only [smul_zero, Finset.sum_const_zero] using i.property

end WeightedPilz
