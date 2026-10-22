import Pilz.Endpoints
import Pilz.FreshAlgebra
import Pilz.Extremal

/-!
# The elementary distance budget from fresh variables

Each independent fresh variable adds one to the endpoint lower bound.
The argument keeps the exact distance of the core rather than merely its
nonvanishing, and is independent of square-root descent.
-/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

/-- An injective relabeling preserves the number of terms. -/
theorem termWeight_rename_of_injective {σ τ : Type*} (f : σ → τ)
    (hf : Function.Injective f) (P : MvPolynomial σ (ZMod 2)) :
    termWeight (rename f P) = termWeight P := by
  classical
  rw [termWeight, support_rename_of_injective hf]
  apply Finset.card_image_iff.mpr
  exact (Finsupp.mapDomain_injective hf).injOn

/-- Adding unused variable names cannot increase the minimum distance:
every old multiplier still provides a multiplier after relabeling. -/
theorem distance_rename_le {σ τ : Type*} (f : σ → τ)
    (hf : Function.Injective f) (P : MvPolynomial σ (ZMod 2)) :
    distance (rename f P) ≤ distance P := by
  obtain ⟨H, hH, hweight⟩ := exists_weight_eq_distance P
  have hrename : rename f H ≠ 0 := by
    intro hz
    apply hH
    apply rename_injective f hf
    simpa using hz
  have h := distance_le_weight_mul (rename f P) (rename f H) hrename
  rw [← map_mul, termWeight_rename_of_injective f hf, hweight] at h
  exact h

@[simp] theorem distance_one {σ : Type*} :
    distance (1 : MvPolynomial σ (ZMod 2)) = 1 := by
  have hle := distance_le_termWeight (1 : MvPolynomial σ (ZMod 2))
  have hpos := distance_pos (one_ne_zero : (1 : MvPolynomial σ (ZMod 2)) ≠ 0)
  have hw : termWeight (1 : MvPolynomial σ (ZMod 2)) = 1 := by
    change (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)).support.card = 1
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero]
    exact Finset.card_singleton _
  omega

private theorem coordinateEquiv_X_self (p : ℕ) :
    coordinateEquiv p (X p : Poly) = Polynomial.X := by
  simp [coordinateEquiv, optionEquivLeft_X_none]

private theorem coordinateEquiv_rename_subtype (p : ℕ)
    (P : MvPolynomial {q : ℕ // q ≠ p} (ZMod 2)) :
    coordinateEquiv p (rename Subtype.val P) = Polynomial.C P := by
  have hh : ((coordinateEquiv p).toRingHom.comp
      (rename (Subtype.val : {q : ℕ // q ≠ p} → ℕ)).toRingHom) = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coordinateEquiv, optionEquivLeft_C]
    · intro q
      simp [coordinateEquiv, Equiv.optionSubtypeNe_symm_of_ne q.property,
        optionEquivLeft_X_some]
  exact RingHom.congr_fun hh P

/-- Adding one independent fresh variable adds one to the distance budget. -/
theorem distance_add_fresh_variable (A : Poly) (p : ℕ) (hA : A ≠ 0)
    (hindependent : IndependentOf A p) :
    distance A + 1 ≤ distance (A + X p) := by
  classical
  let A0 := (coordinateEquiv p A).coeff 0
  have hdeg : A.degreeOf p = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [degreeOf_le_iff]
    intro d hd
    exact (hindependent d hd).le
  have hconst : coordinateEquiv p A = Polynomial.C A0 := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hdeg]
  have hA0 : A0 ≠ 0 := by
    intro hz
    apply coordinateEquiv_ne_zero p hA
    rw [hconst, hz, Polynomial.C_0]
  have hrecover : rename (Subtype.val : {q : ℕ // q ≠ p} → ℕ) A0 = A := by
    apply (coordinateEquiv p).injective
    rw [coordinateEquiv_rename_subtype]
    exact hconst.symm
  have hcore : distance A ≤ distance A0 := by
    rw [← hrecover]
    exact distance_rename_le Subtype.val Subtype.val_injective A0
  let Q := coordinateEquiv p (A + X p)
  have hQ : Q = Polynomial.X + Polynomial.C A0 := by
    dsimp [Q]
    rw [map_add, hconst, coordinateEquiv_X_self, add_comm]
  have hQ0 : Q.coeff 0 ≠ 0 := by
    simpa only [hQ, Polynomial.coeff_add, Polynomial.coeff_X_zero,
      Polynomial.coeff_C_zero, zero_add] using hA0
  have htrail : Q.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hQ0)
  have htop : Q.natDegree = 1 := by rw [hQ, Polynomial.natDegree_X_add_C]
  have hspan : Q.natTrailingDegree < Q.natDegree := by omega
  have hend := endpoint_distance p (A + X p) hspan
  have htc : Q.trailingCoeff = A0 := by
    rw [Polynomial.trailingCoeff, htrail]
    simp only [hQ, Polynomial.coeff_add, Polynomial.coeff_X_zero,
      Polynomial.coeff_C_zero, zero_add]
  have hlc : Q.leadingCoeff = 1 := by rw [hQ, Polynomial.leadingCoeff_X_add_C]
  change distance Q.trailingCoeff + distance Q.leadingCoeff ≤ distance (A + X p) at hend
  rw [htc, hlc, distance_one] at hend
  exact (Nat.add_le_add_right hcore 1).trans hend

private theorem independent_sum_fresh (C : Poly) (V : Finset ℕ) (p : ℕ)
    (hC : IndependentOf C p) (hp : p ∉ V) :
    IndependentOf (C + ∑ i ∈ V, (X i : Poly)) p := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hc | hs
  · exact hC d hc
  · have hmem : d ∈ V.biUnion (fun i => (X i : Poly).support) :=
      MvPolynomial.support_sum hs
    obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp hmem
    rw [MvPolynomial.support_X] at hdi
    have hd : d = Finsupp.single i 1 := Finset.mem_singleton.mp hdi
    have hpi : p ≠ i := fun h => hp (h.symm ▸ hi)
    rw [hd]
    simp [hpi]

/-- Repeated endpoint slicing gives the exact core-distance budget. -/
theorem fresh_sum_distance (V : Finset ℕ) (C : Poly) (hC : C ≠ 0)
    (hindependent : ∀ p ∈ V, IndependentOf C p) :
    distance C + V.card ≤ distance (C + ∑ i ∈ V, (X i : Poly)) := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | @insert p V hp ih =>
    have hCV : ∀ q ∈ V, IndependentOf C q :=
      fun q hq => hindependent q (Finset.mem_insert_of_mem hq)
    have hbound := ih hCV
    let A : Poly := C + ∑ i ∈ V, (X i : Poly)
    have hA : A ≠ 0 := by
      intro hz
      have hpos := distance_pos hC
      change distance C + V.card ≤ distance A at hbound
      rw [hz, distance_zero] at hbound
      omega
    have hAind : IndependentOf A p :=
      independent_sum_fresh C V p (hindependent p (Finset.mem_insert_self p V)) hp
    have hstep := distance_add_fresh_variable A p hA hAind
    have heq : C + ∑ i ∈ insert p V, (X i : Poly) = A + X p := by
      rw [Finset.sum_insert hp]
      dsimp [A]
      ac_rfl
    rw [heq, Finset.card_insert_of_notMem hp]
    change distance C + V.card ≤ distance A at hbound
    omega

namespace FreshData

theorem distance_F (S : FreshData) :
    distance S.C + S.vars.card ≤ distance S.F :=
  fresh_sum_distance S.vars S.C S.C_ne_zero S.independent

/-- A short multiple below the paper's target forces a genuinely
nonmonomial core. This is Basic facts (b) in the descent section. -/
theorem two_le_weight_C_of_short (S : FreshData) (N : ℕ)
    (hN : N ≤ weight S.C + S.vars.card)
    (hex : ∃ G : Poly, ShortMultiple S.F N G) : 2 ≤ weight S.C := by
  obtain ⟨G, hG⟩ := hex
  obtain ⟨H, hfactor⟩ := hG.2.1
  have hH : H ≠ 0 := by
    intro hz
    apply hG.1
    rw [hfactor, hz, mul_zero]
  have hdist : distance S.F ≤ weight G := by
    rw [hfactor]
    exact distance_le_weight_mul S.F H hH
  have hbound := S.distance_F
  have hCpos := distance_pos S.C_ne_zero
  by_contra hnot
  have hsmall : weight S.C ≤ 1 := by omega
  have hshort := hG.2.2
  omega

end FreshData
end Pilz
