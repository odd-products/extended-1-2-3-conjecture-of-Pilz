import WeightedPilz.Endpoints
import WeightedPilz.VariableSlices
import WeightedPilz.ComponentBounds

/-! Adding a linear variable adds the distances of its endpoint coefficients. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial

variable {K : Type*} [Field K]

private theorem coordinateEquiv_rename_subtype_linear (p : ℕ)
    (P : MvPolynomial {q : ℕ // q ≠ p} K) :
    coordinateEquiv p (rename Subtype.val P) = Polynomial.C P := by
  have hh : ((coordinateEquiv (K := K) p).toRingHom.comp
      (rename (Subtype.val : {q : ℕ // q ≠ p} → ℕ)).toRingHom) = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coordinateEquiv, optionEquivLeft_C]
    · intro q
      simp [coordinateEquiv, Equiv.optionSubtypeNe_symm_of_ne q.property,
        optionEquivLeft_X_some]
  exact RingHom.congr_fun hh P

theorem coordinate_zero_recover (p : ℕ) (A : Poly K) (hdegree : A.degreeOf p = 0) :
    rename (Subtype.val : {q : ℕ // q ≠ p} → ℕ) ((coordinateEquiv p A).coeff 0) = A := by
  have hconst : coordinateEquiv p A = Polynomial.C ((coordinateEquiv p A).coeff 0) := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hdegree]
  apply (coordinateEquiv p).injective
  rw [coordinateEquiv_rename_subtype_linear]
  exact hconst.symm

/-- Endpoint slicing for a new linear variable with arbitrary independent
nonzero coefficients, as used in the paper's core-sum tables. -/
theorem linear_core_distance (p : ℕ) (a b : Poly K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hadegree : a.degreeOf p = 0) (hbdegree : b.degreeOf p = 0) :
    distance a + distance b ≤ distance (a + b * X p) := by
  let E := coordinateEquiv (K := K) p
  let a₀ := (E a).coeff 0
  let b₀ := (E b).coeff 0
  have hA : E a = Polynomial.C a₀ := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hadegree]
  have hB : E b = Polynomial.C b₀ := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hbdegree]
  have hA₀ : a₀ ≠ 0 := by
    intro hz
    apply ha
    rw [← coordinate_zero_recover p a hadegree]
    change rename Subtype.val a₀ = 0
    rw [hz, map_zero]
  have hB₀ : b₀ ≠ 0 := by
    intro hz
    apply hb
    rw [← coordinate_zero_recover p b hbdegree]
    change rename Subtype.val b₀ = 0
    rw [hz, map_zero]
  let P := a + b * X p
  have hQ : E P = Polynomial.C a₀ + Polynomial.C b₀ * Polynomial.X := by
    dsimp [P]
    rw [map_add, map_mul, hA, hB]
    congr 2
    simp [E, coordinateEquiv, optionEquivLeft_X_none]
  have hdeg : (E P).natDegree = 1 := by
    rw [hQ, Polynomial.natDegree_C_add, Polynomial.natDegree_C_mul_X b₀ hB₀]
  have htrail : (E P).natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by simpa [hQ] using hA₀))
  have hspan : (E P).natTrailingDegree < (E P).natDegree := by omega
  have hend := endpoint_distance p P hspan
  change distance (E P).trailingCoeff + distance (E P).leadingCoeff ≤ distance P at hend
  have htc : (E P).trailingCoeff = a₀ := by
    rw [Polynomial.trailingCoeff, htrail, hQ]
    simp
  have hlc : (E P).leadingCoeff = b₀ := by
    rw [Polynomial.leadingCoeff, hdeg, hQ]
    simp
  have haDist : distance a ≤ distance a₀ := by
    rw [← coordinate_zero_recover p a hadegree]
    exact (distance_rename_of_injective Subtype.val Subtype.val_injective a₀).le
  have hbDist : distance b ≤ distance b₀ := by
    rw [← coordinate_zero_recover p b hbdegree]
    exact (distance_rename_of_injective Subtype.val Subtype.val_injective b₀).le
  rw [htc, hlc] at hend
  exact (Nat.add_le_add haDist hbDist).trans hend



open scoped BigOperators

/-- Successively slice every fresh linear coordinate. All coefficients avoid
all the slicing coordinates; the constant term witnesses that the bottom
coefficient stays nonzero at every step. -/
theorem repeated_linear_core_distance (T : Finset ℕ) (C : Poly K) (A : ℕ → Poly K)
    (hC : constantCoeff C ≠ 0)
    (hA : ∀ p ∈ T, A p ≠ 0)
    (hCdeg : ∀ p ∈ T, C.degreeOf p = 0)
    (hAdeg : ∀ p ∈ T, ∀ q ∈ T, (A p).degreeOf q = 0) :
    distance C + ∑ p ∈ T, distance (A p) ≤
      distance (C + ∑ p ∈ T, A p * X p) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T hp ih =>
      have hAT : ∀ q ∈ T, A q ≠ 0 := fun q hq => hA q (Finset.mem_insert_of_mem hq)
      have hCT : ∀ q ∈ T, C.degreeOf q = 0 :=
        fun q hq => hCdeg q (Finset.mem_insert_of_mem hq)
      have hATdeg : ∀ q ∈ T, ∀ r ∈ T, (A q).degreeOf r = 0 :=
        fun q hq r hr => hAdeg q (Finset.mem_insert_of_mem hq) r (Finset.mem_insert_of_mem hr)
      have hprev := ih hAT hCT hATdeg
      let B := C + ∑ q ∈ T, A q * X q
      have hB : B ≠ 0 := by
        intro hz
        apply hC
        have hh := congrArg constantCoeff hz
        simpa [B, map_add, map_sum, map_mul] using hh
      have hBdeg : B.degreeOf p = 0 := by
        apply Nat.eq_zero_of_le_zero
        refine (degreeOf_add_le p C (∑ q ∈ T, A q * X q)).trans ?_
        rw [hCdeg p (Finset.mem_insert_self _ _), Nat.zero_max]
        refine (degreeOf_sum_le p T (fun q => A q * X q)).trans ?_
        rw [Finset.sup_le_iff]
        intro q hq
        have hqp : q ≠ p := by intro heq; exact hp (heq ▸ hq)
        refine (degreeOf_mul_le p (A q) (X q)).trans_eq ?_
        rw [hAdeg q (Finset.mem_insert_of_mem hq) p (Finset.mem_insert_self _ _)]
        simp [degreeOf_X, Ne.symm hqp]
      have hlin := linear_core_distance p B (A p) hB
        (hA p (Finset.mem_insert_self _ _)) hBdeg
        (hAdeg p (Finset.mem_insert_self _ _) p (Finset.mem_insert_self _ _))
      have heq : C + ∑ q ∈ insert p T, A q * X q = B + A p * X p := by
        rw [Finset.sum_insert hp]
        dsimp [B]
        ring
      rw [heq, Finset.sum_insert hp]
      dsimp [B] at hlin ⊢
      omega

/-- The two extreme rows of a square are disjoint in a fresh coordinate.
This bound itself works in characteristic two as well. -/
theorem linear_core_square_weight (p : ℕ) (A B : Poly K)
    (hAdegree : A.degreeOf p = 0) (hBdegree : B.degreeOf p = 0) :
    weight (A ^ 2) + weight (B ^ 2) ≤ weight ((A + B * X p) ^ 2) := by
  let E := coordinateEquiv (K := K) p
  let a₀ := (E A).coeff 0
  let b₀ := (E B).coeff 0
  have hA : E A = Polynomial.C a₀ := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hAdegree]
  have hB : E B = Polynomial.C b₀ := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hBdegree]
  have hQ : E ((A + B * X p) ^ 2) =
      Polynomial.C (a₀ ^ 2) + Polynomial.C (2 * a₀ * b₀) * Polynomial.X +
        Polynomial.C (b₀ ^ 2) * Polynomial.X ^ 2 := by
    rw [map_pow, map_add, map_mul, hA, hB]
    have hX : E (X p) = Polynomial.X := by
      simp [E, coordinateEquiv, optionEquivLeft_X_none]
    rw [hX]
    simp only [map_pow, map_mul, map_ofNat]
    ring
  have hrows := weight_two_coordinate_slices p ((A + B * X p) ^ 2) 0 2 (by decide)
  change weight ((E ((A + B * X p) ^ 2)).coeff 0) +
    weight ((E ((A + B * X p) ^ 2)).coeff 2) ≤ _ at hrows
  rw [hQ] at hrows
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow] at hrows
  norm_num at hrows
  have hAw : weight (A ^ 2) = weight (a₀ ^ 2) := by
    calc
      weight (A ^ 2) = weight (rename Subtype.val (a₀ ^ 2)) := by
        congr 1
        rw [map_pow]
        congr 1
        exact (coordinate_zero_recover p A hAdegree).symm
      _ = _ := weight_rename_of_injective Subtype.val Subtype.val_injective _
  have hBw : weight (B ^ 2) = weight (b₀ ^ 2) := by
    calc
      weight (B ^ 2) = weight (rename Subtype.val (b₀ ^ 2)) := by
        congr 1
        rw [map_pow]
        congr 1
        exact (coordinate_zero_recover p B hBdegree).symm
      _ = _ := weight_rename_of_injective Subtype.val Subtype.val_injective _
  rw [hAw, hBw]
  exact hrows

/-- The constant square and every pure square row survive in a simultaneous
linear core. Mixed rows may cancel; this statement does not count them. -/
theorem repeated_linear_core_square_weight (T : Finset ℕ) (C : Poly K) (A : ℕ → Poly K)
    (hCdeg : ∀ p ∈ T, C.degreeOf p = 0)
    (hAdeg : ∀ p ∈ T, ∀ q ∈ T, (A p).degreeOf q = 0) :
    weight (C ^ 2) + ∑ p ∈ T, weight (A p ^ 2) ≤
      weight ((C + ∑ p ∈ T, A p * X p) ^ 2) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T hp ih =>
      have hCT : ∀ q ∈ T, C.degreeOf q = 0 :=
        fun q hq => hCdeg q (Finset.mem_insert_of_mem hq)
      have hATdeg : ∀ q ∈ T, ∀ r ∈ T, (A q).degreeOf r = 0 :=
        fun q hq r hr => hAdeg q (Finset.mem_insert_of_mem hq) r (Finset.mem_insert_of_mem hr)
      have hprev := ih hCT hATdeg
      let B := C + ∑ q ∈ T, A q * X q
      have hBdeg : B.degreeOf p = 0 := by
        apply Nat.eq_zero_of_le_zero
        refine (degreeOf_add_le p C (∑ q ∈ T, A q * X q)).trans ?_
        rw [hCdeg p (Finset.mem_insert_self _ _), Nat.zero_max]
        refine (degreeOf_sum_le p T (fun q => A q * X q)).trans ?_
        rw [Finset.sup_le_iff]
        intro q hq
        have hqp : q ≠ p := by intro heq; exact hp (heq ▸ hq)
        refine (degreeOf_mul_le p (A q) (X q)).trans_eq ?_
        rw [hAdeg q (Finset.mem_insert_of_mem hq) p (Finset.mem_insert_self _ _)]
        simp [degreeOf_X, Ne.symm hqp]
      have hlin := linear_core_square_weight p B (A p) hBdeg
        (hAdeg p (Finset.mem_insert_self _ _) p (Finset.mem_insert_self _ _))
      have heq : C + ∑ q ∈ insert p T, A q * X q = B + A p * X p := by
        rw [Finset.sum_insert hp]
        dsimp [B]
        ring
      rw [heq, Finset.sum_insert hp]
      dsimp [B] at hlin ⊢
      omega

end WeightedPilz


