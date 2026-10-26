import WeightedPilz.Compression
import WeightedPilz.CompressionCoordinates

/-! Extract a scalar multiple from a stable finite monomial span. -/

noncomputable section
namespace WeightedPilz.Compression
open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [DecidableEq σ]

section Ring
variable [CommRing K]

def diagonal (i : σ) (s : K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval (fun k => C (if k = i then s else 1) * X k)

@[simp] theorem diagonal_C (i : σ) (s c : K) : diagonal i s (C c) = C c := by
  simp [diagonal]

@[simp] theorem diagonal_X (i k : σ) (s : K) :
    diagonal i s (X k) = C (if k = i then s else 1) * X k := by simp [diagonal]

theorem diagonal_monomial (i : σ) (s : K) (d : σ →₀ ℕ) (c : K) :
    diagonal i s (monomial d c) = monomial d (c * s ^ d i) := by
  have hp : d.prod (fun k n => (if k = i then s else 1) ^ n) = s ^ d i := by
    simpa using (Finsupp.prod_eq_single (f := d)
      (g := fun k n => (if k = i then s else 1) ^ n) i
      (by intro k _ hki; simp [hki]) (by simp))
  change eval₂ C (fun k => C (if k = i then s else 1) * X k) (monomial d c) = _
  rw [eval₂_monomial, ← hp]
  simp only [monomial_eq, Finsupp.prod, mul_pow, ← map_pow,
    Finset.prod_mul_distrib, ← map_prod, map_mul]
  ring

theorem coeff_diagonal (i : σ) (s : K) (P : MvPolynomial σ K) (d : σ →₀ ℕ) :
    coeff d (diagonal i s P) = coeff d P * s ^ d i := by
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [diagonal_monomial]
    by_cases he : e = d
    · subst e; simp
    · simp [coeff_monomial, he]
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ, add_mul]

/-- The balanced map is diagonal in the coordinates consisting of all but
one fresh variable and the sum of all fresh variables. -/
theorem balancedMap_sumChange (V : Finset σ) (i j : σ)
    (hi : i ∈ V) (hj : j ∈ V) (hij : i ≠ j) (s : K) (P : MvPolynomial σ K) :
    balancedMap i j s (sumChange V j P) = sumChange V j (diagonal i s P) := by
  have h : (balancedMap i j s).comp (sumChange V j).toAlgHom =
      (sumChange V j).toAlgHom.comp (diagonal i s) := by
    apply MvPolynomial.algHom_ext
    intro k
    by_cases hkj : k = j
    · subst k
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
        sumChange_X_self V j hj, balancedMap_sum V i j hi hj hij,
        diagonal_X, if_neg (Ne.symm hij), map_one, one_mul]
    · by_cases hki : k = i
      · subst k
        simp [AlgHom.comp_apply, hij]
      · simp [AlgHom.comp_apply, hkj, hki, balancedMap_X_other i j k hki hkj]
  exact AlgHom.congr_fun h P

def coordinatePart (i : σ) (n : ℕ) (P : MvPolynomial σ K) : MvPolynomial σ K :=
  Finsupp.filter (fun d => d i = n) P

@[simp] theorem coeff_coordinatePart (i : σ) (n : ℕ) (P : MvPolynomial σ K)
    (d : σ →₀ ℕ) : coeff d (coordinatePart i n P) = if d i = n then coeff d P else 0 := by
  simp only [coordinatePart, coeff, Finsupp.filter_apply]

theorem support_coordinatePart (i : σ) (n : ℕ) (P : MvPolynomial σ K) :
    (coordinatePart i n P).support = P.support.filter (fun d => d i = n) := by
  exact Finsupp.support_filter _ _

theorem coordinatePart_eq_outsideSlice (i : σ) (n : ℕ) (P : MvPolynomial σ K) :
    coordinatePart i n P = outsideSlice {k : σ | k ≠ i} (Finsupp.single i n) P := by
  have ho (d : σ →₀ ℕ) : outsideExponent {k : σ | k ≠ i} d = Finsupp.single i (d i) := by
    ext k
    by_cases hk : k = i <;> simp [outsideExponent_apply, hk, Finsupp.single_apply]
  ext d
  rw [coeff_coordinatePart, coeff_outsideSlice, ho]
  simp only [(Finsupp.single_injective i).eq_iff]

end Ring

section Field
variable [Field K]

def formalScale (i j : σ) (P : MvPolynomial σ K) : MvPolynomial σ (Polynomial K) :=
  balancedMap i j Polynomial.X (MvPolynomial.map Polynomial.C P)

theorem formalScale_eq_comp_formalBalanced (i j : σ) (P : MvPolynomial σ K) :
    formalScale i j P = MvPolynomial.map (Polynomial.compRingHom (1 - Polynomial.X))
      (formalBalanced i j P) := by
  unfold formalScale formalBalanced
  rw [map_balancedMap, MvPolynomial.map_map]
  have hc : (Polynomial.compRingHom (1 - Polynomial.X)).comp (Polynomial.C : K →+* _) =
      Polynomial.C := by ext c; simp
  rw [hc]
  simp

theorem support_formalBalanced_subset (S : Finset (σ →₀ ℕ)) (i j : σ)
    (P : MvPolynomial σ K)
    (h : ∀ n, (parameterCoeff n (formalBalanced i j P)).support ⊆ S) :
    (formalBalanced i j P).support ⊆ S := by
  intro d hd
  obtain ⟨n, hn⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hd)
  apply h n
  apply MvPolynomial.mem_support_iff.mpr
  exact Polynomial.mem_support_iff.mp hn

theorem parameterCoeff_formalScale_subset (S : Finset (σ →₀ ℕ)) (i j : σ)
    (P : MvPolynomial σ K)
    (h : ∀ n, (parameterCoeff n (formalBalanced i j P)).support ⊆ S) (n : ℕ) :
    (parameterCoeff n (formalScale i j P)).support ⊆ S := by
  apply (support_coeffProject_subset _ _).trans
  rw [formalScale_eq_comp_formalBalanced]
  exact (MvPolynomial.support_map_subset _ _).trans (support_formalBalanced_subset S i j P h)

theorem parameterCoeff_diagonal (i : σ) (n : ℕ) (P : MvPolynomial σ K) :
    parameterCoeff n (diagonal i Polynomial.X (MvPolynomial.map Polynomial.C P)) =
      coordinatePart i n P := by
  ext d
  rw [coeff_parameterCoeff, coeff_diagonal, coeff_map, coeff_coordinatePart]
  simp [Polynomial.coeff_C_mul_X_pow, eq_comm]

/-- Each coordinate component in the new variables is a parameter
coefficient of a sum-preserving balanced substitution. -/
theorem parameterCoeff_formalScale_sumChange (V : Finset σ) (i j : σ)
    (hi : i ∈ V) (hj : j ∈ V) (hij : i ≠ j) (n : ℕ) (P : MvPolynomial σ K) :
    parameterCoeff n (formalScale i j (sumChange V j P)) =
      sumChange V j (coordinatePart i n P) := by
  unfold formalScale
  rw [map_sumChange, balancedMap_sumChange V i j hi hj hij]
  change coeffProject (Polynomial.lcoeff K n) (sumChange V j _) = _
  rw [coeffProject_sumChange]
  exact congrArg (sumChange V j) (parameterCoeff_diagonal i n P)

/-- The coordinate components inherit support containment from the stable
monomial span in the original variables. -/
theorem sumChange_coordinatePart_support (S : Finset (σ →₀ ℕ)) (V : Finset σ)
    (i j : σ) (hi : i ∈ V) (hj : j ∈ V) (hij : i ≠ j)
    (P : MvPolynomial σ K)
    (h : ∀ n, (parameterCoeff n (formalBalanced i j (sumChange V j P))).support ⊆ S)
    (n : ℕ) : (sumChange V j (coordinatePart i n P)).support ⊆ S := by
  rw [← parameterCoeff_formalScale_sumChange V i j hi hj hij]
  exact parameterCoeff_formalScale_subset S i j (sumChange V j P) h n

/-- Closure of the coordinate span under coefficients of all required
balanced substitutions. This is supplied by the maximal support shift. -/
def StableSupport (V : Finset σ) (j : σ) (S : Finset (σ →₀ ℕ)) : Prop :=
  ∀ i ∈ V.erase j, ∀ Q : MvPolynomial σ K, Q.support ⊆ S →
    ∀ n, (parameterCoeff n (formalBalanced i j Q)).support ⊆ S

theorem coordinatePart_multiple (i : σ) (n : ℕ) (P Q : MvPolynomial σ K)
    (hi : i ∉ P.vars) (hdiv : P ∣ Q) : P ∣ coordinatePart i n Q := by
  obtain ⟨H, rfl⟩ := hdiv
  rw [coordinatePart_eq_outsideSlice, outsideSlice_mul]
  · exact dvd_mul_right _ _
  · intro k hk
    exact fun heq => hi (heq ▸ hk)

/-- Select one nonzero component for every auxiliary fresh coordinate. -/
theorem exists_supported_coordinate_component (V : Finset σ) (j : σ) (hj : j ∈ V)
    (S : Finset (σ →₀ ℕ)) (hstable : StableSupport (K := K) V j S)
    (P Q0 : MvPolynomial σ K) (hQ0 : Q0 ≠ 0) (hdiv : P ∣ Q0)
    (hP : ∀ i ∈ V.erase j, i ∉ P.vars)
    (hsupport : (sumChange V j Q0).support ⊆ S) :
    ∃ Q : MvPolynomial σ K, Q ≠ 0 ∧ P ∣ Q ∧ (sumChange V j Q).support ⊆ S ∧
      ∀ i ∈ V.erase j, ∀ d ∈ Q.support, ∀ e ∈ Q.support, d i = e i := by
  have hmain : ∀ W : Finset σ, W ⊆ V.erase j →
      ∃ Q : MvPolynomial σ K, Q ≠ 0 ∧ P ∣ Q ∧ (sumChange V j Q).support ⊆ S ∧
        ∀ i ∈ W, ∀ d ∈ Q.support, ∀ e ∈ Q.support, d i = e i := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨Q0, hQ0, hdiv, hsupport, by simp⟩
    | @insert i W hi ih =>
      intro hWV
      have hiV : i ∈ V.erase j := hWV (Finset.mem_insert_self i W)
      obtain ⟨Q, hQ, hPQ, hQS, hhom⟩ := ih (fun k hk => hWV (Finset.mem_insert_of_mem hk))
      obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hQ
      let Q' := coordinatePart i (d i) Q
      have hsub : Q'.support ⊆ Q.support := by
        dsimp only [Q']
        rw [support_coordinatePart]
        exact Finset.filter_subset _ _
      have hQ' : Q' ≠ 0 := by
        apply MvPolynomial.support_nonempty.mp
        refine ⟨d, ?_⟩
        dsimp only [Q']
        rw [support_coordinatePart]
        exact Finset.mem_filter.mpr ⟨hd, rfl⟩
      refine ⟨Q', hQ', coordinatePart_multiple i (d i) P Q (hP i hiV) hPQ, ?_, ?_⟩
      · exact sumChange_coordinatePart_support S V i j (Finset.mem_of_mem_erase hiV) hj
          (Finset.mem_erase.mp hiV).1 Q (hstable i hiV _ hQS) (d i)
      · intro k hk a ha b hb
        rcases Finset.mem_insert.mp hk with hki | hk
        · subst k
          have ha' := (Finset.mem_filter.mp (show a ∈ Q.support.filter (fun e => e i = d i) by
            simpa only [Q', support_coordinatePart] using ha)).2
          have hb' := (Finset.mem_filter.mp (show b ∈ Q.support.filter (fun e => e i = d i) by
            simpa only [Q', support_coordinatePart] using hb)).2
          exact ha'.trans hb'.symm
        · exact hhom k hk a (hsub ha) b (hsub hb)
  exact hmain (V.erase j) (Finset.Subset.refl _)

/-- Remove the common auxiliary monomial from a nonzero coordinate component.
Factoring the same monomial out of its cofactor proves divisibility directly. -/
theorem divide_homogeneous_component (B : Set σ) (P Q : MvPolynomial σ K)
    (hP : (P.vars : Set σ) ⊆ B) (hQ : Q ≠ 0) (hdiv : P ∣ Q)
    (hhom : ∀ d ∈ Q.support, ∀ e ∈ Q.support,
      outsideExponent B d = outsideExponent B e) :
    ∃ (α : σ →₀ ℕ) (D : MvPolynomial σ K),
      outsideExponent B α = α ∧ D ≠ 0 ∧ (D.vars : Set σ) ⊆ B ∧
      P ∣ D ∧ Q = monomial α 1 * D := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hQ
  let α := outsideExponent B d
  have hα : outsideExponent B α = α := outsideExponent_idempotent B d
  have hslice : outsideSlice B α Q = Q := by
    ext e
    rw [coeff_outsideSlice]
    by_cases he : e ∈ Q.support
    · rw [if_pos (hhom e he d hd)]
    · simp [MvPolynomial.notMem_support_iff.mp he]
  obtain ⟨D, hDfact, hDvars⟩ := outsideSlice_division B α hα Q
  have hfact : Q = monomial α 1 * D := hslice.symm.trans hDfact
  have hD : D ≠ 0 := by intro hz; apply hQ; rw [hfact, hz, mul_zero]
  obtain ⟨H, hH⟩ := hdiv
  obtain ⟨J, hJfact, _⟩ := outsideSlice_division B α hα H
  have hmono : (monomial α (1 : K) : MvPolynomial σ K) ≠ 0 := by simp
  have hPD : D = P * J := by
    apply mul_left_cancel₀ hmono
    calc
      monomial α 1 * D = outsideSlice B α Q := hDfact.symm
      _ = P * outsideSlice B α H := by rw [hH, outsideSlice_mul B α P H hP]
      _ = monomial α 1 * (P * J) := by rw [hJfact, mul_left_comm]
  exact ⟨α, D, hα, hD, hDvars, ⟨J, hPD⟩, hfact⟩

/-- The scalar extraction half of compression. The remaining polynomial
uses the fresh variables only through their sum; its support, translated by
a monomial in auxiliary fresh variables, stays in the stable finite span. -/
theorem scalar_extraction (V : Finset σ) (j : σ) (hj : j ∈ V)
    (C0 : MvPolynomial σ K) (hind : ∀ i ∈ V, i ∉ C0.vars)
    (S : Finset (σ →₀ ℕ)) (hstable : StableSupport (K := K) V j S)
    (G : MvPolynomial σ K) (hG : G ≠ 0)
    (hdiv : (C0 + ∑ i ∈ V, X i) ∣ G) (hGS : G.support ⊆ S) :
    ∃ (D : MvPolynomial σ K) (α : σ →₀ ℕ), D ≠ 0 ∧
      (∀ i ∈ V.erase j, i ∉ D.vars) ∧
      (C0 + ∑ i ∈ V, X i) ∣ sumChange V j D ∧
      weight (sumChange V j D) ≤ S.card ∧
      (∀ i, i ∉ V ∨ i = j → α i = 0) ∧
      (monomial α 1 * sumChange V j D).support ⊆ S := by
  let E := sumChange (K := K) V j
  let P : MvPolynomial σ K := C0 + X j
  let B : Set σ := {i | i ∉ V ∨ i = j}
  have hEP : E P = C0 + ∑ i ∈ V, X i := by
    change sumChange V j (C0 + X j) = _
    rw [map_add, sumChange_eq_self V j C0 (hind j hj), sumChange_X_self V j hj]
  have hPvars : (P.vars : Set σ) ⊆ B := by
    intro i hi
    rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset C0 (X j) hi) with hc | hx
    · exact Or.inl (fun hiV => hind i hiV hc)
    · exact Or.inr (by simpa using hx)
  have hPind : ∀ i ∈ V.erase j, i ∉ P.vars := by
    intro i hi hm
    rcases hPvars hm with hni | heq
    · exact hni (Finset.mem_of_mem_erase hi)
    · exact (Finset.mem_erase.mp hi).1 heq
  let Q0 := E.symm G
  have hQ0 : Q0 ≠ 0 := fun hz => hG (E.symm.injective (by simpa [Q0] using hz))
  have hPQ0 : P ∣ Q0 := by
    obtain ⟨H, hH⟩ := hdiv
    refine ⟨E.symm H, ?_⟩
    change E.symm G = P * E.symm H
    rw [hH, ← hEP, map_mul, E.symm_apply_apply]
  have hQ0S : (sumChange V j Q0).support ⊆ S := by
    change (E (E.symm G)).support ⊆ S
    simpa only [E.apply_symm_apply] using hGS
  obtain ⟨Q, hQ, hPQ, hQS, hhom⟩ :=
    exists_supported_coordinate_component V j hj S hstable P Q0 hQ0 hPQ0 hPind hQ0S
  have hout : ∀ d ∈ Q.support, ∀ e ∈ Q.support,
      outsideExponent B d = outsideExponent B e := by
    intro d hd e he
    ext i
    by_cases hi : i ∈ B
    · simp [outsideExponent_apply, hi]
    · have hiV : i ∈ V.erase j := by simpa [B, Finset.mem_erase, not_or, and_comm] using hi
      simp only [outsideExponent_apply, if_pos hi]
      exact hhom i hiV d hd e he
  obtain ⟨α, D, hα, hD, hDvars, hPD, hfact⟩ :=
    divide_homogeneous_component B P Q hPvars hQ hPQ hout
  have hαzero : ∀ i, i ∈ B → α i = 0 := by
    intro i hi
    have hh := congrArg (fun d : σ →₀ ℕ => d i) hα
    simpa [outsideExponent_apply, hi] using hh.symm
  have hmono : E (monomial α 1) = monomial α 1 := by
    apply sumChange_eq_self
    rw [vars_monomial one_ne_zero]
    exact fun hm => Finsupp.mem_support_iff.mp hm (hαzero j (Or.inr rfl))
  have hEsupport : (monomial α 1 * E D).support ⊆ S := by
    rwa [hfact, map_mul, hmono] at hQS
  refine ⟨D, α, hD, ?_, ?_, ?_, hαzero, hEsupport⟩
  · intro i hi hm
    rcases hDvars hm with hni | heq
    · exact hni (Finset.mem_of_mem_erase hi)
    · exact (Finset.mem_erase.mp hi).1 heq
  · obtain ⟨H, hH⟩ := hPD
    refine ⟨E H, ?_⟩
    rw [hH, map_mul, hEP]
  · have hw : weight (monomial α 1 * E D) ≤ S.card := Finset.card_le_card hEsupport
    rwa [weight_monomial_mul] at hw

end Field
end WeightedPilz.Compression
