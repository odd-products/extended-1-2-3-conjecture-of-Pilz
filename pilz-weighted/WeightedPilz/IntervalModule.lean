import WeightedPilz.ActionLocalization

/-! Finite interval matrices and change from residue-field coefficients to
arbitrary module coefficients. Every scalar interval bound used below is an
explicit premise, until the field interval theorem supplies it. -/

noncomputable section

namespace WeightedPilz

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {R M : Type*}

/-- A vector indexed by a finite set, extended by zero to positive integers. -/
def supportedInput [AddCommMonoid M] (S : Finset ℕ+) (v : S → M) : ℕ+ →₀ M :=
  ∑ b : S, Finsupp.single b.val (v b)

@[simp] theorem supportedInput_apply_mem [AddCommMonoid M] (S : Finset ℕ+)
    (v : S → M) (b : S) : supportedInput S v b.val = v b := by
  classical
  simp [supportedInput, Finsupp.finset_sum_apply, Finsupp.single_apply, Subtype.val_inj]

theorem supportedInput_apply_not_mem [AddCommMonoid M] (S : Finset ℕ+)
    (v : S → M) {b : ℕ+} (hb : b ∉ S) : supportedInput S v b = 0 := by
  classical
  rw [supportedInput, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finsupp.single_eq_of_ne
  intro h
  exact hb (h.symm ▸ a.property)

theorem supportedInput_support_subset [AddCommMonoid M] (S : Finset ℕ+)
    (v : S → M) : (supportedInput S v).support ⊆ S := by
  intro b hb
  by_contra hnot
  exact (Finsupp.mem_support_iff.mp hb) (supportedInput_apply_not_mem S v hnot)

theorem supportedInput_ne_zero [AddCommMonoid M] (S : Finset ℕ+)
    {v : S → M} (hv : v ≠ 0) : supportedInput S v ≠ 0 := by
  intro h
  apply hv
  funext b
  have hb := congrArg (fun f : ℕ+ →₀ M => f b.val) h
  simpa only [supportedInput_apply_mem, Finsupp.zero_apply] using hb

@[simp] theorem supportedInput_support_values [AddCommMonoid M] (f : ℕ+ →₀ M) :
    supportedInput f.support (fun b => f b.val) = f := by
  ext b
  by_cases hb : b ∈ f.support
  · exact supportedInput_apply_mem f.support (fun b => f b.val) ⟨b, hb⟩
  · rw [supportedInput_apply_not_mem _ _ hb, Finsupp.notMem_support_iff.mp hb]

/-- All possible interval output positions for a given finite input support. -/
def intervalOutputSet (n : ℕ) (S : Finset ℕ+) : Finset ℕ+ :=
  (Finset.range n).biUnion (fun a => S.image (fun b => intervalIndex a * b))

theorem intervalEndAction_support_subset [AddCommMonoid M] (n : ℕ)
    (φ : ℕ → AddMonoid.End M) (f : ℕ+ →₀ M) (S : Finset ℕ+)
    (hS : f.support ⊆ S) :
    (intervalEndAction n φ f).support ⊆ intervalOutputSet n S := by
  classical
  intro m hm
  by_contra hmout
  apply Finsupp.mem_support_iff.mp hm
  rw [intervalEndAction_apply]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hd : intervalIndex a ∣ m
  · rw [if_pos hd]
    have hquot : PNat.divExact m (intervalIndex a) ∉ f.support := by
      intro hq
      apply hmout
      apply Finset.mem_biUnion.mpr
      refine ⟨a, ha, Finset.mem_image.mpr ?_⟩
      exact ⟨_, hS hq, PNat.mul_div_exact hd⟩
    rw [Finsupp.notMem_support_iff.mp hquot, map_zero]
  · exact if_neg hd

/-- Restricting a supported function to a containing finite set preserves its
number of nonzero coordinates. -/
theorem finiteVectorSupport_restrict_card [Zero M] (B : Finset ℕ+) (f : ℕ+ →₀ M)
    (hB : f.support ⊆ B) :
    (finiteVectorSupport (fun b : B => f b.val)).card = f.support.card := by
  classical
  have heq : (finiteVectorSupport (fun b : B => f b.val)).image Subtype.val = f.support := by
    ext b
    simp only [Finset.mem_image, finiteVectorSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, Finsupp.mem_support_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hb
      exact ⟨⟨b, hB (Finsupp.mem_support_iff.mpr hb)⟩, hb, rfl⟩
  rw [← heq, Finset.card_image_of_injective _ Subtype.val_injective]

/-- Finite interval convolution matrix, with arbitrary chosen input and output
sets. A row receives the coefficient `c(a+1)` from multiplication by `a+1`. -/
def intervalMatrix [Semiring R] (n : ℕ) (c : ℕ → R) (S B : Finset ℕ+) :
    Matrix B S R :=
  fun m b => ∑ a ∈ Finset.range n,
    if intervalIndex a * b.val = m.val then c (a + 1) else 0

theorem intervalMatrix_map {T : Type*} [Semiring R] [Semiring T]
    (θ : R →+* T) (n : ℕ) (c : ℕ → R) (S B : Finset ℕ+) :
    (intervalMatrix n c S B).map θ = intervalMatrix n (fun a => θ (c a)) S B := by
  ext m b
  simp [intervalMatrix, Matrix.map_apply, map_sum, apply_ite]

/-- The finite matrix acts on any module exactly as the arithmetic interval
operator on the corresponding supported input. -/
theorem matrixModuleAction_intervalMatrix [Semiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) (c : ℕ → R) (S B : Finset ℕ+) (v : S → M) (m : B) :
    matrixModuleAction (intervalMatrix n c S B) v m =
      intervalEndAction n (fun a => scalarWeightEnd (c a)) (supportedInput S v) m.val := by
  classical
  simp only [matrixModuleAction, intervalMatrix, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp only [intervalEndAction, supportedInput, Finsupp.mapRange_finset_sum,
    Finsupp.mapRange_single, Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single,
    Finsupp.finset_sum_apply, Finsupp.single_apply]
  rfl

/-- Scalar support bounds over every residue field provide the exact hypothesis
needed by the finite matrix module theorem. -/
theorem intervalMatrix_residue_support_bound [CommRing R] (n : ℕ) (c : ℕ → R)
    (hfield : ∀ (I : Ideal R), I.IsMaximal →
      IntervalEndBound (M := R ⧸ I) n
        (fun a => scalarWeightEnd (Ideal.Quotient.mk I (c a))))
    (S : Finset ℕ+) (I : Ideal R) (hI : I.IsMaximal)
    (v : S → R ⧸ I) (hv : v ≠ 0) :
    n ≤ (finiteVectorSupport
      (((intervalMatrix n c S (intervalOutputSet n S)).map (Ideal.Quotient.mk I)).mulVec v)).card := by
  classical
  have hb := hfield I hI (supportedInput S v) (supportedInput_ne_zero S hv)
  rw [intervalMatrix_map]
  have heq :
      (intervalMatrix n (fun a => Ideal.Quotient.mk I (c a)) S (intervalOutputSet n S)).mulVec v =
      fun m : intervalOutputSet n S =>
        intervalEndAction n (fun a => scalarWeightEnd (Ideal.Quotient.mk I (c a)))
          (supportedInput S v) m.val := by
    funext m
    exact matrixModuleAction_intervalMatrix (R := R ⧸ I) n
      (fun a => Ideal.Quotient.mk I (c a)) S _ v m
  rw [heq, finiteVectorSupport_restrict_card]
  · exact hb
  · exact intervalEndAction_support_subset n _ _ S (supportedInput_support_subset S v)

/-- Interval bounds pass from the residue fields of a ring to every module over
that ring. The residue-field bound is explicit. -/
theorem intervalEndBound_of_residue_bounds [CommRing R] [AddCommMonoid M] [Module R M]
    (n : ℕ) (c : ℕ → R)
    (hfield : ∀ (I : Ideal R), I.IsMaximal →
      IntervalEndBound (M := R ⧸ I) n
        (fun a => scalarWeightEnd (Ideal.Quotient.mk I (c a)))) :
    IntervalEndBound (M := M) n (fun a => scalarWeightEnd (c a)) := by
  classical
  intro f hf
  let S := f.support
  let B := intervalOutputSet n S
  let v : S → M := fun b => f b.val
  have hv : v ≠ 0 := by
    intro hz
    apply hf
    ext b
    by_cases hb : b ∈ f.support
    · exact congrFun hz ⟨b, hb⟩
    · exact Finsupp.notMem_support_iff.mp hb
  have hbound := matrixModuleAction_support_bound
    (intervalMatrix n c S B) n (intervalMatrix_residue_support_bound n c hfield S) v hv
  have heq : matrixModuleAction (intervalMatrix n c S B) v =
      fun m : B => intervalEndAction n (fun a => scalarWeightEnd (c a)) f m.val := by
    funext m
    rw [matrixModuleAction_intervalMatrix]
    change intervalEndAction n _ (supportedInput f.support (fun b => f b.val)) m.val = _
    rw [supportedInput_support_values]
  rw [heq, finiteVectorSupport_restrict_card] at hbound
  · exact hbound
  · exact intervalEndAction_support_subset n _ f S (Finset.Subset.refl _)

/-- Erasing fewer than `n` rows of a finite interval matrix leaves a left inverse
over the ring whenever all residue-field interval bounds hold. -/
theorem intervalMatrix_erasure_left_inverse [CommRing R] (n : ℕ) (c : ℕ → R)
    (hfield : ∀ (I : Ideal R), I.IsMaximal →
      IntervalEndBound (M := R ⧸ I) n
        (fun a => scalarWeightEnd (Ideal.Quotient.mk I (c a))))
    (S : Finset ℕ+) (E : Finset (intervalOutputSet n S)) (hE : E.card < n) :
    ∃ L : Matrix S {i : intervalOutputSet n S // i ∉ E} R,
      L * (intervalMatrix n c S (intervalOutputSet n S)).submatrix
        (fun (i : {i : intervalOutputSet n S // i ∉ E}) => i.val) id = 1 :=
  matrix_exists_erasure_left_inverse _ n
    (intervalMatrix_residue_support_bound n c hfield S) E hE

end WeightedPilz
