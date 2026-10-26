import WeightedPilz.GenericInitialOverlap

/-! The support geometry of `A + ∑ i, X i * B i`, with independent fresh
coordinates. This is the general rowwise refinement of the initial test. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [DecidableEq σ] [Field K]

/-- A polynomial affine in a finite set of fresh variables. The base
coefficients can involve arbitrarily many other variables. -/
structure InitialSlicedData (σ K : Type*) [DecidableEq σ] [Field K] where
  fresh : Finset σ
  A : MvPolynomial σ K
  B : σ → MvPolynomial σ K
  independent_A : ∀ i ∈ fresh, ∀ d ∈ A.support, d i = 0
  independent_B : ∀ j ∈ fresh, ∀ i ∈ fresh, ∀ d ∈ (B j).support, d i = 0

namespace InitialSlicedData

def polynomial (S : InitialSlicedData σ K) : MvPolynomial σ K :=
  S.A + ∑ i ∈ S.fresh, X i * S.B i

def projection (S : InitialSlicedData σ K) : (σ →₀ ℕ) →+ (σ →₀ ℕ) :=
  Finsupp.filterAddHom (fun i => i ∈ S.fresh)

@[simp] theorem projection_apply (S : InitialSlicedData σ K) (d : σ →₀ ℕ) (i : σ) :
    S.projection d i = if i ∈ S.fresh then d i else 0 := rfl

def indices (S : InitialSlicedData σ K) : Finset (Option σ) :=
  insert none (S.fresh.image some)

def tag : Option σ → σ →₀ ℕ
  | none => 0
  | some i => Finsupp.single i 1

def coefficient (S : InitialSlicedData σ K) : Option σ → MvPolynomial σ K
  | none => S.A
  | some i => S.B i

def row (S : InitialSlicedData σ K) : Option σ → MvPolynomial σ K
  | none => S.A
  | some i => X i * S.B i

theorem tag_injective : Function.Injective (tag (σ := σ)) := by
  intro t u h
  cases t with
  | none =>
      cases u with
      | none => rfl
      | some i =>
          have hh := congrArg (fun d : σ →₀ ℕ => d i) h
          simp [tag] at hh
  | some i =>
      cases u with
      | none =>
          have hh := congrArg (fun d : σ →₀ ℕ => d i) h
          simp [tag] at hh
      | some j =>
          by_cases hij : i = j
          · exact congrArg some hij
          · have hh := congrArg (fun d : σ →₀ ℕ => d i) h
            simp [tag, hij, Ne.symm hij] at hh

theorem polynomial_eq_sum_rows (S : InitialSlicedData σ K) :
    S.polynomial = ∑ t ∈ S.indices, S.row t := by
  classical
  rw [indices, Finset.sum_insert (by simp)]
  rw [Finset.sum_image (by intro i hi j hj h; exact Option.some.inj h)]
  rfl

theorem projection_of_independent (S : InitialSlicedData σ K) (d : σ →₀ ℕ)
    (hd : ∀ i ∈ S.fresh, d i = 0) : S.projection d = 0 := by
  ext i
  by_cases hi : i ∈ S.fresh <;> simp [projection_apply, hi, hd]

theorem projection_tag (S : InitialSlicedData σ K) {t : Option σ} (ht : t ∈ S.indices) :
    S.projection (tag t) = tag t := by
  cases t with
  | none => simp [tag]
  | some i =>
      have hi : i ∈ S.fresh := by simpa [indices] using ht
      exact Finsupp.filter_single_of_pos (fun k => k ∈ S.fresh) hi

theorem projection_row_support (S : InitialSlicedData σ K) {t : Option σ}
    (ht : t ∈ S.indices) {d : σ →₀ ℕ} (hd : d ∈ (S.row t).support) :
    S.projection d = tag t := by
  cases t with
  | none =>
      exact S.projection_of_independent d (fun i hi => S.independent_A i hi d hd)
  | some j =>
      have hj : j ∈ S.fresh := by simpa [indices] using ht
      rw [row, support_X_mul] at hd
      obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hd
      change S.projection (Finsupp.single j 1 + e) = tag (some j)
      rw [map_add, S.projection_of_independent e (fun i hi => S.independent_B j hj i hi e he),
        add_zero]
      exact S.projection_tag ht

theorem projection_support (S : InitialSlicedData σ K) {d : σ →₀ ℕ}
    (hd : d ∈ S.polynomial.support) : ∃ t ∈ S.indices, S.projection d = tag t := by
  rw [S.polynomial_eq_sum_rows] at hd
  obtain ⟨t, ht, hd⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  exact ⟨t, ht, S.projection_row_support ht hd⟩

theorem projection_support_subset_simplex (S : InitialSlicedData σ K) :
    S.polynomial.support.image S.projection ⊆ exponentSimplex S.fresh := by
  intro β hβ
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hβ
  obtain ⟨t, ht, htag⟩ := S.projection_support hd
  rw [htag]
  cases t with
  | none => exact Finset.mem_insert_self _ _
  | some i =>
      have hi : i ∈ S.fresh := by simpa [indices] using ht
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

private theorem projectedRow_of_constant
    (π : (σ →₀ ℕ) →+ (σ →₀ ℕ)) (P : MvPolynomial σ K)
    (α β : σ →₀ ℕ) (hP : ∀ d ∈ P.support, π d = α) :
    projectedRow π β P = if α = β then P else 0 := by
  classical
  by_cases h : α = β
  · rw [if_pos h]
    apply (Finsupp.filter_eq_self_iff _ _).mpr
    intro d hd
    exact (hP d (Finsupp.mem_support_iff.mpr hd)).trans h
  · rw [if_neg h]
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro d hd
    by_contra hd0
    exact h ((hP d (Finsupp.mem_support_iff.mpr hd0)).symm.trans hd)

theorem projectedRow_polynomial (S : InitialSlicedData σ K) {t : Option σ}
    (ht : t ∈ S.indices) : projectedRow S.projection (tag t) S.polynomial = S.row t := by
  classical
  rw [S.polynomial_eq_sum_rows]
  change (∑ u ∈ S.indices, S.row u).filter (fun d => S.projection d = tag t) = S.row t
  rw [Finsupp.filter_sum]
  rw [Finset.sum_eq_single t]
  · exact (projectedRow_of_constant S.projection (S.row t) (tag t) (tag t)
      (fun d hd => S.projection_row_support ht hd)).trans (if_pos rfl)
  · intro u hu hut
    exact (projectedRow_of_constant S.projection (S.row u) (tag u) (tag t)
      (fun d hd => S.projection_row_support hu hd)).trans
        (if_neg (fun h => hut (tag_injective h)))
  · exact fun h => False.elim (h ht)

theorem weight_row (S : InitialSlicedData σ K) (t : Option σ) :
    weight (S.row t) = weight (S.coefficient t) := by
  cases t with
  | none => rfl
  | some i => simp [row, coefficient, weight, support_X_mul]

/-- Every nonempty overlap is confined to one pair of coefficient rows.
The coefficient support sizes bound every row pair; the base-to-base pair
has the sharper largest-residue-class bound. -/
theorem translated_overlap_rows (S : InitialSlicedData σ K)
    (m q : ℕ) (hm : 0 < m) (hq : 2 ≤ q) (a b : σ →₀ ℕ)
    (hI : ((S.polynomial.support.image (fun d => a + scaleExponent m d)) ∩
      (S.polynomial.support.image (fun d => b + scaleExponent (m * q) d))).Nonempty) :
    ∃ t ∈ S.indices, ∃ u ∈ S.indices,
      (S.polynomial.support.image (fun d => a + scaleExponent m d)) ∩
          (S.polynomial.support.image (fun d => b + scaleExponent (m * q) d)) ⊆
        ((S.row t).support.image (fun d => a + scaleExponent m d)) ∩
          ((S.row u).support.image (fun d => b + scaleExponent (m * q) d)) ∧
      (((S.polynomial.support.image (fun d => a + scaleExponent m d)) ∩
        (S.polynomial.support.image (fun d => b + scaleExponent (m * q) d))).card ≤
          min (weight (S.coefficient t)) (weight (S.coefficient u))) ∧
      (t = none → u = none →
        (((S.polynomial.support.image (fun d => a + scaleExponent m d)) ∩
          (S.polynomial.support.image (fun d => b + scaleExponent (m * q) d))).card ≤
            residueSigma q S.A)) := by
  classical
  have hsmall : ∀ d ∈ S.polynomial.support, ∀ i, S.projection d i < q := by
    intro d hd i
    have h := exponentSimplex_coordinate_le_one S.fresh
      (S.projection_support_subset_simplex (Finset.mem_image.mpr ⟨d, hd, rfl⟩)) i
    omega
  obtain ⟨β, hβ, γ, hγ, hsub, hcard, hres⟩ :=
    translated_dilate_overlap_rows S.projection S.polynomial S.polynomial m q hm
      (by omega) hsmall a b hI
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hβ
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hγ
  obtain ⟨t, ht, het⟩ := S.projection_support he
  obtain ⟨u, hu, hfu⟩ := S.projection_support hf
  rw [het, hfu, S.projectedRow_polynomial ht, S.projectedRow_polynomial hu] at hsub hcard
  rw [het, S.projectedRow_polynomial ht] at hres
  rw [S.weight_row t, S.weight_row u] at hcard
  refine ⟨t, ht, u, hu, hsub, hcard, ?_⟩
  intro ht0 hu0
  simpa [ht0, row] using hres

/-- There is at most one projected point in the overlap, even if some
coefficient rows vanish. -/
theorem translated_overlap_projection_card_le_one (S : InitialSlicedData σ K)
    (m q : ℕ) (hm : 0 < m) (hq : 2 ≤ q) (a b : σ →₀ ℕ) :
    (((S.polynomial.support.image (fun d => a + scaleExponent m d)) ∩
      (S.polynomial.support.image (fun d => b + scaleExponent (m * q) d))).image
        S.projection).card ≤ 1 := by
  classical
  have hsub : ((S.polynomial.support.image (fun d => a + scaleExponent m d)) ∩
      (S.polynomial.support.image (fun d => b + scaleExponent (m * q) d))).image
        S.projection ⊆
      ((exponentSimplex S.fresh).image (fun d => S.projection a + scaleExponent m d)) ∩
        ((exponentSimplex S.fresh).image
          (fun d => S.projection b + scaleExponent (m * q) d)) := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, he, hed⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hd).1
    obtain ⟨f, hf, hfd⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hd).2
    apply Finset.mem_inter.mpr
    constructor
    · refine Finset.mem_image.mpr ⟨S.projection e,
        S.projection_support_subset_simplex (Finset.mem_image.mpr ⟨e, he, rfl⟩), ?_⟩
      simpa only [map_add, scaleExponent, map_nsmul] using congrArg S.projection hed
    · refine Finset.mem_image.mpr ⟨S.projection f,
        S.projection_support_subset_simplex (Finset.mem_image.mpr ⟨f, hf, rfl⟩), ?_⟩
      simpa only [map_add, scaleExponent, map_nsmul] using congrArg S.projection hfd
  exact (Finset.card_le_card hsub).trans
    (translated_simplex_dilate_inter_card_le_one S.fresh S.fresh m q hm hq
      (S.projection a) (S.projection b))

/-- The rowwise bounds for the literal supports of translated unequal
characteristic powers, over an arbitrary field. -/
theorem distinguished_overlap_rows (S : InitialSlicedData σ K)
    (p e f : ℕ) [ExpChar K p] (hef : e ≤ f) (hne : p ^ e ≠ p ^ f)
    (a b : σ →₀ ℕ) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0)
    (hI : ((monomial a u * S.polynomial ^ p ^ e).support ∩
      (monomial b v * S.polynomial ^ p ^ f).support).Nonempty) :
    ∃ t ∈ S.indices, ∃ w ∈ S.indices,
      (monomial a u * S.polynomial ^ p ^ e).support ∩
          (monomial b v * S.polynomial ^ p ^ f).support ⊆
        ((S.row t).support.image (fun d => a + scaleExponent (p ^ e) d)) ∩
          ((S.row w).support.image (fun d => b + scaleExponent (p ^ f) d)) ∧
      (((monomial a u * S.polynomial ^ p ^ e).support ∩
        (monomial b v * S.polynomial ^ p ^ f).support).card ≤
          min (weight (S.coefficient t)) (weight (S.coefficient w))) ∧
      (t = none → w = none →
        (((monomial a u * S.polynomial ^ p ^ e).support ∩
          (monomial b v * S.polynomial ^ p ^ f).support).card ≤
            residueSigma (p ^ (f - e)) S.A)) := by
  have hp : 2 ≤ p := by
    have hp0 := expChar_pos K p
    by_contra h
    have hp1 : p = 1 := by omega
    simp [hp1] at hne
  have hlt : e < f := by
    have hne' : e ≠ f := fun h => hne (congrArg (fun k => p ^ k) h)
    omega
  have hratio : 2 ≤ p ^ (f - e) := by
    have h := Nat.pow_le_pow_right (by omega : 1 ≤ p) (show 1 ≤ f - e by omega)
    simp only [pow_one] at h
    exact hp.trans h
  have hfactor : p ^ f = p ^ e * p ^ (f - e) := by
    rw [← pow_add, Nat.add_sub_of_le hef]
  simp only [support_scalar_monomial_frobenius p e S.polynomial a u hu,
    support_scalar_monomial_frobenius p f S.polynomial b v hv] at hI ⊢
  rw [hfactor] at hI ⊢
  exact S.translated_overlap_rows (p ^ e) (p ^ (f - e))
    (pow_pos (expChar_pos K p) e) hratio a b hI

end InitialSlicedData
end WeightedPilz
