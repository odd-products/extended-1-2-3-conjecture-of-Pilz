import WeightedPilz.LineProjectionGeometry
import WeightedPilz.FiniteLineRepresentatives
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Occupied rational affine lines and the affine dimension of exponent support.

One representative per fiber, together with the fiber direction, spans every
support difference. Prescribed collinear representatives save generators. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
attribute [local instance] Classical.propDecidable

variable {σ K : Type*} [CommSemiring K]

private theorem affineDimension_le_fiber_generators {β : Type*}
    (P : MvPolynomial σ K) (q : (σ →₀ ℕ) → β) (v : σ →₀ ℚ)
    (hfiber : ∀ x y, q x = q y → ∃ t : ℚ,
      rationalExponent x - rationalExponent y = t • v)
    (R : Finset (σ →₀ ℕ)) (hcover : P.support.image q ⊆ R.image q)
    (b : σ →₀ ℕ) (G : Finset (σ →₀ ℚ))
    (hv : v ∈ Submodule.span ℚ (G : Set (σ →₀ ℚ)))
    (hR : ∀ r ∈ R, rationalExponent r - rationalExponent b ∈
      Submodule.span ℚ (G : Set (σ →₀ ℚ))) :
    affineDimension P ≤ G.card := by
  classical
  let W := Submodule.span ℚ (G : Set (σ →₀ ℚ))
  have hbase (x : σ →₀ ℕ) (hx : x ∈ P.support) :
      rationalExponent x - rationalExponent b ∈ W := by
    obtain ⟨r, hr, hqr⟩ := Finset.mem_image.mp (hcover (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    obtain ⟨t, ht⟩ := hfiber x r hqr.symm
    have heq : rationalExponent x - rationalExponent b =
        t • v + (rationalExponent r - rationalExponent b) := by
      rw [← ht]
      abel
    rw [heq]
    exact W.add_mem (W.smul_mem t hv) (hR r hr)
  have hspan : affineDifferenceSpan P ≤ W := by
    apply Submodule.span_le.mpr
    rintro x ⟨a, ha, c, hc, rfl⟩
    have h := W.sub_mem (hbase a ha) (hbase c hc)
    simpa only [sub_sub_sub_cancel_right] using h
  exact (Submodule.finrank_mono hspan).trans (finrank_span_finset_le_card G)

/-- A finite exponent support of affine dimension `d` occupies at least `d`
rational affine lines in every nonzero binomial direction. -/
theorem affineDimension_le_binomialLineCount (P : MvPolynomial σ K)
    (a b : σ →₀ ℕ) (j : σ) (hj : a j ≠ b j) :
    affineDimension P ≤ (P.support.image (binomialLineProjection a b j)).card := by
  classical
  by_cases hP : P = 0
  · subst P
    have hspan : affineDifferenceSpan (0 : MvPolynomial σ K) = ⊥ := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro x ⟨u, hu, v, hv, heq⟩
        exact False.elim ((Finsupp.notMem_support_iff.mpr rfl) hu)
      · exact bot_le
    simp [affineDimension, hspan]
  obtain ⟨c, hc⟩ := Finsupp.support_nonempty_iff.mpr hP
  let q := binomialLineProjection a b j
  let v := rationalExponent b - rationalExponent a
  obtain ⟨R, hRS, hcR, hqR, hcover, hcard⟩ :=
    exists_finite_fiber_representatives P.support q {c}
      (by simpa using hc) (by simpa using Set.injOn_singleton q c)
  have hcR' : c ∈ R := hcR (by simp)
  let G := insert v ((R.erase c).image (fun r => rationalExponent r - rationalExponent c))
  have hdim : affineDimension P ≤ G.card := by
    apply affineDimension_le_fiber_generators P q v
      (fun x y hxy => (binomialLineProjection_eq_iff a b x y j hj).mp hxy)
      R (by rw [hcover]) c G
    · exact Submodule.subset_span (Finset.mem_insert_self _ _)
    · intro r hr
      by_cases hrc : r = c
      · subst r
        simp
      · apply Submodule.subset_span
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨r, Finset.mem_erase.mpr ⟨hrc, hr⟩, rfl⟩)
  have hG : G.card ≤ (R.erase c).card + 1 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
  have hcCard := Finset.card_erase_add_one hcR'
  change affineDimension P ≤ (P.support.image q).card
  omega

/-- Collinearity transverse to the fiber direction makes projection
injective on the collinear subset. -/
theorem binomialLineProjection_injOn_collinear (a b : σ →₀ ℕ) (j : σ)
    (hj : a j ≠ b j) (T : Finset (σ →₀ ℕ)) (c : σ →₀ ℕ) (v : σ →₀ ℚ)
    (hline : ∀ x ∈ T, ∃ t : ℚ,
      rationalExponent x - rationalExponent c = t • v)
    (htrans : ¬ ∃ t : ℚ, v = t • (rationalExponent b - rationalExponent a)) :
    Set.InjOn (binomialLineProjection a b j) (T : Set (σ →₀ ℕ)) := by
  intro x hx y hy hxy
  obtain ⟨s, hs⟩ := hline x hx
  obtain ⟨t, ht⟩ := hline y hy
  obtain ⟨u, hu⟩ := (binomialLineProjection_eq_iff a b x y j hj).mp hxy
  have hdiff : rationalExponent x - rationalExponent y = (s - t) • v := by
    calc
      _ = (rationalExponent x - rationalExponent c) -
          (rationalExponent y - rationalExponent c) := by abel
      _ = _ := by rw [hs, ht, sub_smul]
  by_cases hst : s - t = 0
  · apply rationalExponent_injective
    apply sub_eq_zero.mp
    simpa only [hst, zero_smul] using hdiff
  · apply False.elim
    apply htrans
    refine ⟨(s - t)⁻¹ * u, ?_⟩
    calc
      v = (s - t)⁻¹ • ((s - t) • v) := (inv_smul_smul₀ hst v).symm
      _ = (s - t)⁻¹ • (u • (rationalExponent b - rationalExponent a)) := by
        rw [← hdiff, hu]
      _ = _ := by rw [smul_smul]

/-- Every prescribed collinear point beyond the first two saves one
generator in the occupied-line bound. -/
theorem affineDimension_add_collinear_card_le_binomialLineCount_add_two
    (P : MvPolynomial σ K) (a b : σ →₀ ℕ) (j : σ) (hj : a j ≠ b j)
    (T : Finset (σ →₀ ℕ)) (hT : T ⊆ P.support)
    (c : σ →₀ ℕ) (v : σ →₀ ℚ)
    (hline : ∀ x ∈ T, ∃ t : ℚ,
      rationalExponent x - rationalExponent c = t • v)
    (htrans : ¬ ∃ t : ℚ, v = t • (rationalExponent b - rationalExponent a)) :
    affineDimension P + T.card ≤
      (P.support.image (binomialLineProjection a b j)).card + 2 := by
  classical
  let q := binomialLineProjection a b j
  let w := rationalExponent b - rationalExponent a
  have hqT := binomialLineProjection_injOn_collinear a b j hj T c v hline htrans
  obtain ⟨R, hRS, hTR, hqR, hcover, hcard⟩ :=
    exists_finite_fiber_representatives P.support q T hT hqT
  let G := insert w (insert v ((R \ T).image
    (fun r => rationalExponent r - rationalExponent c)))
  have hdim : affineDimension P ≤ G.card := by
    apply affineDimension_le_fiber_generators P q w
      (fun x y hxy => (binomialLineProjection_eq_iff a b x y j hj).mp hxy)
      R (by rw [hcover]) c G
    · exact Submodule.subset_span (Finset.mem_insert_self _ _)
    · intro r hr
      by_cases hrT : r ∈ T
      · obtain ⟨t, ht⟩ := hline r hrT
        rw [ht]
        apply Submodule.smul_mem
        exact Submodule.subset_span (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      · apply Submodule.subset_span
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨r, Finset.mem_sdiff.mpr ⟨hr, hrT⟩, rfl⟩))
  have hG : G.card ≤ (R \ T).card + 2 := by
    have h₁ := Finset.card_insert_le w (insert v ((R \ T).image
      (fun r => rationalExponent r - rationalExponent c)))
    have h₂ := Finset.card_insert_le v ((R \ T).image
      (fun r => rationalExponent r - rationalExponent c))
    have h₃ : ((R \ T).image (fun r => rationalExponent r - rationalExponent c)).card ≤
        (R \ T).card := Finset.card_image_le
    dsimp [G]
    omega
  have hpartition := Finset.card_sdiff_add_card_eq_card hTR
  change affineDimension P + T.card ≤ (P.support.image q).card + 2
  omega

/-- Four distinct collinear support points, whose line is not parallel to
the binomial direction, force at least `d+2` occupied lines. -/
theorem affineDimension_add_two_le_binomialLineCount_of_four_collinear
    (P : MvPolynomial σ K) (a b : σ →₀ ℕ) (j : σ) (hj : a j ≠ b j)
    (T : Finset (σ →₀ ℕ)) (hT : T ⊆ P.support) (hfour : 4 ≤ T.card)
    (hcol : Collinear ℚ (rationalExponent '' (T : Set (σ →₀ ℕ))))
    (c d : σ →₀ ℕ) (hc : c ∈ T) (hd : d ∈ T)
    (htrans : ¬ ∃ t : ℚ, rationalExponent d - rationalExponent c =
      t • (rationalExponent b - rationalExponent a)) :
    affineDimension P + 2 ≤
      (P.support.image (binomialLineProjection a b j)).card := by
  classical
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (k := ℚ)
    (Set.mem_image_of_mem rationalExponent hc)).mp hcol
  have hline (x : σ →₀ ℕ) (hx : x ∈ T) :
      ∃ t : ℚ, rationalExponent x - rationalExponent c = t • v := by
    obtain ⟨t, ht⟩ := hv _ (Set.mem_image_of_mem rationalExponent hx)
    refine ⟨t, ?_⟩
    change rationalExponent x = t • v + rationalExponent c at ht
    exact sub_eq_iff_eq_add.mpr ht
  have hvtrans : ¬ ∃ t : ℚ, v = t • (rationalExponent b - rationalExponent a) := by
    rintro ⟨t, ht⟩
    obtain ⟨s, hs⟩ := hline d hd
    apply htrans
    refine ⟨s * t, ?_⟩
    rw [hs, ht, smul_smul]
  have h := affineDimension_add_collinear_card_le_binomialLineCount_add_two
    P a b j hj T hT c v hline hvtrans
  omega

end WeightedPilz
