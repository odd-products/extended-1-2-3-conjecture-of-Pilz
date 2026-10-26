import WeightedPilz.Frobenius

/-!
# Strict descent in the total width of a multiplier

These are the well-ordering and extraction steps of `lem:width-descent`.
The geometric facts supplying positive base width and scalar compression
are separate obligations; neither is assumed as an instance or an axiom.
-/

noncomputable section

namespace WeightedPilz

open MvPolynomial

variable {σ K : Type*} [Field K] [DecidableEq σ]

/-- Choose an actual counterexample of minimum total cofactor width. -/
theorem exists_minimal_width_counterexample (B : Finset σ)
    (P : MvPolynomial σ K) (N : ℕ)
    (h : ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (P * H) < N) :
    ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (P * H) < N ∧
      ∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth B J < totalWidth B H →
        N ≤ weight (P * J) := by
  classical
  have hex : ∃ b : ℕ, ∃ H : MvPolynomial σ K,
      H ≠ 0 ∧ weight (P * H) < N ∧ totalWidth B H = b := by
    obtain ⟨H, hH, hshort⟩ := h
    exact ⟨totalWidth B H, H, hH, hshort, rfl⟩
  obtain ⟨H, hH, hshort, hwidth⟩ := Nat.find_spec hex
  refine ⟨H, hH, hshort, ?_⟩
  intro J hJ hsmaller
  by_contra! hshortJ
  have hle : Nat.find hex ≤ totalWidth B J :=
    Nat.find_min' hex ⟨J, hJ, hshortJ, rfl⟩
  omega

/-- If width-zero inputs meet the bound, the chosen minimum counterexample
has strictly positive base width. -/
theorem exists_positive_minimal_width_counterexample (B : Finset σ)
    (P : MvPolynomial σ K) (N : ℕ)
    (hzero : ∀ H : MvPolynomial σ K, H ≠ 0 → totalWidth B H = 0 →
      N ≤ weight (P * H))
    (h : ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (P * H) < N) :
    ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (P * H) < N ∧
      0 < totalWidth B H ∧
      ∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth B J < totalWidth B H →
        N ≤ weight (P * J) := by
  obtain ⟨H, hH, hshort, hmin⟩ := exists_minimal_width_counterexample B P N h
  refine ⟨H, hH, hshort, ?_, hmin⟩
  by_contra! hz
  have hbound := hzero H hH (Nat.eq_zero_of_le_zero hz)
  omega

/-- Any compression that decreases output weight and base width preserves
the chosen minimum cofactor width. -/
theorem minimal_width_preserved_by_compression (B : Finset σ)
    (P H J : MvPolynomial σ K) (N : ℕ)
    (hP : P ≠ 0) (hH : H ≠ 0) (hJ : J ≠ 0)
    (hshort : weight (P * H) < N)
    (hmin : ∀ D : MvPolynomial σ K, D ≠ 0 → totalWidth B D < totalWidth B H →
      N ≤ weight (P * D))
    (hweight : weight (P * J) ≤ weight (P * H))
    (hwidth : totalWidth B (P * J) ≤ totalWidth B (P * H)) :
    totalWidth B J = totalWidth B H := by
  rw [totalWidth_mul B hP hJ, totalWidth_mul B hP hH] at hwidth
  have hupper : totalWidth B J ≤ totalWidth B H := by omega
  by_contra hne
  have hstrict : totalWidth B J < totalWidth B H := by omega
  have hbound := hmin J hJ hstrict
  omega

/-- The Frobenius support extraction strictly decreases total base cofactor
width under the displayed correction-width hypothesis of the manuscript. -/
theorem frobenius_strict_width_extraction (p e : ℕ) [ExpChar K p]
    (hq : 1 < p ^ e) (B : Finset σ) (P H E : MvPolynomial σ K)
    (α : σ →₀ ℕ) (hP : P ≠ 0) (hH : H ≠ 0)
    (hpos : 0 < totalWidth B H)
    (hclass : residuePart (p ^ e) (P ^ p ^ e * E) α ≠ 0)
    (hwidth : ∀ i ∈ B, widthOf i (P ^ p ^ e * E) ≤
      widthOf i (P * H) + (p ^ e - 1) * widthOf i P) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      weight (P * J) ≤ weight (residuePart (p ^ e) (P ^ p ^ e * E) α) ∧
      p ^ e * totalWidth B J ≤ totalWidth B H ∧
      totalWidth B J < totalWidth B H := by
  classical
  obtain ⟨J, hJ, hPJ, _, hs⟩ := frobenius_extraction_residue p e P E α hclass
  have hqpos : 0 < p ^ e := lt_trans Nat.zero_lt_one hq
  have hwt : weight (P * J) ≤ weight (residuePart (p ^ e) (P ^ p ^ e * E) α) := by
    have hinj : Function.Injective (fun d : σ →₀ ℕ => α + scaleExponent (p ^ e) d) :=
      (add_right_injective α).comp (scaleExponent_injective hqpos)
    have himage : (P * J).support.image (fun d => α + scaleExponent (p ^ e) d) ⊆
        (residuePart (p ^ e) (P ^ p ^ e * E) α).support := by
      intro d hd
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
      exact hs a ha
    have hc := Finset.card_le_card himage
    rwa [Finset.card_image_of_injective _ hinj] at hc
  have hcoord : ∀ i ∈ B, p ^ e * widthOf i J ≤ widthOf i H := by
    intro i hi
    have hscaled := scaled_width_le_of_support_image (p ^ e) i (P * J)
      (residuePart (p ^ e) (P ^ p ^ e * E) α) α hPJ hs
    have hsubset := widthOf_mono_support i hclass
      (support_residuePart_subset (p ^ e) (P ^ p ^ e * E) α)
    have hbound := hwidth i hi
    rw [widthOf_mul i hP hJ] at hscaled
    rw [widthOf_mul i hP hH] at hbound
    have hmul : widthOf i P ≤ p ^ e * widthOf i P := by
      simpa using Nat.mul_le_mul_right (widthOf i P) (Nat.le_of_lt hq)
    simp only [Nat.mul_add] at hscaled
    simp only [Nat.sub_mul, Nat.one_mul] at hbound
    omega
  have htotal : p ^ e * totalWidth B J ≤ totalWidth B H := by
    simpa only [totalWidth, Finset.mul_sum] using Finset.sum_le_sum hcoord
  refine ⟨J, hJ, hPJ, hwt, htotal, ?_⟩
  by_contra! hle
  have hmul := Nat.mul_le_mul_left (p ^ e) hle
  have hstrict := Nat.mul_lt_mul_of_pos_right hq hpos
  simp only [Nat.one_mul] at hstrict
  omega

/-- Every nonzero correction residue class meets the target bound once the
original counterexample is chosen with positive, minimum base width. -/
theorem correction_residue_bound_of_minimal_width (p e : ℕ) [ExpChar K p]
    (hq : 1 < p ^ e) (B : Finset σ) (P H E : MvPolynomial σ K)
    (α : σ →₀ ℕ) (N : ℕ) (hP : P ≠ 0) (hH : H ≠ 0)
    (hpos : 0 < totalWidth B H)
    (hmin : ∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth B J < totalWidth B H →
      N ≤ weight (P * J))
    (hclass : residuePart (p ^ e) (P ^ p ^ e * E) α ≠ 0)
    (hwidth : ∀ i ∈ B, widthOf i (P ^ p ^ e * E) ≤
      widthOf i (P * H) + (p ^ e - 1) * widthOf i P) :
    N ≤ weight (residuePart (p ^ e) (P ^ p ^ e * E) α) := by
  obtain ⟨J, hJ, _, hwt, _, hstrict⟩ :=
    frobenius_strict_width_extraction p e hq B P H E α hP hH hpos hclass hwidth
  exact (hmin J hJ hstrict).trans hwt

/-- Translate the manuscript's separate lower-order and upper-degree bounds
into the width inequality used by strict descent. -/
theorem correction_width_bound_of_exponent_bounds (q : ℕ) (i : σ)
    (P G U : MvPolynomial σ K) (hPorder : orderOf i P = 0)
    (horder : orderOf i G ≤ orderOf i U)
    (hdegree : U.degreeOf i ≤ G.degreeOf i + (q - 1) * P.degreeOf i) :
    widthOf i U ≤ widthOf i G + (q - 1) * widthOf i P := by
  have hG := orderOf_le_degreeOf i G
  simp only [widthOf, hPorder, Nat.sub_zero]
  omega

/-- The exact correction-class consequence of `eq:descent-exponent-bounds`.
The fresh-variable geometry supplies the premise that the base orders of
`P` vanish, while the choice of minimum width supplies `hmin`. -/
theorem correction_residue_bound_of_exponent_bounds (p e : ℕ) [ExpChar K p]
    (hq : 1 < p ^ e) (B : Finset σ) (P H E : MvPolynomial σ K)
    (α : σ →₀ ℕ) (N : ℕ) (hP : P ≠ 0) (hH : H ≠ 0)
    (hpos : 0 < totalWidth B H)
    (hmin : ∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth B J < totalWidth B H →
      N ≤ weight (P * J))
    (hclass : residuePart (p ^ e) (P ^ p ^ e * E) α ≠ 0)
    (hPorder : ∀ i ∈ B, orderOf i P = 0)
    (horder : ∀ i ∈ B, orderOf i (P * H) ≤ orderOf i (P ^ p ^ e * E))
    (hdegree : ∀ i ∈ B, (P ^ p ^ e * E).degreeOf i ≤
      (P * H).degreeOf i + (p ^ e - 1) * P.degreeOf i) :
    N ≤ weight (residuePart (p ^ e) (P ^ p ^ e * E) α) := by
  apply correction_residue_bound_of_minimal_width p e hq B P H E α N hP hH hpos hmin hclass
  intro i hi
  exact correction_width_bound_of_exponent_bounds (p ^ e) i P (P * H) (P ^ p ^ e * E)
    (hPorder i hi) (horder i hi) (hdegree i hi)

end WeightedPilz
