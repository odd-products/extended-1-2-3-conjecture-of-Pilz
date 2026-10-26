import WeightedPilz.DilationOverlap

/-! Rowwise overlap of unequal dilates. The projection may have any number
of fresh coordinates; coefficients may use any independent base variables. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [DecidableEq σ] [DecidableEq τ] [CommSemiring R]

/-- The vertices of the standard exponent simplex, including its origin. -/
def exponentSimplex (V : Finset σ) : Finset (σ →₀ ℕ) :=
  insert 0 (V.image (fun i => Finsupp.single i 1))

theorem exponentSimplex_coordinate_le_one (V : Finset σ)
    {d : σ →₀ ℕ} (hd : d ∈ exponentSimplex V) (i : σ) : d i ≤ 1 := by
  rcases Finset.mem_insert.mp hd with rfl | hd
  · simp
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    by_cases h : j = i <;> simp [h, Finsupp.single_apply]

private theorem small_scaled_intersections (m q a b x y x' y' : ℕ)
    (hm : 0 < m) (hq : 0 < q) (hx : x < q) (hx' : x' < q)
    (h : a + m * x = b + (m * q) * y)
    (h' : a + m * x' = b + (m * q) * y') : x = x' ∧ y = y' := by
  have hmul : m * (x + q * y') = m * (x' + q * y) := by
    calc
      _ = m * x + (m * q) * y' := by ring
      _ = m * x' + (m * q) * y := by omega
      _ = _ := by ring
  have hc := Nat.eq_of_mul_eq_mul_left hm hmul
  have hr := congrArg (fun n : ℕ => n % q) hc
  have hxx : x = x' := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt hx'] using hr
  refine ⟨hxx, ?_⟩
  have hy : (m * q) * y = (m * q) * y' := by
    rw [hxx] at h
    omega
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hm hq) hy

/-- A translate of a simplex and a translate of its larger dilate have at
most one point in common. A common positive dilation is also allowed. -/
theorem translated_simplex_dilate_inter_card_le_one (V W : Finset σ)
    (m q : ℕ) (hm : 0 < m) (hq : 2 ≤ q) (a b : σ →₀ ℕ) :
    (((exponentSimplex V).image (fun d => a + scaleExponent m d)) ∩
      ((exponentSimplex W).image (fun d => b + scaleExponent (m * q) d))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).1
  obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).2
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).1
  obtain ⟨f', hf', hfe'⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).2
  have hee : e = e' := by
    ext i
    have h := congrArg (fun d : σ →₀ ℕ => d i) hfe.symm
    have h' := congrArg (fun d : σ →₀ ℕ => d i) hfe'.symm
    simp only [Finsupp.add_apply, scaleExponent_apply] at h h'
    exact (small_scaled_intersections m q (a i) (b i) (e i) (f i) (e' i) (f' i)
      hm (by omega) (by have := exponentSimplex_coordinate_le_one V he i; omega)
      (by have := exponentSimplex_coordinate_le_one V he' i; omega) h h').1
  rw [hee]

/-- One row of a polynomial with respect to an additive exponent projection. -/
def projectedRow (π : (σ →₀ ℕ) →+ (τ →₀ ℕ)) (β : τ →₀ ℕ)
    (P : MvPolynomial σ R) : MvPolynomial σ R := by
  classical
  exact P.filter (fun d => π d = β)

theorem support_projectedRow (π : (σ →₀ ℕ) →+ (τ →₀ ℕ)) (β : τ →₀ ℕ)
    (P : MvPolynomial σ R) :
    (projectedRow π β P).support = P.support.filter (fun d => π d = β) := by
  classical
  rfl

/-- If the smaller support projects into one residue box, all overlaps
come from one pair of projected rows. Their size is bounded by either row,
and also by the largest residue class of the smaller row. -/
theorem translated_dilate_overlap_rows
    (π : (σ →₀ ℕ) →+ (τ →₀ ℕ)) (P Q : MvPolynomial σ R)
    (m q : ℕ) (hm : 0 < m) (hq : 0 < q)
    (hsmall : ∀ d ∈ P.support, ∀ i, π d i < q) (a b : σ →₀ ℕ)
    (hI : ((P.support.image (fun d => a + scaleExponent m d)) ∩
      (Q.support.image (fun d => b + scaleExponent (m * q) d))).Nonempty) :
    ∃ β ∈ P.support.image π, ∃ γ ∈ Q.support.image π,
      (P.support.image (fun d => a + scaleExponent m d)) ∩
          (Q.support.image (fun d => b + scaleExponent (m * q) d)) ⊆
        ((projectedRow π β P).support.image (fun d => a + scaleExponent m d)) ∩
          ((projectedRow π γ Q).support.image (fun d => b + scaleExponent (m * q) d)) ∧
      (((P.support.image (fun d => a + scaleExponent m d)) ∩
        (Q.support.image (fun d => b + scaleExponent (m * q) d))).card ≤
          min (weight (projectedRow π β P)) (weight (projectedRow π γ Q))) ∧
      (((P.support.image (fun d => a + scaleExponent m d)) ∩
        (Q.support.image (fun d => b + scaleExponent (m * q) d))).card ≤
          residueSigma q (projectedRow π β P)) := by
  classical
  let I := (P.support.image (fun d => a + scaleExponent m d)) ∩
    (Q.support.image (fun d => b + scaleExponent (m * q) d))
  obtain ⟨z, hz⟩ := hI
  obtain ⟨e₀, he₀, hez⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).1
  obtain ⟨f₀, hf₀, hfz⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).2
  have hbase := congrArg π (hez.trans hfz.symm)
  simp only [map_add, scaleExponent, map_nsmul] at hbase
  have hrows {e f : σ →₀ ℕ} (he : e ∈ P.support)
      (hef : a + scaleExponent m e = b + scaleExponent (m * q) f) :
      π e = π e₀ ∧ π f = π f₀ := by
    have hp := congrArg π hef
    simp only [map_add, scaleExponent, map_nsmul] at hp
    have hcoord (i : τ) : π e i = π e₀ i ∧ π f i = π f₀ i := by
      have hh := congrArg (fun d : τ →₀ ℕ => d i) hp
      have hh₀ := congrArg (fun d : τ →₀ ℕ => d i) hbase
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hh hh₀
      exact small_scaled_intersections m q (π a i) (π b i) (π e i) (π f i)
        (π e₀ i) (π f₀ i) hm hq (hsmall e he i) (hsmall e₀ he₀ i) hh hh₀
    exact ⟨Finsupp.ext (fun i => (hcoord i).1), Finsupp.ext (fun i => (hcoord i).2)⟩
  have hsub : I ⊆
      ((projectedRow π (π e₀) P).support.image (fun d => a + scaleExponent m d)) ∩
      ((projectedRow π (π f₀) Q).support.image (fun d => b + scaleExponent (m * q) d)) := by
    intro x hx
    obtain ⟨e, he, hex⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).1
    obtain ⟨f, hf, hfx⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).2
    have hh := hrows he (hex.trans hfx.symm)
    apply Finset.mem_inter.mpr
    constructor
    · refine Finset.mem_image.mpr ⟨e, ?_, hex⟩
      rw [support_projectedRow]
      exact Finset.mem_filter.mpr ⟨he, hh.1⟩
    · refine Finset.mem_image.mpr ⟨f, ?_, hfx⟩
      rw [support_projectedRow]
      exact Finset.mem_filter.mpr ⟨hf, hh.2⟩
  refine ⟨π e₀, Finset.mem_image.mpr ⟨e₀, he₀, rfl⟩,
    π f₀, Finset.mem_image.mpr ⟨f₀, hf₀, rfl⟩, hsub, ?_, ?_⟩
  · apply le_min
    · exact (Finset.card_le_card (hsub.trans Finset.inter_subset_left)).trans
        Finset.card_image_le
    · exact (Finset.card_le_card (hsub.trans Finset.inter_subset_right)).trans
        Finset.card_image_le
  · exact (Finset.card_le_card hsub).trans
      (translated_dilate_inter_card_le (projectedRow π (π e₀) P)
        (projectedRow π (π f₀) Q).support m q hm a b)

end WeightedPilz
