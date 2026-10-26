import WeightedPilz.Support
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring

/-! The two extreme terms on every occupied line survive multiplication by
a binomial. The projection is arbitrary: no lattice basis is required. -/

noncomputable section
namespace WeightedPilz

open MvPolynomial
attribute [local instance] Classical.propDecidable

private theorem two_shift_boundary_card {E A : Type*}
    [AddCommMonoid E] [AddCancelCommMonoid A] [DecidableEq E] [DecidableEq A]
    (S : Finset E) (q : E →+ A) (h : E →+ ℕ) (a b : E)
    (hq : q a = q b) (hab : h a < h b) :
    2 * (S.image q).card ≤
      ((S.image (a + ·) \ S.image (b + ·)) ∪
        (S.image (b + ·) \ S.image (a + ·))).card := by
  classical
  let T := S.image q
  let fiber (x : T) := S.filter (fun e => q e = x.val)
  have hne (x : T) : (fiber x).Nonempty := by
    obtain ⟨e, he, hq⟩ := Finset.mem_image.mp x.property
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hq⟩⟩
  choose lo hlo using fun x : T => (fiber x).exists_min_image h (hne x)
  choose hi hhi using fun x : T => (fiber x).exists_max_image h (hne x)
  have hloS (x : T) : lo x ∈ S := (Finset.mem_filter.mp (hlo x).1).1
  have hhiS (x : T) : hi x ∈ S := (Finset.mem_filter.mp (hhi x).1).1
  have hloQ (x : T) : q (lo x) = x.val := (Finset.mem_filter.mp (hlo x).1).2
  have hhiQ (x : T) : q (hi x) = x.val := (Finset.mem_filter.mp (hhi x).1).2
  have hlohi (x : T) : h (lo x) ≤ h (hi x) := (hlo x).2 _ (hhi x).1
  let boundary := (S.image (a + ·) \ S.image (b + ·)) ∪
    (S.image (b + ·) \ S.image (a + ·))
  have hlow (x : T) : a + lo x ∈ boundary := by
    apply Finset.mem_union_left
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨lo x, hloS x, rfl⟩, ?_⟩
    intro hm
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
    have hqe : q e = x.val := by
      have hh := congrArg q heq
      rw [map_add, map_add, ← hq, hloQ] at hh
      exact add_left_cancel hh
    have hle := (hlo x).2 e (Finset.mem_filter.mpr ⟨he, hqe⟩)
    have hh := congrArg h heq
    simp only [map_add] at hh
    omega
  have hhigh (x : T) : b + hi x ∈ boundary := by
    apply Finset.mem_union_right
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨hi x, hhiS x, rfl⟩, ?_⟩
    intro hm
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
    have hqe : q e = x.val := by
      have hh := congrArg q heq
      rw [map_add, map_add, ← hq, hhiQ] at hh
      exact add_left_cancel hh
    have hle := (hhi x).2 e (Finset.mem_filter.mpr ⟨he, hqe⟩)
    have hh := congrArg h heq
    simp only [map_add] at hh
    omega
  let endpoint : T ⊕ T → boundary := Sum.elim
    (fun x => ⟨a + lo x, hlow x⟩) (fun x => ⟨b + hi x, hhigh x⟩)
  have hinj : Function.Injective endpoint := by
    intro x y hxy
    have heq := congrArg Subtype.val hxy
    rcases x with x | x <;> rcases y with y | y
    · have hx : x = y := by
        apply Subtype.ext
        have hh := congrArg q heq
        change q (a + lo x) = q (a + lo y) at hh
        simpa only [map_add, hloQ, add_right_inj] using hh
      exact congrArg Sum.inl hx
    · have hx : x = y := by
        apply Subtype.ext
        have hh := congrArg q heq
        change q (a + lo x) = q (b + hi y) at hh
        rw [map_add, map_add, ← hq, hloQ, hhiQ] at hh
        exact add_left_cancel hh
      subst y
      have hh := congrArg h heq
      change h (a + lo x) = h (b + hi x) at hh
      simp only [map_add] at hh
      have := hlohi x
      omega
    · have hx : x = y := by
        apply Subtype.ext
        have hh := congrArg q heq
        change q (b + hi x) = q (a + lo y) at hh
        rw [map_add, map_add, ← hq, hhiQ, hloQ] at hh
        exact add_left_cancel hh
      subst y
      have hh := congrArg h heq
      change h (b + hi x) = h (a + lo x) at hh
      simp only [map_add] at hh
      have := hlohi x
      omega
    · have hx : x = y := by
        apply Subtype.ext
        have hh := congrArg q heq
        change q (b + hi x) = q (b + hi y) at hh
        simpa only [map_add, hhiQ, add_right_inj] using hh
      exact congrArg Sum.inr hx
  have hc := Fintype.card_le_of_injective endpoint hinj
  simpa only [Fintype.card_sum, Fintype.card_coe, ← two_mul, T, boundary] using hc

variable {σ A K : Type*} [Field K] [AddCancelCommMonoid A]

/-- Every occupied fiber of an additive projection that identifies the two
binomial exponents contributes two nonzero product terms. -/
theorem weight_mul_binomial_projection (F : MvPolynomial σ K)
    (a b : σ →₀ ℕ) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hab : a ≠ b)
    (q : (σ →₀ ℕ) →+ A) (hq : q a = q b) :
    2 * (F.support.image q).card ≤ weight (F * (monomial a u + monomial b v)) := by
  classical
  have hsupport (e : σ →₀ ℕ) (c : K) (hc : c ≠ 0) :
      (monomial e c * F).support = F.support.image (e + ·) := by
    have hs := AddMonoidAlgebra.support_single_mul F c (by simp [hc]) e
    simpa only [Finset.map_eq_image, addLeftEmbedding_apply] using hs
  have hboundary : ((F.support.image (a + ·) \ F.support.image (b + ·)) ∪
      (F.support.image (b + ·) \ F.support.image (a + ·))) ⊆
      (F * (monomial a u + monomial b v)).support := by
    rw [mul_add, mul_comm F (monomial a u), mul_comm F (monomial b v)]
    rw [← hsupport a u hu, ← hsupport b v hv]
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact MvPolynomial.support_sdiff_support_subset_support_add _ _ he
    · rw [add_comm]
      exact MvPolynomial.support_sdiff_support_subset_support_add _ _ he
  have hex : ∃ j, a j ≠ b j := by
    by_contra! h
    exact hab (Finsupp.ext h)
  obtain ⟨j, hj⟩ := hex
  let h : (σ →₀ ℕ) →+ ℕ := {
    toFun := fun e => e j
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  rcases lt_or_gt_of_ne hj with hj | hj
  · exact (two_shift_boundary_card F.support q h a b hq hj).trans
      (Finset.card_le_card hboundary)
  · have hc := two_shift_boundary_card F.support q h b a hq.symm hj
    rw [Finset.union_comm] at hc
    exact hc.trans (Finset.card_le_card hboundary)

/-- A certified subset of the support suffices to count occupied lines. -/
theorem weight_mul_binomial_projection_of_subset (F : MvPolynomial σ K)
    (U : Finset (σ →₀ ℕ)) (hU : U ⊆ F.support)
    (a b : σ →₀ ℕ) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hab : a ≠ b)
    (q : (σ →₀ ℕ) →+ A) (hq : q a = q b) :
    2 * (U.image q).card ≤ weight (F * (monomial a u + monomial b v)) := by
  have hc := Finset.card_le_card (Finset.image_subset_image hU (f := q))
  exact (Nat.mul_le_mul_left 2 hc).trans
    (weight_mul_binomial_projection F a b u v hu hv hab q hq)

/-- Integer cross-product coordinates identify precisely the rational lines
parallel to `b-a`, provided coordinate `j` of that direction is nonzero. -/
def binomialLineProjection (a b : σ →₀ ℕ) (j : σ) : (σ →₀ ℕ) →+ (σ → ℤ) where
  toFun e k := ((b j : ℤ) - a j) * e k - (e j : ℤ) * ((b k : ℤ) - a k)
  map_zero' := by ext k; simp
  map_add' e f := by
    ext k
    simp only [Finsupp.add_apply, Nat.cast_add, Pi.add_apply]
    ring

theorem binomialLineProjection_eq (a b : σ →₀ ℕ) (j : σ) :
    binomialLineProjection a b j a = binomialLineProjection a b j b := by
  ext k
  change ((b j : ℤ) - a j) * a k - (a j : ℤ) * ((b k : ℤ) - a k) =
    ((b j : ℤ) - a j) * b k - (b j : ℤ) * ((b k : ℤ) - a k)
  ring

theorem weight_mul_binomial_lines (F : MvPolynomial σ K)
    (a b : σ →₀ ℕ) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hab : a ≠ b) (j : σ) :
    2 * (F.support.image (binomialLineProjection a b j)).card ≤
      weight (F * (monomial a u + monomial b v)) :=
  weight_mul_binomial_projection F a b u v hu hv hab _ (binomialLineProjection_eq a b j)

end WeightedPilz
