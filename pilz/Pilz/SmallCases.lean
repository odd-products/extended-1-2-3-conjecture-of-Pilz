import Pilz.Endpoints
import Pilz.Parity
import Pilz.OddProduct
import Mathlib.Tactic.Ring

/-!
# The first interval lengths and the paper's small cores

The proofs at lengths three and four follow the paper: pure endpoints give
three terms, and parity improves the bound to four for `F₄`.
-/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

theorem coeff_interval_constant {n : ℕ} (hn : 0 < n) :
    coeff 0 (interval n) = 1 := by
  have hpos : ∀ a ∈ Finset.Icc 1 n, 0 < a :=
    fun a ha => (Finset.mem_Icc.mp ha).1
  have h := coeff_polynomialOf (Finset.Icc 1 n) hpos (a := 1) (by decide)
  simpa [← interval_eq_polynomialOf, show 1 ≤ n by omega] using h

theorem coeff_interval_prime {n p : ℕ} (hp : Nat.Prime p) (hpn : p ≤ n) :
    coeff (Finsupp.single p 1) (interval n) = 1 := by
  have hpos : ∀ a ∈ Finset.Icc 1 n, 0 < a :=
    fun a ha => (Finset.mem_Icc.mp ha).1
  have h := coeff_polynomialOf (Finset.Icc 1 n) hpos (a := p) hp.pos
  rw [hp.factorization] at h
  simpa [← interval_eq_polynomialOf, hp.one_lt.le, hpn] using h

theorem interval_two : interval 2 = 1 + X 2 := by
  calc
    interval 2 = interval 1 + monomialOf 2 := interval_succ 1
    _ = 1 + X 2 := by rw [interval_one, monomialOf_prime (by decide : Nat.Prime 2)]

theorem interval_three : interval 3 = 1 + X 2 + X 3 := by
  calc
    interval 3 = interval 2 + monomialOf 3 := interval_succ 2
    _ = 1 + X 2 + X 3 := by rw [interval_two, monomialOf_prime (by decide : Nat.Prime 3)]

theorem monomialOf_four : monomialOf 4 = (X 2 : Poly) ^ 2 := by
  calc
    monomialOf 4 = monomialOf 2 * monomialOf 2 :=
      monomialOf_mul (a := 2) (b := 2) (by decide) (by decide)
    _ = X 2 ^ 2 := by rw [monomialOf_prime (by decide : Nat.Prime 2), pow_two]

theorem interval_four : interval 4 = 1 + X 2 + X 2 ^ 2 + X 3 := by
  calc
    interval 4 = interval 3 + monomialOf 4 := interval_succ 3
    _ = 1 + X 2 + X 2 ^ 2 + X 3 := by rw [interval_three, monomialOf_four]; ac_rfl

/-- The endpoint estimate used for both `n=3` and `n=4`. -/
theorem three_le_weight_interval_mul {n : ℕ} (hn : 3 ≤ n)
    (H : Poly) (hH : H ≠ 0) : 3 ≤ weight (interval n * H) := by
  have h0 : coeff 0 (interval n) ≠ 0 := by
    rw [coeff_interval_constant (by omega)]
    exact one_ne_zero
  have hpure : ∀ p ∈ ({2, 3} : Finset ℕ), ∃ k : ℕ, 0 < k ∧
      coeff (Finsupp.single p k) (interval n) ≠ 0 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact ⟨1, by decide, by
        rw [coeff_interval_prime (by decide : Nat.Prime 2) (by omega)]
        exact one_ne_zero⟩
    · exact ⟨1, by decide, by
        rw [coeff_interval_prime (by decide : Nat.Prime 3) hn]
        exact one_ne_zero⟩
  have h := pure_endpoints_weight_mul ({2, 3} : Finset ℕ) (interval n) H h0 hpure hH
  simpa [termWeight, weight] using h

theorem conjectureAt_three : ConjectureAt 3 :=
  three_le_weight_interval_mul (by decide)

theorem conjectureAt_four : ConjectureAt 4 := by
  intro H hH
  have hthree := three_le_weight_interval_mul (n := 4) (by decide) H hH
  have heven : Even (weight (interval 4 * H)) := by
    apply even_weight_mul
    rw [weight_interval]
    decide
  obtain ⟨k, hk⟩ := heven
  omega

theorem conjectureAt_le_four (n : ℕ) (hn : n ≤ 4) : ConjectureAt n := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact conjectureAt_zero
  · exact conjectureAt_one
  · exact conjectureAt_two
  · exact conjectureAt_three
  · exact conjectureAt_four

theorem distance_interval_eq_of_conjecture {n : ℕ} (h : ConjectureAt n) :
    distance (interval n) = n := by
  apply Nat.le_antisymm
  · have hupper : distance (interval n) ≤ weight (interval n) := distance_le_termWeight (interval n)
    simpa only [weight_interval] using hupper
  · apply (le_distance_iff (interval n) n).mpr
    exact h

theorem distance_interval_le_four (n : ℕ) (hn : n ≤ 4) : distance (interval n) = n :=
  distance_interval_eq_of_conjecture (conjectureAt_le_four n hn)

theorem even_distance_of_even_weight {P : Poly} (hP : Even (weight P)) :
    Even (distance P) := by
  obtain ⟨H, _hH, hw⟩ := exists_weight_eq_distance P
  have heven := even_weight_mul hP H
  change Even (termWeight (P * H)) at heven
  rw [hw] at heven
  exact heven

/-- The original finite-set statement, unconditionally for all `n ≤ 4`. -/
theorem oddProduct_interval_lower_bound_le_four (n : ℕ) (hn : n ≤ 4)
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    n ≤ (oddProduct A (Finset.Icc 1 n)).card :=
  oddProduct_interval_lower_bound (conjectureAt_le_four n hn) A hA hne

namespace SmallCore

def cAt (x : Poly) (k : ℕ) : Poly := ∑ i ∈ Finset.range (k + 1), x ^ i
def c (k : ℕ) : Poly := cAt (X 2) k

def f9At (x y : Poly) : Poly := cAt x 3 + cAt x 1 * y + y ^ 2
def f12At (x y : Poly) : Poly := cAt x 3 + cAt x 2 * y + y ^ 2
def f16At (x y : Poly) : Poly := cAt x 4 + cAt x 2 * y + y ^ 2
def f18At (x y : Poly) : Poly := cAt x 4 + cAt x 2 * y + cAt x 1 * y ^ 2
def f24At (x y : Poly) : Poly := cAt x 4 + cAt x 3 * y + cAt x 1 * y ^ 2
def f25At (x y z : Poly) : Poly := f24At x y + z * (cAt x 2 + y) + z ^ 2

def f9 : Poly := f9At (X 2) (X 3)
def f12 : Poly := f12At (X 2) (X 3)
def f16 : Poly := f16At (X 2) (X 3)
def f18 : Poly := f18At (X 2) (X 3)
def f24 : Poly := f24At (X 2) (X 3)
def f25 : Poly := f25At (X 2) (X 3) (X 5)

@[simp] theorem cAt_zero (x : Poly) : cAt x 0 = 1 := by simp [cAt]
theorem cAt_succ (x : Poly) (k : ℕ) : cAt x (k + 1) = cAt x k + x ^ (k + 1) := by
  exact Finset.sum_range_succ (fun i => x ^ i) (k + 1)

theorem cAt_one (x : Poly) : cAt x 1 = 1 + x := by simp [cAt, Finset.sum_range_succ]
theorem cAt_two (x : Poly) : cAt x 2 = 1 + x + x ^ 2 := by
  simp [cAt, Finset.sum_range_succ]
theorem cAt_three (x : Poly) : cAt x 3 = 1 + x + x ^ 2 + x ^ 3 := by
  simp [cAt, Finset.sum_range_succ]
theorem cAt_four (x : Poly) : cAt x 4 = 1 + x + x ^ 2 + x ^ 3 + x ^ 4 := by
  simp [cAt, Finset.sum_range_succ]

theorem interval_two_eq_c : interval 2 = c 1 := by rw [interval_two, c, cAt_one]
theorem interval_three_eq_c : interval 3 = c 1 + X 3 := by
  rw [interval_three, c, cAt_one]
theorem interval_four_eq_c : interval 4 = c 2 + X 3 := by
  rw [interval_four, c, cAt_two]

/-- Coefficient correspondence for a mixed `x₂^a x₃^b` monomial. -/
theorem coordinate_coeff_mixed (P : Poly) (a b : ℕ) :
    coeff (Finsupp.single (⟨2, by decide⟩ : {p : ℕ // p ≠ 3}) a)
      ((coordinateEquiv 3 P).coeff b) =
      coeff (Finsupp.single 2 a + Finsupp.single 3 b) P := by
  have h := coordinate_coeff_coeff 3 P (Finsupp.single 2 a + Finsupp.single 3 b)
  simpa [Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    Equiv.optionSubtypeNe_symm_of_ne (by decide : 2 ≠ 3),
    Equiv.optionSubtypeNe_symm_self, Finsupp.some_add,
    Finsupp.some_single_some, Finsupp.some_single_none, Finsupp.add_apply] using h

/-- A row with a constant and an `x₂` term has distance at least two. -/
theorem coordinate_row_distance_two (P : Poly) (k : ℕ)
    (h0 : coeff (Finsupp.single 3 k) P ≠ 0)
    (hx : coeff (Finsupp.single 2 1 + Finsupp.single 3 k) P ≠ 0) :
    2 ≤ distance ((coordinateEquiv 3 P).coeff k) := by
  let q : {p : ℕ // p ≠ 3} := ⟨2, by decide⟩
  have hc : coeff 0 ((coordinateEquiv 3 P).coeff k) ≠ 0 := by
    rw [coordinate_coeff_pure_self]
    exact h0
  have hpure : ∀ p ∈ ({q} : Finset {p : ℕ // p ≠ 3}), ∃ j : ℕ, 0 < j ∧
      coeff (Finsupp.single p j) ((coordinateEquiv 3 P).coeff k) ≠ 0 := by
    intro p hp
    simp only [Finset.mem_singleton] at hp
    subst p
    refine ⟨1, by decide, ?_⟩
    exact (coordinate_coeff_mixed P 1 k).trans_ne hx
  simpa using pure_endpoints_distance ({q} : Finset {p : ℕ // p ≠ 3})
    ((coordinateEquiv 3 P).coeff k) hc hpure

/-- The bottom row of `f₂₅` has the three endpoint directions `1,x₂,x₅`. -/
theorem coordinate_bottom_distance_three (P : Poly)
    (h0 : coeff 0 P ≠ 0) (hx : coeff (Finsupp.single 2 1) P ≠ 0)
    (hz : coeff (Finsupp.single 5 1) P ≠ 0) :
    3 ≤ distance ((coordinateEquiv 3 P).coeff 0) := by
  let q : {p : ℕ // p ≠ 3} := ⟨2, by decide⟩
  let r : {p : ℕ // p ≠ 3} := ⟨5, by decide⟩
  have hc : coeff 0 ((coordinateEquiv 3 P).coeff 0) ≠ 0 := by
    rw [coordinate_coeff_zero]
    exact h0
  have hpure : ∀ p ∈ ({q, r} : Finset {p : ℕ // p ≠ 3}), ∃ j : ℕ, 0 < j ∧
      coeff (Finsupp.single p j) ((coordinateEquiv 3 P).coeff 0) ≠ 0 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · refine ⟨1, by decide, ?_⟩
      exact (coordinate_coeff_pure_of_ne 3 2 (by decide) P 1).trans_ne hx
    · refine ⟨1, by decide, ?_⟩
      exact (coordinate_coeff_pure_of_ne 3 5 (by decide) P 1).trans_ne hz
  simpa [q, r] using pure_endpoints_distance ({q, r} : Finset {p : ℕ // p ≠ 3})
    ((coordinateEquiv 3 P).coeff 0) hc hpure

/-- Endpoint slicing for a polynomial quadratic in `x₃`, with independently
established lower bounds on its bottom and top rows. -/
theorem quadratic_endpoints_lower (P : Poly) (a b : ℕ)
    (hdegree : P.degreeOf 3 ≤ 2) (h0 : coeff 0 P ≠ 0)
    (h2 : coeff (Finsupp.single 3 2) P ≠ 0)
    (hlo : a ≤ distance ((coordinateEquiv 3 P).coeff 0))
    (hhi : b ≤ distance ((coordinateEquiv 3 P).coeff 2)) :
    a + b ≤ distance P := by
  let Q := coordinateEquiv 3 P
  have hge : 2 ≤ P.degreeOf 3 := by
    simpa only [Finsupp.single_eq_same] using
      monomial_le_degreeOf 3 (MvPolynomial.mem_support_iff.mpr h2)
  have hdeg : Q.natDegree = 2 := by
    rw [show Q = coordinateEquiv 3 P from rfl, natDegree_coordinateEquiv]
    omega
  have hQ0 : Q.coeff 0 ≠ 0 := by
    intro hz
    have h := coordinate_coeff_zero 3 P
    change coeff 0 (Q.coeff 0) = coeff 0 P at h
    rw [hz, coeff_zero] at h
    exact h0 h.symm
  have htrail : Q.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hQ0)
  have hspan : (coordinateEquiv 3 P).natTrailingDegree <
      (coordinateEquiv 3 P).natDegree := by
    change Q.natTrailingDegree < Q.natDegree
    omega
  have hend := endpoint_distance 3 P hspan
  change distance Q.trailingCoeff + distance Q.leadingCoeff ≤ distance P at hend
  rw [Polynomial.trailingCoeff, Polynomial.leadingCoeff, htrail, hdeg] at hend
  exact (Nat.add_le_add hlo hhi).trans hend

theorem c3_cube_at (x : Poly) : cAt x 3 = cAt x 1 ^ 3 := by
  rw [cAt_three, cAt_one]
  calc
    1 + x + x ^ 2 + x ^ 3 = (1 + x ^ 2) * (1 + x) := by ring
    _ = (1 + x) ^ 2 * (1 + x) := by rw [CharTwo.add_sq, one_pow]
    _ = (1 + x) ^ 3 := by ring

theorem c1_mul_c4_at (x : Poly) : cAt x 1 * cAt x 4 = 1 + x ^ 5 := by
  rw [cAt_one, cAt_four]
  calc
    (1 + x) * (1 + x + x ^ 2 + x ^ 3 + x ^ 4) =
      1 + x ^ 5 + (x + x) + (x ^ 2 + x ^ 2) +
        (x ^ 3 + x ^ 3) + (x ^ 4 + x ^ 4) := by ring
    _ = _ := by simp only [CharTwo.add_self_eq_zero, add_zero]

/-- Equation (f25) in the paper; valid for arbitrary polynomials substituted
for the three variable symbols. -/
theorem f25_alternate_at (x y z : Poly) :
    f25At x y z = f16At x z + (cAt x 3 + z) * y + cAt x 1 * y ^ 2 := by
  unfold f25At f24At f16At
  ring

/-- Any nonzero coefficient at an odd exponent obstructs being a square. -/
theorem coeff_odd_square_zero (P : Poly) (d : ℕ →₀ ℕ) (i : ℕ)
    (hi : d i % 2 = 1) : coeff d (P ^ 2) = 0 := by
  by_contra hn
  have hd := MvPolynomial.mem_support_iff.mpr hn
  have he := exponent_mod_two_of_mem_support_square hd i
  omega

theorem coeff_c_pure (k m : ℕ) (hm : m ≤ k) :
    coeff (Finsupp.single 2 m) (c k) = 1 := by
  have hsingle (i : ℕ) : (Finsupp.single 2 i : ℕ →₀ ℕ) = Finsupp.single 2 m ↔ i = m :=
    (Finsupp.single_injective 2).eq_iff
  simp [c, cAt, MvPolynomial.coeff_sum, MvPolynomial.coeff_X_pow, hsingle,
    show m < k + 1 by omega]

theorem coeff_c_zero (k : ℕ) : coeff 0 (c k) = 1 := by
  simpa using coeff_c_pure k 0 (Nat.zero_le k)

theorem c3_ne_c2_square : c 3 ≠ c 2 ^ 2 := by
  intro h
  have hc := congrArg (coeff (Finsupp.single 2 1)) h
  rw [coeff_c_pure 3 1 (by omega), coeff_odd_square_zero _ _ 2 (by simp)] at hc
  exact one_ne_zero hc

theorem c4_ne_c2_square : c 4 ≠ c 2 ^ 2 := by
  intro h
  have hc := congrArg (coeff (Finsupp.single 2 1)) h
  rw [coeff_c_pure 4 1 (by omega), coeff_odd_square_zero _ _ 2 (by simp)] at hc
  exact one_ne_zero hc

theorem c1_mul_c4_ne_c2_square : c 1 * c 4 ≠ c 2 ^ 2 := by
  intro h
  have hc := congrArg (coeff (Finsupp.single 2 5)) h
  have hprod : c 1 * c 4 = 1 + X 2 ^ 5 := c1_mul_c4_at (X 2)
  rw [hprod, MvPolynomial.coeff_add, MvPolynomial.coeff_one,
    MvPolynomial.coeff_X_pow, coeff_odd_square_zero _ _ 2 (by simp)] at hc
  have hs : (0 : ℕ →₀ ℕ) ≠ Finsupp.single 2 5 := by
    exact Ne.symm (Finsupp.single_ne_zero.mpr (by decide))
  simp [hs] at hc

theorem c1_mul_c4_ne_c3_square : c 1 * c 4 ≠ c 3 ^ 2 := by
  intro h
  have hc := congrArg (coeff (Finsupp.single 2 5)) h
  have hprod : c 1 * c 4 = 1 + X 2 ^ 5 := c1_mul_c4_at (X 2)
  rw [hprod, MvPolynomial.coeff_add, MvPolynomial.coeff_one,
    MvPolynomial.coeff_X_pow, coeff_odd_square_zero _ _ 2 (by simp)] at hc
  have hs : (0 : ℕ →₀ ℕ) ≠ Finsupp.single 2 5 := by
    exact Ne.symm (Finsupp.single_ne_zero.mpr (by decide))
  simp [hs] at hc

/-- The f25 quadratic obstruction also has this very short scalar witness:
set x2=0 and x5=1. It evaluates the first side to one and the square to zero. -/
theorem f25_quadratic_obstruction :
    c 1 * f16At (X 2) (X 5) ≠ (c 3 + X 5) ^ 2 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun i : ℕ => if i = 5 then 1 else 0)) h
  simp [c, cAt, f16At, Finset.sum_range_succ, map_add, map_mul, map_pow,
    CharTwo.add_self_eq_zero] at he

-- Constant-coefficient facts can be proved through the ring homomorphism,
-- avoiding convolution sums entirely.
theorem constantCoeff_c (k : ℕ) : constantCoeff (c k) = 1 := by
  induction k with
  | zero => simp [c, cAt]
  | succ k hk =>
      have hs : c (k + 1) = c k + X 2 ^ (k + 1) := by
        simp [c, cAt, Finset.sum_range_succ]
      rw [hs, map_add, hk, map_pow, constantCoeff_X]
      simp

theorem constantCoeff_f9 : constantCoeff f9 = 1 := by
  simp [f9, f9At, cAt, Finset.sum_range_succ]

theorem constantCoeff_f12 : constantCoeff f12 = 1 := by
  simp [f12, f12At, cAt, Finset.sum_range_succ]

theorem constantCoeff_f16 : constantCoeff f16 = 1 := by
  simp [f16, f16At, cAt, Finset.sum_range_succ]

theorem constantCoeff_f18 : constantCoeff f18 = 1 := by
  simp [f18, f18At, cAt, Finset.sum_range_succ]

theorem constantCoeff_f24 : constantCoeff f24 = 1 := by
  simp [f24, f24At, cAt, Finset.sum_range_succ]

theorem constantCoeff_f25 : constantCoeff f25 = 1 := by
  simp [f25, f25At, f24At, cAt, Finset.sum_range_succ]

/-- A compact finite table is convenient for exact coefficients and weights. -/
def coreExponent (a b z : ℕ) : ℕ →₀ ℕ :=
  Finsupp.single 2 a + Finsupp.single 3 b + Finsupp.single 5 z

theorem coreExponent_inj (a b z a' b' z' : ℕ) :
    coreExponent a b z = coreExponent a' b' z' ↔ a = a' ∧ b = b' ∧ z = z' := by
  constructor
  · intro h
    have h2 := congrArg (fun d : ℕ →₀ ℕ => d 2) h
    have h3 := congrArg (fun d : ℕ →₀ ℕ => d 3) h
    have h5 := congrArg (fun d : ℕ →₀ ℕ => d 5) h
    exact ⟨by simpa [coreExponent, Finsupp.add_apply] using h2,
      by simpa [coreExponent, Finsupp.add_apply] using h3,
      by simpa [coreExponent, Finsupp.add_apply] using h5⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

def coreTerm (t : ℕ × ℕ × ℕ) : Poly := monomial (coreExponent t.1 t.2.1 t.2.2) 1

theorem coreTerm_eq (a b z : ℕ) :
    coreTerm (a, b, z) = X 2 ^ a * X 3 ^ b * X 5 ^ z := by
  simp only [coreTerm, coreExponent, X_pow_eq_monomial, monomial_mul, mul_one]

def terms9 : Finset (ℕ × ℕ × ℕ) :=
  {(0,0,0), (1,0,0), (2,0,0), (3,0,0), (0,1,0), (1,1,0), (0,2,0)}

def terms12 : Finset (ℕ × ℕ × ℕ) := terms9 ∪ {(2,1,0)}

def terms16 : Finset (ℕ × ℕ × ℕ) := terms12 ∪ {(4,0,0)}

def terms18 : Finset (ℕ × ℕ × ℕ) :=
  {(0,0,0), (1,0,0), (2,0,0), (3,0,0), (4,0,0),
    (0,1,0), (1,1,0), (2,1,0), (0,2,0), (1,2,0)}

def terms24 : Finset (ℕ × ℕ × ℕ) := terms18 ∪ {(3,1,0)}

def terms25 : Finset (ℕ × ℕ × ℕ) := terms24 ∪
  {(0,0,1), (1,0,1), (2,0,1), (0,1,1), (0,0,2)}

theorem f9_terms : f9 = ∑ t ∈ terms9, coreTerm t := by
  simp [f9, f9At, cAt, Finset.sum_range_succ, terms9, coreTerm_eq]
  ring

theorem f12_terms : f12 = ∑ t ∈ terms12, coreTerm t := by
  simp [f12, f12At, cAt, Finset.sum_range_succ, terms12, terms9, coreTerm_eq]
  ring

theorem f16_terms : f16 = ∑ t ∈ terms16, coreTerm t := by
  simp [f16, f16At, cAt, Finset.sum_range_succ, terms16, terms12, terms9, coreTerm_eq]
  ring

theorem f18_terms : f18 = ∑ t ∈ terms18, coreTerm t := by
  simp [f18, f18At, cAt, Finset.sum_range_succ, terms18, coreTerm_eq]
  ring

theorem f24_terms : f24 = ∑ t ∈ terms24, coreTerm t := by
  simp [f24, f24At, cAt, Finset.sum_range_succ, terms24, terms18, coreTerm_eq]
  ring

theorem f25_terms : f25 = ∑ t ∈ terms25, coreTerm t := by
  simp [f25, f25At, f24At, cAt, Finset.sum_range_succ,
    terms25, terms24, terms18, coreTerm_eq]
  ring

-- These are exactly the coefficient witnesses needed for the elementary
-- endpoint bounds, including the mixed coefficient showing that the top
-- y-row has its own nonconstant x term.
theorem f9_selected_coefficients :
    coeff (coreExponent 0 0 0) f9 = 1 ∧
    coeff (coreExponent 1 0 0) f9 = 1 ∧
    coeff (coreExponent 0 1 0) f9 = 1 := by
  simp [f9_terms, terms9, coreTerm, MvPolynomial.coeff_monomial, coreExponent_inj]

theorem f12_selected_coefficients :
    coeff (coreExponent 0 0 0) f12 = 1 ∧
    coeff (coreExponent 1 0 0) f12 = 1 ∧
    coeff (coreExponent 0 1 0) f12 = 1 := by
  simp [f12_terms, terms12, terms9, coreTerm, MvPolynomial.coeff_monomial, coreExponent_inj]

theorem f16_selected_coefficients :
    coeff (coreExponent 0 0 0) f16 = 1 ∧
    coeff (coreExponent 1 0 0) f16 = 1 ∧
    coeff (coreExponent 0 1 0) f16 = 1 := by
  simp [f16_terms, terms16, terms12, terms9, coreTerm,
    MvPolynomial.coeff_monomial, coreExponent_inj]

theorem f18_selected_coefficients :
    coeff (coreExponent 0 0 0) f18 = 1 ∧
    coeff (coreExponent 1 0 0) f18 = 1 ∧
    coeff (coreExponent 0 1 0) f18 = 1 ∧
    coeff (coreExponent 0 2 0) f18 = 1 ∧
    coeff (coreExponent 1 2 0) f18 = 1 := by
  simp [f18_terms, terms18, coreTerm, MvPolynomial.coeff_monomial, coreExponent_inj]

theorem f24_selected_coefficients :
    coeff (coreExponent 0 0 0) f24 = 1 ∧
    coeff (coreExponent 1 0 0) f24 = 1 ∧
    coeff (coreExponent 0 1 0) f24 = 1 ∧
    coeff (coreExponent 0 2 0) f24 = 1 ∧
    coeff (coreExponent 1 2 0) f24 = 1 := by
  simp [f24_terms, terms24, terms18, coreTerm, MvPolynomial.coeff_monomial, coreExponent_inj]

theorem f25_selected_coefficients :
    coeff (coreExponent 0 0 0) f25 = 1 ∧
    coeff (coreExponent 1 0 0) f25 = 1 ∧
    coeff (coreExponent 0 1 0) f25 = 1 ∧
    coeff (coreExponent 0 2 0) f25 = 1 ∧
    coeff (coreExponent 1 2 0) f25 = 1 ∧
    coeff (coreExponent 0 0 1) f25 = 1 := by
  simp [f25_terms, terms25, terms24, terms18, coreTerm,
    MvPolynomial.coeff_monomial, coreExponent_inj]

theorem degreeOf_core_terms_le (T : Finset (ℕ × ℕ × ℕ))
    (hT : ∀ t ∈ T, t.2.1 ≤ 2) :
    (∑ t ∈ T, coreTerm t).degreeOf 3 ≤ 2 := by
  calc
    _ ≤ T.sup (fun t => (coreTerm t).degreeOf 3) := degreeOf_sum_le 3 T coreTerm
    _ ≤ 2 := Finset.sup_le (fun t ht => by
      rw [coreTerm, degreeOf_monomial_eq _ 3 (one_ne_zero : (1 : ZMod 2) ≠ 0)]
      simpa [coreExponent, Finsupp.add_apply] using hT t ht)

theorem degreeOf_f18_three : f18.degreeOf 3 ≤ 2 := by
  rw [f18_terms]
  exact degreeOf_core_terms_le terms18 (by simp [terms18])

theorem degreeOf_f24_three : f24.degreeOf 3 ≤ 2 := by
  rw [f24_terms]
  exact degreeOf_core_terms_le terms24 (by simp [terms24, terms18])

theorem degreeOf_f25_three : f25.degreeOf 3 ≤ 2 := by
  rw [f25_terms]
  exact degreeOf_core_terms_le terms25 (by simp [terms25, terms24, terms18])

theorem even_weight_f12 : Even (weight f12) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [← eval_one_eq_weight]
  simp [f12, f12At, cAt, Finset.sum_range_succ, CharTwo.add_self_eq_zero]

theorem even_weight_f18 : Even (weight f18) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [← eval_one_eq_weight]
  simp [f18, f18At, cAt, Finset.sum_range_succ, CharTwo.add_self_eq_zero]

theorem even_weight_f25 : Even (weight f25) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [← eval_one_eq_weight]
  simp [f25, f25At, f24At, cAt, Finset.sum_range_succ, CharTwo.add_self_eq_zero]

/-- The univariate core always supplies two endpoint terms. -/
theorem c_distance_lower (k : ℕ) (hk : 1 ≤ k) : 2 ≤ distance (c k) := by
  have h0 : coeff 0 (c k) ≠ 0 := by rw [coeff_c_zero]; exact one_ne_zero
  have hpure : ∀ p ∈ ({2} : Finset ℕ), ∃ j : ℕ, 0 < j ∧
      coeff (Finsupp.single p j) (c k) ≠ 0 := by
    intro p hp
    simp only [Finset.mem_singleton] at hp
    subst p
    exact ⟨1, by decide, by rw [coeff_c_pure k 1 hk]; exact one_ne_zero⟩
  simpa using pure_endpoints_distance ({2} : Finset ℕ) (c k) h0 hpure

theorem three_le_distance_of_selected (P : Poly)
    (h : coeff (coreExponent 0 0 0) P = 1 ∧
      coeff (coreExponent 1 0 0) P = 1 ∧ coeff (coreExponent 0 1 0) P = 1) :
    3 ≤ distance P := by
  have h0 : coeff 0 P = 1 := by simpa [coreExponent] using h.1
  have hx : coeff (Finsupp.single 2 1) P = 1 := by simpa [coreExponent] using h.2.1
  have hy : coeff (Finsupp.single 3 1) P = 1 := by simpa [coreExponent] using h.2.2
  have hpure : ∀ p ∈ ({2, 3} : Finset ℕ), ∃ k : ℕ, 0 < k ∧
      coeff (Finsupp.single p k) P ≠ 0 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact ⟨1, by decide, by rw [hx]; exact one_ne_zero⟩
    · exact ⟨1, by decide, by rw [hy]; exact one_ne_zero⟩
  have hc : coeff 0 P ≠ 0 := by rw [h0]; exact one_ne_zero
  simpa using pure_endpoints_distance ({2, 3} : Finset ℕ) P hc hpure

/-- These endpoint bounds deliberately make no use of the two-row obstruction. -/
theorem f9_distance_lower : 3 ≤ distance f9 :=
  three_le_distance_of_selected f9 f9_selected_coefficients

theorem f12_distance_lower : 4 ≤ distance f12 := by
  have hthree := three_le_distance_of_selected f12 f12_selected_coefficients
  obtain ⟨k, hk⟩ := even_distance_of_even_weight even_weight_f12
  omega

theorem f16_distance_lower : 3 ≤ distance f16 :=
  three_le_distance_of_selected f16 f16_selected_coefficients

theorem four_le_distance_of_selected (P : Poly) (hdegree : P.degreeOf 3 ≤ 2)
    (h : coeff (coreExponent 0 0 0) P = 1 ∧
      coeff (coreExponent 1 0 0) P = 1 ∧ coeff (coreExponent 0 1 0) P = 1 ∧
      coeff (coreExponent 0 2 0) P = 1 ∧ coeff (coreExponent 1 2 0) P = 1) :
    4 ≤ distance P := by
  have h0 : coeff 0 P = 1 := by simpa [coreExponent] using h.1
  have hx : coeff (Finsupp.single 2 1) P = 1 := by simpa [coreExponent] using h.2.1
  have h2 : coeff (Finsupp.single 3 2) P = 1 := by simpa [coreExponent] using h.2.2.2.1
  have hx2 : coeff (Finsupp.single 2 1 + Finsupp.single 3 2) P = 1 := by
    simpa [coreExponent] using h.2.2.2.2
  have hc : coeff 0 P ≠ 0 := by rw [h0]; exact one_ne_zero
  have hxc : coeff (Finsupp.single 2 1) P ≠ 0 := by rw [hx]; exact one_ne_zero
  have h2c : coeff (Finsupp.single 3 2) P ≠ 0 := by rw [h2]; exact one_ne_zero
  have hx2c : coeff (Finsupp.single 2 1 + Finsupp.single 3 2) P ≠ 0 := by
    rw [hx2]; exact one_ne_zero
  have hlo := coordinate_row_distance_two P 0 (by simpa using hc) (by simpa using hxc)
  have hhi := coordinate_row_distance_two P 2 h2c hx2c
  exact quadratic_endpoints_lower P 2 2 hdegree hc h2c hlo hhi

theorem f18_distance_lower : 4 ≤ distance f18 :=
  four_le_distance_of_selected f18 degreeOf_f18_three f18_selected_coefficients

theorem f24_distance_lower : 4 ≤ distance f24 :=
  four_le_distance_of_selected f24 degreeOf_f24_three f24_selected_coefficients

theorem f25_distance_lower : 6 ≤ distance f25 := by
  have h := f25_selected_coefficients
  have h0 : coeff 0 f25 = 1 := by simpa [coreExponent] using h.1
  have hx : coeff (Finsupp.single 2 1) f25 = 1 := by simpa [coreExponent] using h.2.1
  have h2 : coeff (Finsupp.single 3 2) f25 = 1 := by simpa [coreExponent] using h.2.2.2.1
  have hx2 : coeff (Finsupp.single 2 1 + Finsupp.single 3 2) f25 = 1 := by
    simpa [coreExponent] using h.2.2.2.2.1
  have hz : coeff (Finsupp.single 5 1) f25 = 1 := by
    simpa [coreExponent] using h.2.2.2.2.2
  have hc : coeff 0 f25 ≠ 0 := by rw [h0]; exact one_ne_zero
  have hxc : coeff (Finsupp.single 2 1) f25 ≠ 0 := by rw [hx]; exact one_ne_zero
  have h2c : coeff (Finsupp.single 3 2) f25 ≠ 0 := by rw [h2]; exact one_ne_zero
  have hx2c : coeff (Finsupp.single 2 1 + Finsupp.single 3 2) f25 ≠ 0 := by
    rw [hx2]; exact one_ne_zero
  have hzc : coeff (Finsupp.single 5 1) f25 ≠ 0 := by rw [hz]; exact one_ne_zero
  have hlo := coordinate_bottom_distance_three f25 hc hxc hzc
  have hhi := coordinate_row_distance_two f25 2 h2c hx2c
  have hfive := quadratic_endpoints_lower f25 3 2 degreeOf_f25_three hc h2c hlo hhi
  obtain ⟨k, hk⟩ := even_distance_of_even_weight even_weight_f25
  omega


end SmallCore
end Pilz
