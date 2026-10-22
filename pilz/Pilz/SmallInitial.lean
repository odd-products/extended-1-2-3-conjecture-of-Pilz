import Pilz.SmallCases
import Pilz.CoreBudget
import Pilz.Protection
import Pilz.IntervalElimination
import Pilz.LinearCoreBounds
import Pilz.F9Parametrization

/-!
# The initial interval cases used in the paper

These are the normal-form/core-budget arguments for lengths five through ten.
No few-multiplier or few-prime theorem is used to prove these initial inputs.
-/

noncomputable section

namespace Pilz

open MvPolynomial

private theorem initial_weight_mul_of_weight_one (n : ℕ) (H : Poly)
    (hH : weight H = 1) : weight (interval n * H) = n := by
  classical
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hH
  have hc : coeff d H = 1 := by
    have hc0 : coeff d H ≠ 0 := mem_support_iff.mp (by rw [hd]; simp)
    have hunit {z : ZMod 2} (hz : z ≠ 0) : z = 1 := by
      fin_cases z <;> simp_all
    exact hunit hc0
  have hmono : H = monomial d 1 := by
    rw [MvPolynomial.as_sum H, hd]
    simp [hc]
  rw [hmono, weight_mul_monomial, weight_interval]

/-- A numerical criterion that isolates the common argument in the six rows
of the paper's initial-case table. -/
theorem conjectureAt_of_small_core (n κ r M T : ℕ) (S : FreshData)
    (hF : S.F = interval n) (hr : S.vars.card = r)
    (hκ : κ ≤ distance S.C) (hκpos : 2 ≤ κ)
    (hM : sigma S.C ≤ M) (hNM : 2 * M ≤ n)
    (hbound : ∀ m : ℕ, m < n → (Even n → Even m) → m ≤ T)
    (hreduce : ∀ m u : ℕ, 0 < u → r * u < m → 2 * u ≤ m → m ≤ T →
      u < κ ∧ (r * u + κ ≤ m → u = 1)) : ConjectureAt n := by
  intro H hH
  by_contra hnot
  have hshort : weight (interval n * H) < n := by omega
  have hex : ∃ G : Poly, ShortMultiple S.F n G := by
    refine ⟨S.F * H, mul_ne_zero S.prime_F.ne_zero hH, dvd_mul_right _ _, ?_⟩
    simpa only [hF] using hshort
  have hC : 2 ≤ weight S.C := by
    exact hκpos.trans (hκ.trans (distance_le_termWeight S.C))
  obtain ⟨nf⟩ := exists_normalForm S n hC hex
  have hm : weight nf.G < n := nf.extremal.1.2.2
  have hpar : Even n → Even (weight nf.G) := by
    intro hn
    obtain ⟨V, hV⟩ := nf.extremal.1.2.1
    have hp : Even (weight (S.F * V)) :=
      even_weight_mul (P := S.F) (by simpa [hF] using hn) V
    rwa [← hV] at hp
  have hmT := hbound (weight nf.G) hm hpar
  have hu : 0 < weight nf.D := weight_pos nf.D_ne_zero
  have hG₀ : 0 < weight nf.G₀ := weight_pos nf.G₀_ne_zero
  have hw := normalForm_weight S n nf
  rw [hr] at hw
  have hru : r * weight nf.D < weight nf.G := by omega
  obtain ⟨husmall, hunit⟩ := hreduce (weight nf.G) (weight nf.D) hu hru nf.half hmT
  have hcore := normalForm_core_budget S n nf (husmall.trans_le hκ)
  rw [hr] at hcore
  have huone : weight nf.D = 1 := hunit (by omega)
  have hN : n ≤ weight S.C + S.vars.card := by
    rw [← S.weight_F, hF, weight_interval]
  have hcap : ∀ ε : ℕ → ℕ, classWeight (S.C * nf.D) ε ≤ M := by
    intro ε
    have h := classWeight_mul_le_sigma S.C nf.D ε
    rw [huone, mul_one] at h
    exact h.trans hM
  have hprod : n ≤ weight (S.F * nf.D) := by
    rw [hF, initial_weight_mul_of_weight_one n nf.D huone]
  exact normalForm_excluded_of_twice_capacity S n nf hN M hcap hNM hprod

private theorem initial_m2 : monomialOf 2 = (X 2 : Poly) :=
  monomialOf_prime (by decide)
private theorem initial_m3 : monomialOf 3 = (X 3 : Poly) :=
  monomialOf_prime (by decide)
private theorem initial_m5 : monomialOf 5 = (X 5 : Poly) :=
  monomialOf_prime (by decide)
private theorem initial_m6 : monomialOf 6 = (X 2 : Poly) * X 3 := by
  calc
    monomialOf 6 = monomialOf 2 * monomialOf 3 := monomialOf_mul (a := 2) (b := 3) (by decide) (by decide)
    _ = (X 2 : Poly) * X 3 := by rw [initial_m2, initial_m3]
private theorem initial_m8 : monomialOf 8 = (X 2 : Poly) ^ 3 := by
  calc
    monomialOf 8 = monomialOf 2 * monomialOf 4 := monomialOf_mul (a := 2) (b := 4) (by decide) (by decide)
    _ = (X 2 : Poly) ^ 3 := by rw [initial_m2, monomialOf_four]; ring
private theorem initial_m9 : monomialOf 9 = (X 3 : Poly) ^ 2 := by
  calc
    monomialOf 9 = monomialOf 3 * monomialOf 3 := monomialOf_mul (a := 3) (b := 3) (by decide) (by decide)
    _ = (X 3 : Poly) ^ 2 := by rw [initial_m3, pow_two]
private theorem initial_m10 : monomialOf 10 = (X 2 : Poly) * X 5 := by
  calc
    monomialOf 10 = monomialOf 2 * monomialOf 5 := monomialOf_mul (a := 2) (b := 5) (by decide) (by decide)
    _ = (X 2 : Poly) * X 5 := by rw [initial_m2, initial_m5]

theorem core_five : core 5 = SmallCore.c 2 := by
  have hs : Finset.Icc 1 5 \ freshPrimes 5 = ({1, 2, 4} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, monomialOf_one, initial_m2, monomialOf_four,
    SmallCore.c, SmallCore.cAt, Finset.sum_range_succ]
  ring

theorem core_six : core 6 = SmallCore.c 2 + SmallCore.c 1 * X 3 := by
  have hs : Finset.Icc 1 6 \ freshPrimes 6 = ({1, 2, 3, 4, 6} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, monomialOf_one, initial_m2, initial_m3, monomialOf_four, initial_m6,
    SmallCore.c, SmallCore.cAt, Finset.sum_range_succ]
  ring

theorem core_seven : core 7 = core 6 := by
  have hs : Finset.Icc 1 7 \ freshPrimes 7 = Finset.Icc 1 6 \ freshPrimes 6 := by decide
  rw [core, hs, core]

theorem core_eight : core 8 = SmallCore.c 3 + SmallCore.c 1 * X 3 := by
  have hs : Finset.Icc 1 8 \ freshPrimes 8 = ({1, 2, 3, 4, 6, 8} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, monomialOf_one, initial_m2, initial_m3, monomialOf_four,
    initial_m6, initial_m8, SmallCore.c, SmallCore.cAt, Finset.sum_range_succ]
  ring

theorem core_nine : core 9 = SmallCore.f9 := by
  have hs : Finset.Icc 1 9 \ freshPrimes 9 = ({1, 2, 3, 4, 6, 8, 9} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, monomialOf_one, initial_m2, initial_m3, monomialOf_four,
    initial_m6, initial_m8, initial_m9, SmallCore.f9, SmallCore.f9At,
    SmallCore.cAt, Finset.sum_range_succ]
  ring

theorem core_ten : core 10 = SmallCore.f9 + SmallCore.c 1 * X 5 := by
  have hs : Finset.Icc 1 10 \ freshPrimes 10 = ({1, 2, 3, 4, 5, 6, 8, 9, 10} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, monomialOf_one, initial_m2, initial_m3, initial_m5, monomialOf_four,
    initial_m6, initial_m8, initial_m9, initial_m10, SmallCore.f9, SmallCore.f9At,
    SmallCore.c, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem initial_case (n κ r T : ℕ) (hn : 0 < n)
    (hfresh : (freshPrimes n).Nonempty) (hr : (freshPrimes n).card = r)
    (hκ : κ ≤ distance (core n)) (hκpos : 2 ≤ κ)
    (hNM : 2 * Nat.sqrt n ≤ n)
    (hbound : ∀ m : ℕ, m < n → (Even n → Even m) → m ≤ T)
    (hreduce : ∀ m u : ℕ, 0 < u → r * u < m → 2 * u ≤ m → m ≤ T →
      u < κ ∧ (r * u + κ ≤ m → u = 1)) : ConjectureAt n := by
  exact conjectureAt_of_small_core n κ r (Nat.sqrt n) T (intervalFreshData n hn hfresh)
    (intervalFreshData_F n hn hfresh) hr hκ hκpos (sigma_core_le_sqrt n) hNM hbound hreduce

private theorem initial_sqrt_bound (n : ℕ) (h : n < (n / 2 + 1) * (n / 2 + 1)) :
    2 * Nat.sqrt n ≤ n := by
  have hs : Nat.sqrt n < n / 2 + 1 := Nat.sqrt_lt.mpr h
  omega

/-- The first application of the paper's normal-form/core budget. -/
theorem conjectureAt_five : ConjectureAt 5 := by
  apply initial_case 5 2 2 4 (by decide) (by decide) (by decide)
    (by rw [core_five]; exact SmallCore.c_distance_lower 2 (by decide)) (by decide)
    (initial_sqrt_bound 5 (by decide))
  · intro m hm _hp
    omega
  · intro m u hu hru hhalf hm
    constructor
    · omega
    · intro hbudget
      omega

private theorem initial_c_ne_zero (k : ℕ) : SmallCore.c k ≠ 0 := by
  intro hz
  have h := congrArg constantCoeff hz
  simp [SmallCore.constantCoeff_c] at h

private theorem initial_c_degree (p k : ℕ) (hp : p ≠ 2) :
    (SmallCore.c k).degreeOf p = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold SmallCore.c SmallCore.cAt
  refine (degreeOf_sum_le p _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro i _hi
  exact (degreeOf_pow_le p (X 2 : Poly) i).trans_eq (by simp [degreeOf_X, hp])

private theorem initial_f9_degree : SmallCore.f9.degreeOf 5 = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [SmallCore.f9_terms]
  refine (degreeOf_sum_le 5 SmallCore.terms9 SmallCore.coreTerm).trans ?_
  apply Finset.sup_le
  intro t ht
  have hzeros : ∀ t ∈ SmallCore.terms9, t.2.2 = 0 := by simp [SmallCore.terms9]
  have htz : t.2.2 = 0 := hzeros t ht
  rw [SmallCore.coreTerm,
    degreeOf_monomial_eq _ 5 (one_ne_zero : (1 : ZMod 2) ≠ 0)]
  simp [SmallCore.coreExponent, htz]

theorem core_six_distance_four : 4 ≤ distance (core 6) := by
  rw [core_six]
  have h := linear_core_distance 3 (SmallCore.c 2) (SmallCore.c 1)
    (initial_c_ne_zero 2) (initial_c_ne_zero 1)
    (initial_c_degree 3 2 (by decide)) (initial_c_degree 3 1 (by decide))
  have hlo := SmallCore.c_distance_lower 2 (by decide)
  have hhi := SmallCore.c_distance_lower 1 (by decide)
  omega

theorem core_eight_distance_four : 4 ≤ distance (core 8) := by
  rw [core_eight]
  have h := linear_core_distance 3 (SmallCore.c 3) (SmallCore.c 1)
    (initial_c_ne_zero 3) (initial_c_ne_zero 1)
    (initial_c_degree 3 3 (by decide)) (initial_c_degree 3 1 (by decide))
  have hlo := SmallCore.c_distance_lower 3 (by decide)
  have hhi := SmallCore.c_distance_lower 1 (by decide)
  omega

theorem core_ten_distance_seven (hf9 : 5 ≤ distance SmallCore.f9) :
    7 ≤ distance (core 10) := by
  rw [core_ten]
  have h9 : SmallCore.f9 ≠ 0 := by
    intro hz
    rw [hz, distance_zero] at hf9
    omega
  have h := linear_core_distance 5 SmallCore.f9 (SmallCore.c 1)
    h9 (initial_c_ne_zero 1) initial_f9_degree (initial_c_degree 5 1 (by decide))
  have hhi := SmallCore.c_distance_lower 1 (by decide)
  omega

theorem conjectureAt_six : ConjectureAt 6 := by
  apply initial_case 6 4 1 4 (by decide) (by decide) (by decide)
    core_six_distance_four (by decide) (initial_sqrt_bound 6 (by decide))
  · intro m hm hp
    obtain ⟨k, hk⟩ := hp (by decide)
    omega
  · intro m u hu hru hhalf hm
    constructor
    · omega
    · intro hbudget
      omega

theorem conjectureAt_seven : ConjectureAt 7 := by
  apply initial_case 7 4 2 6 (by decide) (by decide) (by decide)
    (by rw [core_seven]; exact core_six_distance_four) (by decide)
    (initial_sqrt_bound 7 (by decide))
  · intro m hm _hp
    omega
  · intro m u hu hru hhalf hm
    constructor
    · omega
    · intro hbudget
      omega

theorem conjectureAt_eight : ConjectureAt 8 := by
  apply initial_case 8 4 2 6 (by decide) (by decide) (by decide)
    core_eight_distance_four (by decide) (initial_sqrt_bound 8 (by decide))
  · intro m hm hp
    obtain ⟨k, hk⟩ := hp (by decide)
    omega
  · intro m u hu hru hhalf hm
    constructor
    · omega
    · intro hbudget
      omega

theorem conjectureAt_nine_of_f9 (hf9 : 5 ≤ distance SmallCore.f9) : ConjectureAt 9 := by
  apply initial_case 9 5 2 8 (by decide) (by decide) (by decide)
    (by rwa [core_nine]) (by decide) (initial_sqrt_bound 9 (by decide))
  · intro m hm _hp
    omega
  · intro m u hu hru hhalf hm
    constructor
    · omega
    · intro hbudget
      omega

theorem conjectureAt_ten_of_f9 (hf9 : 5 ≤ distance SmallCore.f9) : ConjectureAt 10 := by
  apply initial_case 10 7 1 8 (by decide) (by decide) (by decide)
    (core_ten_distance_seven hf9) (by decide) (initial_sqrt_bound 10 (by decide))
  · intro m hm hp
    obtain ⟨k, hk⟩ := hp (by decide)
    omega
  · intro m u hu hru hhalf hm
    constructor
    · omega
    · intro hbudget
      omega

theorem conjectureAt_le_ten_of_f9 (hf9 : 5 ≤ distance SmallCore.f9)
    (n : ℕ) (hn : n ≤ 10) : ConjectureAt n := by
  by_cases hsmall : n ≤ 4
  · exact conjectureAt_le_four n hsmall
  · interval_cases n
    · exact conjectureAt_five
    · exact conjectureAt_six
    · exact conjectureAt_seven
    · exact conjectureAt_eight
    · exact conjectureAt_nine_of_f9 hf9
    · exact conjectureAt_ten_of_f9 hf9

theorem conjectureAt_nine : ConjectureAt 9 :=
  conjectureAt_nine_of_f9 F9Param.f9_distance_lower_five

theorem conjectureAt_ten : ConjectureAt 10 :=
  conjectureAt_ten_of_f9 F9Param.f9_distance_lower_five

/-- All initial cases required as inputs by the rest of the paper. -/
theorem conjectureAt_le_ten (n : ℕ) (hn : n ≤ 10) : ConjectureAt n :=
  conjectureAt_le_ten_of_f9 F9Param.f9_distance_lower_five n hn

theorem distance_interval_le_ten (n : ℕ) (hn : n ≤ 10) : distance (interval n) = n :=
  distance_interval_eq_of_conjecture (conjectureAt_le_ten n hn)

theorem oddProduct_interval_lower_bound_le_ten (n : ℕ) (hn : n ≤ 10)
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    n ≤ (oddProduct A (Finset.Icc 1 n)).card :=
  oddProduct_interval_lower_bound (conjectureAt_le_ten n hn) A hA hne

end Pilz
