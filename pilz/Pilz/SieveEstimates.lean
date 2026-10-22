import Pilz.Sieve
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Real-argument rough counts, discrepancy propagation, and one-step sieving. -/

noncomputable section

namespace Pilz

open scoped BigOperators

def roughRealCount (T : Finset ℕ) (x : ℝ) : ℝ := (roughCount T ⌊x⌋₊ : ℝ)

def roughRealIntervalCount (T : Finset ℕ) (x : ℝ) : ℝ :=
  roughRealCount T x - roughRealCount T (x / 2)

def RoughDiscrepancy (T : Finset ℕ) (ρ δ : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → |roughRealCount T x - ρ * x| ≤ δ

def RoughIntervalDiscrepancy (T : Finset ℕ) (ρ δ : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → |roughRealIntervalCount T x - ρ * x / 2| ≤ δ

@[simp] theorem roughRealCount_natCast (T : Finset ℕ) (n : ℕ) :
    roughRealCount T n = (roughCount T n : ℝ) := by simp [roughRealCount]

theorem roughRealIntervalCount_eq_floor (T : Finset ℕ) (x : ℝ) :
    roughRealIntervalCount T x = (roughIntervalCount T ⌊x⌋₊ : ℝ) := by
  unfold roughRealIntervalCount roughRealCount roughIntervalCount
  have hfloor : ⌊x / 2⌋₊ = ⌊x⌋₊ / 2 := Nat.floor_div_natCast x 2
  rw [hfloor]
  rw [Nat.cast_sub (roughCount_mono T (Nat.div_le_self ⌊x⌋₊ 2))]

@[simp] theorem roughRealIntervalCount_natCast (T : Finset ℕ) (n : ℕ) :
    roughRealIntervalCount T n = (roughIntervalCount T n : ℝ) := by
  rw [roughRealIntervalCount_eq_floor]
  simp

theorem roughRealCount_nonneg (T : Finset ℕ) (x : ℝ) : 0 ≤ roughRealCount T x :=
  Nat.cast_nonneg _

theorem roughRealIntervalCount_nonneg (T : Finset ℕ) (x : ℝ) :
    0 ≤ roughRealIntervalCount T x := by
  rw [roughRealIntervalCount_eq_floor]
  exact Nat.cast_nonneg _

/-- Exact real-argument Legendre recurrence, including nonintegral inputs. -/
theorem roughRealCount_insert_add (T : Finset ℕ) (p : ℕ) (x : ℝ)
    (hT : ∀ q ∈ T, Nat.Prime q) (hp : Nat.Prime p) (hpT : p ∉ T) :
    roughRealCount (insert p T) x + roughRealCount T (x / p) = roughRealCount T x := by
  have h := roughCount_insert_add T p ⌊x⌋₊ hT hp hpT
  have hc : (roughCount (insert p T) ⌊x⌋₊ : ℝ) + roughCount T (⌊x⌋₊ / p) =
      roughCount T ⌊x⌋₊ := by exact_mod_cast h
  simpa only [roughRealCount, Nat.floor_div_natCast] using hc

theorem roughRealCount_insert (T : Finset ℕ) (p : ℕ) (x : ℝ)
    (hT : ∀ q ∈ T, Nat.Prime q) (hp : Nat.Prime p) (hpT : p ∉ T) :
    roughRealCount (insert p T) x = roughRealCount T x - roughRealCount T (x / p) := by
  have h := roughRealCount_insert_add T p x hT hp hpT
  linarith

/-- Adding one new sieve prime multiplies the density by `(1-1/p)` and
at most doubles its uniform discrepancy. -/
theorem roughDiscrepancy_insert (T : Finset ℕ) (p : ℕ) (ρ δ : ℝ)
    (hT : ∀ q ∈ T, Nat.Prime q) (hp : Nat.Prime p) (hpT : p ∉ T)
    (herr : RoughDiscrepancy T ρ δ) :
    RoughDiscrepancy (insert p T) (ρ * (1 - 1 / (p : ℝ))) (2 * δ) := by
  intro x hx
  have hxp : 0 ≤ x / (p : ℝ) := div_nonneg hx (Nat.cast_nonneg p)
  have h₁ := herr x hx
  have h₂ := herr (x / p) hxp
  rw [roughRealCount_insert T p x hT hp hpT]
  have hid : roughRealCount T x - roughRealCount T (x / p) -
      ρ * (1 - 1 / (p : ℝ)) * x =
      (roughRealCount T x - ρ * x) - (roughRealCount T (x / p) - ρ * (x / p)) := by ring
  rw [hid]
  calc
    |(roughRealCount T x - ρ * x) - (roughRealCount T (x / p) - ρ * (x / p))| ≤
        |roughRealCount T x - ρ * x| + |roughRealCount T (x / p) - ρ * (x / p)| :=
      abs_sub _ _
    _ ≤ δ + δ := add_le_add h₁ h₂
    _ = 2 * δ := by ring

/-- Iterating the exact one-prime recurrence gives the uniform exponential
discrepancy bound for any finite collection of new sieve primes. -/
theorem roughDiscrepancy_union (T U : Finset ℕ) (ρ δ : ℝ)
    (hT : ∀ p ∈ T, Nat.Prime p) (hU : ∀ p ∈ U, Nat.Prime p) (hdis : Disjoint T U)
    (herr : RoughDiscrepancy T ρ δ) :
    RoughDiscrepancy (T ∪ U) (ρ * ∏ p ∈ U, (1 - 1 / (p : ℝ)))
      (2 ^ U.card * δ) := by
  classical
  induction U using Finset.induction_on with
  | empty => simpa using herr
  | @insert p U hpU ih =>
      have hU' : ∀ q ∈ U, Nat.Prime q := fun q hq => hU q (Finset.mem_insert_of_mem hq)
      have hdis' : Disjoint T U := Finset.disjoint_left.mpr
        (fun q hqT hqU => Finset.disjoint_left.mp hdis hqT (Finset.mem_insert_of_mem hqU))
      have hprev := ih hU' hdis'
      have hpT : p ∉ T := fun hpt =>
        Finset.disjoint_left.mp hdis hpt (Finset.mem_insert_self p U)
      have hpTU : p ∉ T ∪ U := by
        intro hp
        rcases Finset.mem_union.mp hp with hpt | hpu
        · exact hpT hpt
        · exact hpU hpu
      have hTU : ∀ q ∈ T ∪ U, Nat.Prime q := by
        intro q hq
        rcases Finset.mem_union.mp hq with hqt | hqu
        · exact hT q hqt
        · exact hU' q hqu
      have hnext := roughDiscrepancy_insert (T ∪ U) p
        (ρ * ∏ q ∈ U, (1 - 1 / (q : ℝ))) (2 ^ U.card * δ)
        hTU (hU p (Finset.mem_insert_self p U)) hpTU hprev
      have hset : T ∪ insert p U = insert p (T ∪ U) := by ext q; simp [or_left_comm]
      rw [hset]
      convert hnext using 1 <;>
        simp [Finset.prod_insert, hpU, Finset.card_insert_of_notMem hpU, pow_succ] <;> ring

theorem roughIntervalDiscrepancy_of_discrepancy (T : Finset ℕ) (ρ δ : ℝ)
    (herr : RoughDiscrepancy T ρ δ) : RoughIntervalDiscrepancy T ρ (2 * δ) := by
  intro x hx
  have h₁ := herr x hx
  have h₂ := herr (x / 2) (by linarith)
  have hid : roughRealIntervalCount T x - ρ * x / 2 =
      (roughRealCount T x - ρ * x) - (roughRealCount T (x / 2) - ρ * (x / 2)) := by
    unfold roughRealIntervalCount
    ring
  rw [hid]
  calc
    |(roughRealCount T x - ρ * x) - (roughRealCount T (x / 2) - ρ * (x / 2))| ≤
        |roughRealCount T x - ρ * x| + |roughRealCount T (x / 2) - ρ * (x / 2)| :=
      abs_sub _ _
    _ ≤ δ + δ := add_le_add h₁ h₂
    _ = 2 * δ := by ring

theorem roughRealIntervalCount_lower (T : Finset ℕ) (ρ δ x : ℝ)
    (herr : RoughDiscrepancy T ρ δ) (hx : 0 ≤ x) :
    ρ * x / 2 - 2 * δ ≤ roughRealIntervalCount T x := by
  have h := (abs_le.mp (roughIntervalDiscrepancy_of_discrepancy T ρ δ herr x hx)).1
  linarith

/-- A union bound in an arbitrary finite collection of candidate integers. -/
private theorem sieve_union_card (B U : Finset ℕ) :
    B.card ≤ (B.filter (fun b => ∀ p ∈ U, ¬p ∣ b)).card +
      ∑ p ∈ U, (B.filter (fun b => p ∣ b)).card := by
  classical
  let bad := U.biUnion (fun p => B.filter (fun b => p ∣ b))
  have hgood : B.filter (fun b => ∀ p ∈ U, ¬p ∣ b) = B \ bad := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_sdiff, bad, Finset.mem_biUnion]
    constructor
    · rintro ⟨hb, havoid⟩
      refine ⟨hb, ?_⟩
      rintro ⟨p, hp, _hb, hdiv⟩
      exact havoid p hp hdiv
    · rintro ⟨hb, hbad⟩
      refine ⟨hb, ?_⟩
      intro p hp hdiv
      exact hbad ⟨p, hp, hb, hdiv⟩
  have h₁ := Finset.card_le_card_sdiff_add_card (s := B) (t := bad)
  have h₂ : bad.card ≤ ∑ p ∈ U, (B.filter (fun b => p ∣ b)).card := Finset.card_biUnion_le
  rw [hgood]
  omega

theorem roughCount_union_bound (T U : Finset ℕ) (n : ℕ)
    (hT : ∀ p ∈ T, Nat.Prime p) (hU : ∀ p ∈ U, Nat.Prime p) (hdis : Disjoint T U) :
    roughCount T n ≤ roughCount (T ∪ U) n + ∑ p ∈ U, roughCount T (n / p) := by
  classical
  have hgood : (roughNumbers T n).filter (fun b => ∀ p ∈ U, ¬p ∣ b) =
      roughNumbers (T ∪ U) n := by
    ext b
    simp only [Finset.mem_filter, mem_roughNumbers, Finset.forall_mem_union]
    tauto
  have hcard := sieve_union_card (roughNumbers T n) U
  rw [hgood] at hcard
  calc
    roughCount T n ≤ roughCount (T ∪ U) n +
        ∑ p ∈ U, ((roughNumbers T n).filter (fun b => p ∣ b)).card := hcard
    _ = roughCount (T ∪ U) n + ∑ p ∈ U, roughCount T (n / p) := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [rough_multiples_eq_image T p n hT (hU p hp)
        (fun hpT => Finset.disjoint_left.mp hdis hpT hp)]
      exact Finset.card_image_of_injective _ (fun a b h =>
        Nat.eq_of_mul_eq_mul_left (hU p hp).pos h)

theorem roughRealCount_union_bound (T U : Finset ℕ) (x : ℝ)
    (hT : ∀ p ∈ T, Nat.Prime p) (hU : ∀ p ∈ U, Nat.Prime p) (hdis : Disjoint T U) :
    roughRealCount T x - ∑ p ∈ U, roughRealCount T (x / p) ≤ roughRealCount (T ∪ U) x := by
  have hnat := roughCount_union_bound T U ⌊x⌋₊ hT hU hdis
  have hc : (roughCount T ⌊x⌋₊ : ℝ) ≤ roughCount (T ∪ U) ⌊x⌋₊ +
      ∑ p ∈ U, (roughCount T (⌊x⌋₊ / p) : ℝ) := by
    have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
    simpa only [Nat.cast_add, Nat.cast_sum] using hcast
  have h : roughRealCount T x ≤ roughRealCount (T ∪ U) x +
      ∑ p ∈ U, roughRealCount T (x / p) := by
    simpa only [roughRealCount, Nat.floor_div_natCast] using hc
  linarith

def roughHalfNumbers (T : Finset ℕ) (n : ℕ) : Finset ℕ :=
  roughNumbers T n \ roughNumbers T (n / 2)

theorem mem_roughHalfNumbers (T : Finset ℕ) (n b : ℕ) :
    b ∈ roughHalfNumbers T n ↔ 1 ≤ b ∧ b ≤ n ∧ n / 2 < b ∧ ∀ p ∈ T, ¬p ∣ b := by
  simp only [roughHalfNumbers, Finset.mem_sdiff, mem_roughNumbers]
  constructor
  · rintro ⟨⟨hbpos, hbn, hrough⟩, hnot⟩
    refine ⟨hbpos, hbn, ?_, hrough⟩
    by_contra hhalf
    exact hnot ⟨hbpos, by omega, hrough⟩
  · rintro ⟨hbpos, hbn, hhalf, hrough⟩
    refine ⟨⟨hbpos, hbn, hrough⟩, ?_⟩
    rintro ⟨_, hble, _⟩
    omega

theorem card_roughHalfNumbers (T : Finset ℕ) (n : ℕ) :
    (roughHalfNumbers T n).card = roughIntervalCount T n := by
  rw [roughHalfNumbers,
    Finset.card_sdiff_of_subset (roughNumbers_mono T (Nat.div_le_self n 2))]
  rfl

theorem roughHalf_multiples_eq_image (T : Finset ℕ) (p n : ℕ)
    (hT : ∀ q ∈ T, Nat.Prime q) (hp : Nat.Prime p) (hpT : p ∉ T) :
    (roughHalfNumbers T n).filter (fun b => p ∣ b) =
      (roughHalfNumbers T (n / p)).image (fun b => p * b) := by
  classical
  have hfilter : (roughHalfNumbers T n).filter (fun b => p ∣ b) =
      ((roughNumbers T n).filter (fun b => p ∣ b)) \
        ((roughNumbers T (n / 2)).filter (fun b => p ∣ b)) := by
    ext b
    simp only [roughHalfNumbers, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [hfilter, rough_multiples_eq_image T p n hT hp hpT,
    rough_multiples_eq_image T p (n / 2) hT hp hpT]
  have hdiv : n / 2 / p = n / p / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm 2 p]
  rw [hdiv, ← Finset.image_sdiff _ _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
  rfl

theorem roughIntervalCount_union_bound (T U : Finset ℕ) (n : ℕ)
    (hT : ∀ p ∈ T, Nat.Prime p) (hU : ∀ p ∈ U, Nat.Prime p) (hdis : Disjoint T U) :
    roughIntervalCount T n ≤ roughIntervalCount (T ∪ U) n +
      ∑ p ∈ U, roughIntervalCount T (n / p) := by
  classical
  have hgood : (roughHalfNumbers T n).filter (fun b => ∀ p ∈ U, ¬p ∣ b) =
      roughHalfNumbers (T ∪ U) n := by
    ext b
    simp only [Finset.mem_filter, mem_roughHalfNumbers, Finset.forall_mem_union]
    tauto
  have hcard := sieve_union_card (roughHalfNumbers T n) U
  rw [hgood, card_roughHalfNumbers, card_roughHalfNumbers] at hcard
  calc
    roughIntervalCount T n ≤ roughIntervalCount (T ∪ U) n +
        ∑ p ∈ U, ((roughHalfNumbers T n).filter (fun b => p ∣ b)).card := hcard
    _ = roughIntervalCount (T ∪ U) n + ∑ p ∈ U, roughIntervalCount T (n / p) := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [roughHalf_multiples_eq_image T p n hT (hU p hp)
        (fun hpT => Finset.disjoint_left.mp hdis hpT hp),
        Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left (hU p hp).pos h),
        card_roughHalfNumbers]

theorem roughRealIntervalCount_union_bound (T U : Finset ℕ) (x : ℝ)
    (hT : ∀ p ∈ T, Nat.Prime p) (hU : ∀ p ∈ U, Nat.Prime p) (hdis : Disjoint T U) :
    roughRealIntervalCount T x - ∑ p ∈ U, roughRealIntervalCount T (x / p) ≤
      roughRealIntervalCount (T ∪ U) x := by
  have hnat := roughIntervalCount_union_bound T U ⌊x⌋₊ hT hU hdis
  have hc : (roughIntervalCount T ⌊x⌋₊ : ℝ) ≤ roughIntervalCount (T ∪ U) ⌊x⌋₊ +
      ∑ p ∈ U, (roughIntervalCount T (⌊x⌋₊ / p) : ℝ) := by
    have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
    simpa only [Nat.cast_add, Nat.cast_sum] using hcast
  have h : roughRealIntervalCount T x ≤ roughRealIntervalCount (T ∪ U) x +
      ∑ p ∈ U, roughRealIntervalCount T (x / p) := by
    simpa only [roughRealIntervalCount_eq_floor, Nat.floor_div_natCast] using hc
  linarith

private theorem sum_linear_sieve_errors (U : Finset ℕ) (ρ δ x : ℝ) :
    (∑ p ∈ U, (ρ * (x / p) + δ)) =
      ρ * x * (∑ p ∈ U, 1 / (p : ℝ)) + (U.card : ℝ) * δ := by
  calc
    (∑ p ∈ U, (ρ * (x / p) + δ)) =
        (∑ p ∈ U, ρ * x * (1 / (p : ℝ))) + ∑ _p ∈ U, δ := by
      rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = ρ * x * (∑ p ∈ U, 1 / (p : ℝ)) + (U.card : ℝ) * δ := by
      rw [← Finset.mul_sum]
      simp

/-- The ordinary count bound in the paper's one-step sieve. -/
theorem roughRealCount_one_step (T U : Finset ℕ) (ρ δ x : ℝ)
    (hT : ∀ p ∈ T, Nat.Prime p) (hU : ∀ p ∈ U, Nat.Prime p) (hdis : Disjoint T U)
    (herr : RoughDiscrepancy T ρ δ) (hx : 0 ≤ x) :
    ρ * (1 - ∑ p ∈ U, 1 / (p : ℝ)) * x - (1 + (U.card : ℝ)) * δ ≤
      roughRealCount (T ∪ U) x := by
  have hbase := (abs_le.mp (herr x hx)).1
  have hupper : (∑ p ∈ U, roughRealCount T (x / p)) ≤
      ∑ p ∈ U, (ρ * (x / p) + δ) := by
    apply Finset.sum_le_sum
    intro p hp
    have h := (abs_le.mp (herr (x / p) (div_nonneg hx (Nat.cast_nonneg p)))).2
    linarith
  rw [sum_linear_sieve_errors U ρ δ x] at hupper
  have hbound := roughRealCount_union_bound T U x hT hU hdis
  nlinarith

/-- A supplied half-interval discrepancy gives the sharper one-step error
`(1+|U|)*δ`, as used for the `22/15` bound in the manuscript. -/
theorem roughRealIntervalCount_one_step_refined (T U : Finset ℕ) (ρ δ x : ℝ)
    (hT : ∀ p ∈ T, Nat.Prime p) (hU : ∀ p ∈ U, Nat.Prime p) (hdis : Disjoint T U)
    (herr : RoughIntervalDiscrepancy T ρ δ) (hx : 0 ≤ x) :
    ρ * (1 - ∑ p ∈ U, 1 / (p : ℝ)) * x / 2 - (1 + (U.card : ℝ)) * δ ≤
      roughRealIntervalCount (T ∪ U) x := by
  have hbase := (abs_le.mp (herr x hx)).1
  have hupper : (∑ p ∈ U, roughRealIntervalCount T (x / p)) ≤
      ∑ p ∈ U, ((ρ / 2) * (x / p) + δ) := by
    apply Finset.sum_le_sum
    intro p hp
    have h := (abs_le.mp (herr (x / p) (div_nonneg hx (Nat.cast_nonneg p)))).2
    linarith
  rw [sum_linear_sieve_errors U (ρ / 2) δ x] at hupper
  have hbound := roughRealIntervalCount_union_bound T U x hT hU hdis
  nlinarith

theorem roughRealIntervalCount_one_step (T U : Finset ℕ) (ρ δ x : ℝ)
    (hT : ∀ p ∈ T, Nat.Prime p) (hU : ∀ p ∈ U, Nat.Prime p) (hdis : Disjoint T U)
    (herr : RoughDiscrepancy T ρ δ) (hx : 0 ≤ x) :
    ρ * (1 - ∑ p ∈ U, 1 / (p : ℝ)) * x / 2 - 2 * (1 + (U.card : ℝ)) * δ ≤
      roughRealIntervalCount (T ∪ U) x := by
  have h := roughRealIntervalCount_one_step_refined T U ρ (2 * δ) x hT hU hdis
    (roughIntervalDiscrepancy_of_discrepancy T ρ δ herr) hx
  nlinarith

end Pilz
