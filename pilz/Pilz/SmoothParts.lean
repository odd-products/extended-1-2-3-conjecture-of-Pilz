import Pilz.Basic
import Pilz.Sieve

/-!
# The unique smooth and rough factors of a positive integer

The prime-exponent vector is split by restriction to `T` and to its
complement. Products of the corresponding prime powers give the exact
arithmetic factors used by the rough-component decomposition.
-/

noncomputable section

namespace Pilz

open scoped BigOperators

def insideExponent (T : Finset ℕ) (d : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  d.filter (fun p => p ∈ T)

def smoothFactor (T : Finset ℕ) (a : ℕ) : ℕ :=
  (insideExponent T a.factorization).prod (fun p k => p ^ k)

def roughFactor (T : Finset ℕ) (a : ℕ) : ℕ :=
  (a.factorization.filter (fun p => p ∉ T)).prod (fun p k => p ^ k)

/-- Every prime factor of `a` belongs to `T`. Arithmetic uses below assume `a>0`. -/
def Smooth (T : Finset ℕ) (a : ℕ) : Prop := a.factorization.support ⊆ T

instance (T : Finset ℕ) (a : ℕ) : Decidable (Smooth T a) :=
  inferInstanceAs (Decidable (a.factorization.support ⊆ T))

def smoothNumbers (T : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (Smooth T)

def smoothInterval (T : Finset ℕ) (n : ℕ) : Poly := polynomialOf (smoothNumbers T n)

private theorem prime_of_mem_factorization {a p : ℕ} (hp : p ∈ a.factorization.support) :
    Nat.Prime p := (Nat.mem_primeFactors.mp hp).1

private theorem prime_of_mem_filtered_factorization (T : Finset ℕ) (a : ℕ)
    (q : ℕ → Prop) [DecidablePred q] {p : ℕ}
    (hp : p ∈ (a.factorization.filter q).support) : Nat.Prime p := by
  exact prime_of_mem_factorization (Finset.mem_filter.mp hp).1

private theorem primePowerProduct_pos (d : ℕ →₀ ℕ)
    (hd : ∀ p ∈ d.support, Nat.Prime p) : 0 < d.prod (fun p k => p ^ k) := by
  apply Nat.pos_of_ne_zero
  apply Finsupp.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (hd p hp).ne_zero

theorem smoothFactor_pos (T : Finset ℕ) (a : ℕ) : 0 < smoothFactor T a := by
  apply primePowerProduct_pos
  intro p hp
  exact prime_of_mem_filtered_factorization T a (fun p => p ∈ T) hp

theorem roughFactor_pos (T : Finset ℕ) (a : ℕ) : 0 < roughFactor T a := by
  apply primePowerProduct_pos
  intro p hp
  exact prime_of_mem_filtered_factorization T a (fun p => p ∉ T) hp

theorem smoothFactor_factorization (T : Finset ℕ) (a : ℕ) :
    (smoothFactor T a).factorization = insideExponent T a.factorization := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  exact prime_of_mem_filtered_factorization T a (fun p => p ∈ T) hp

theorem roughFactor_factorization (T : Finset ℕ) (a : ℕ) :
    (roughFactor T a).factorization = a.factorization.filter (fun p => p ∉ T) := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  exact prime_of_mem_filtered_factorization T a (fun p => p ∉ T) hp

theorem smoothFactor_mul_roughFactor (T : Finset ℕ) {a : ℕ} (ha : a ≠ 0) :
    smoothFactor T a * roughFactor T a = a := by
  have h := Finsupp.prod_filter_mul_prod_filter_not
    (fun p => p ∈ T) a.factorization (fun p k => p ^ k)
  exact h.trans (Nat.factorization_prod_pow_eq_self ha)

theorem roughFactor_mul_smoothFactor (T : Finset ℕ) {a : ℕ} (ha : a ≠ 0) :
    roughFactor T a * smoothFactor T a = a := by
  rw [Nat.mul_comm, smoothFactor_mul_roughFactor T ha]

theorem smoothFactor_smooth (T : Finset ℕ) (a : ℕ) : Smooth T (smoothFactor T a) := by
  rw [Smooth, smoothFactor_factorization]
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem roughFactor_rough (T : Finset ℕ) (a : ℕ)
    (hT : ∀ p ∈ T, Nat.Prime p) : ∀ p ∈ T, ¬p ∣ roughFactor T a := by
  intro p hp hdiv
  have hval : 0 < (roughFactor T a).factorization p :=
    (hT p hp).factorization_pos_of_dvd (ne_of_gt (roughFactor_pos T a)) hdiv
  rw [roughFactor_factorization] at hval
  simp [Finsupp.filter_apply, hp] at hval

theorem roughFactor_le (T : Finset ℕ) {a : ℕ} (ha : a ≠ 0) : roughFactor T a ≤ a := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero ha)
  exact ⟨smoothFactor T a, (roughFactor_mul_smoothFactor T ha).symm⟩

theorem smoothFactor_le (T : Finset ℕ) {a : ℕ} (ha : a ≠ 0) : smoothFactor T a ≤ a := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero ha)
  exact ⟨roughFactor T a, (smoothFactor_mul_roughFactor T ha).symm⟩

theorem insideFactorization_eq_zero_of_rough (T : Finset ℕ) (b : ℕ)
    (hb : ∀ p ∈ T, ¬p ∣ b) : insideExponent T b.factorization = 0 := by
  ext p
  by_cases hp : p ∈ T
  · simp [insideExponent, Finsupp.filter_apply, hp,
      Nat.factorization_eq_zero_of_not_dvd (hb p hp)]
  · simp [insideExponent, Finsupp.filter_apply, hp]

theorem outsideFactorization_eq_self_of_rough (T : Finset ℕ) (b : ℕ)
    (hb : ∀ p ∈ T, ¬p ∣ b) :
    b.factorization.filter (fun p => p ∉ T) = b.factorization := by
  ext p
  by_cases hp : p ∈ T
  · simp [Finsupp.filter_apply, hp, Nat.factorization_eq_zero_of_not_dvd (hb p hp)]
  · simp [Finsupp.filter_apply, hp]

theorem insideFactorization_eq_self_of_smooth (T : Finset ℕ) (c : ℕ)
    (hc : Smooth T c) : insideExponent T c.factorization = c.factorization := by
  apply (Finsupp.filter_eq_self_iff _ _).mpr
  intro p hp
  exact hc (Finsupp.mem_support_iff.mpr hp)

theorem outsideFactorization_eq_zero_of_smooth (T : Finset ℕ) (c : ℕ)
    (hc : Smooth T c) : c.factorization.filter (fun p => p ∉ T) = 0 := by
  ext p
  by_cases hp : p ∈ T
  · simp [Finsupp.filter_apply, hp]
  · have hz : c.factorization p = 0 := Finsupp.notMem_support_iff.mp (fun hm => hp (hc hm))
    simp [Finsupp.filter_apply, hp, hz]

theorem roughFactor_mul_of_rough_smooth (T : Finset ℕ) {b c : ℕ}
    (hbpos : 0 < b) (hcpos : 0 < c)
    (hb : ∀ p ∈ T, ¬p ∣ b) (hc : Smooth T c) : roughFactor T (b * c) = b := by
  apply Nat.factorization_inj (ne_of_gt (roughFactor_pos T (b * c))) (ne_of_gt hbpos)
  rw [roughFactor_factorization, Nat.factorization_mul (ne_of_gt hbpos) (ne_of_gt hcpos),
    Finsupp.filter_add, outsideFactorization_eq_self_of_rough T b hb,
    outsideFactorization_eq_zero_of_smooth T c hc, add_zero]

theorem smoothFactor_mul_of_rough_smooth (T : Finset ℕ) {b c : ℕ}
    (hbpos : 0 < b) (hcpos : 0 < c)
    (hb : ∀ p ∈ T, ¬p ∣ b) (hc : Smooth T c) : smoothFactor T (b * c) = c := by
  apply Nat.factorization_inj (ne_of_gt (smoothFactor_pos T (b * c))) (ne_of_gt hcpos)
  rw [smoothFactor_factorization, Nat.factorization_mul (ne_of_gt hbpos) (ne_of_gt hcpos)]
  change (b.factorization + c.factorization).filter (fun p => p ∈ T) = _
  rw [Finsupp.filter_add, ← insideExponent, insideFactorization_eq_zero_of_rough T b hb,
    zero_add, ← insideExponent, insideFactorization_eq_self_of_smooth T c hc]

theorem mem_smoothNumbers (T : Finset ℕ) (n c : ℕ) :
    c ∈ smoothNumbers T n ↔ 1 ≤ c ∧ c ≤ n ∧ Smooth T c := by
  simp [smoothNumbers, and_assoc]

@[simp] theorem smooth_one (T : Finset ℕ) : Smooth T 1 := by simp [Smooth]

theorem roughFactor_mem (T : Finset ℕ) (hT : ∀ p ∈ T, Nat.Prime p)
    {n a : ℕ} (ha : a ∈ Finset.Icc 1 n) : roughFactor T a ∈ roughNumbers T n := by
  obtain ⟨hapos, han⟩ := Finset.mem_Icc.mp ha
  exact (mem_roughNumbers T n _).mpr
    ⟨roughFactor_pos T a, (roughFactor_le T (ne_of_gt hapos)).trans han, roughFactor_rough T a hT⟩

theorem smoothFactor_mem (T : Finset ℕ) {n a : ℕ} (ha : a ∈ Finset.Icc 1 n) :
    smoothFactor T a ∈ smoothNumbers T (n / roughFactor T a) := by
  obtain ⟨hapos, han⟩ := Finset.mem_Icc.mp ha
  apply (mem_smoothNumbers T _ _).mpr
  refine ⟨smoothFactor_pos T a, ?_, smoothFactor_smooth T a⟩
  apply (Nat.le_div_iff_mul_le (roughFactor_pos T a)).mpr
  rw [smoothFactor_mul_roughFactor T (ne_of_gt hapos)]
  exact han

end Pilz
