import WeightedPilz.BinarySmoothRows
import WeightedPilz.Components
import WeightedPilz.ComponentBounds
import WeightedPilz.Arithmetic.Counts

/-! Exact finite support trees for the binary smooth-core bound. All leaves
and odd unique-sum witnesses are kernel-checked on the true smooth supports. -/

namespace WeightedPilz.Arithmetic
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option synthInstance.maxSize 2048

def binarySmoothSupport (n : ℕ) : Finset (ℕ →₀ ℕ) :=
  (Pilz.smoothNumbers (Pilz.primesUpTo (Nat.sqrt n)) n).image Nat.factorization

private def kernelValuation (n p : ℕ) : ℕ :=
  if 0 < n ∧ n < 128 then
    ((Finset.Ico 1 7).filter (fun k => p ^ k ∣ n)).card
  else ((Finset.Ico 1 n).filter (fun k => p ^ k ∣ n)).card

private theorem kernelValuation_eq (n p : ℕ) (hp : p.Prime) :
    kernelValuation n p = n.factorization p := by
  unfold kernelValuation
  split_ifs with hn
  · symm
    apply Nat.factorization_eq_card_pow_dvd_of_lt hp hn.1
    exact hn.2.trans_le (show 128 ≤ p ^ 7 by
      calc
        128 = 2 ^ 7 := by norm_num
        _ ≤ p ^ 7 := pow_le_pow_left' hp.two_le 7)
  · exact (Nat.factorization_eq_card_pow_dvd n hp).symm

private def kernelExponent (n p : ℕ) : ℕ :=
  if kernelPrime p then kernelValuation n p else 0

private theorem kernelExponent_eq (n p : ℕ) :
    kernelExponent n p = n.factorization p := by
  unfold kernelExponent
  split_ifs with hp
  · exact kernelValuation_eq n p ((kernelPrime_iff p).mp hp)
  · exact (Nat.factorization_eq_zero_of_non_prime n
      (fun hp' => hp ((kernelPrime_iff p).mpr hp'))).symm

private def kernelFactorization (n : ℕ) : ℕ →₀ ℕ where
  support := (Finset.range (n + 1)).filter (fun p => kernelPrime p ∧ p ∣ n ∧ n ≠ 0)
  toFun p := kernelExponent n p
  mem_support_toFun p := by
    rw [kernelExponent_eq, ← Finsupp.mem_support_iff, Nat.support_factorization,
      Nat.mem_primeFactors]
    simp only [Finset.mem_filter, Finset.mem_range, kernelPrime_iff]
    constructor
    · rintro ⟨_, hp, hd, hn⟩
      exact ⟨hp, hd, hn⟩
    · rintro ⟨hp, hd, hn⟩
      exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd), hp, hd, hn⟩

private theorem kernelFactorization_eq (n : ℕ) :
    kernelFactorization n = n.factorization := by
  ext p
  exact kernelExponent_eq n p

private theorem factorizationFunction_eq : Nat.factorization = kernelFactorization :=
  funext (fun n => (kernelFactorization_eq n).symm)

private def kernelSmoothSupport (n : ℕ) : Finset (ℕ →₀ ℕ) :=
  ((Finset.Icc 1 n).filter (fun a => (kernelFactorization a).support ⊆
    (Finset.range (smallSqrt n + 1)).filter kernelPrime)).image kernelFactorization

private theorem binarySmoothSupport_eq (n : ℕ) :
    binarySmoothSupport n = kernelSmoothSupport n := by
  have hp : Pilz.primesUpTo (Nat.sqrt n) =
      (Finset.range (smallSqrt n + 1)).filter kernelPrime := by
    ext p
    simp only [Pilz.primesUpTo, Finset.mem_filter, smallSqrt_eq, kernelPrime_iff]
  unfold binarySmoothSupport kernelSmoothSupport
  rw [factorizationFunction_eq]
  congr 1
  ext a
  simp only [Pilz.smoothNumbers, Finset.mem_filter, Pilz.Smooth,
    kernelFactorization_eq, hp]

private def kernelErase (p : ℕ) (d : ℕ →₀ ℕ) : ℕ →₀ ℕ where
  support := d.support.erase p
  toFun q := if q = p then 0 else d q
  mem_support_toFun q := by
    by_cases hq : q = p
    · subst q
      simp
    · simp [hq]

private theorem kernelErase_eq (p : ℕ) (d : ℕ →₀ ℕ) :
    kernelErase p d = d.erase p := by
  ext q
  by_cases hq : q = p
  · subst q
    simp [kernelErase]
  · simp [kernelErase, hq]

private def kernelRowSupport (p k : ℕ) (S : Finset (ℕ →₀ ℕ)) : Finset (ℕ →₀ ℕ) :=
  (S.filter (fun d => d p = k)).image (kernelErase p)

private theorem rowSupport_eq (p k : ℕ) (S : Finset (ℕ →₀ ℕ)) :
    rowSupport p k S = kernelRowSupport p k S := by
  unfold rowSupport kernelRowSupport
  congr 1
  funext d
  exact (kernelErase_eq p d).symm

private def ThreeRowsTest (S : Finset (ℕ →₀ ℕ)) (p m j : ℕ)
    (a b : ℕ →₀ ℕ) : Prop :=
  2 ≤ m ∧ (∀ d ∈ S, d p ≤ m) ∧
    (rowSupport p 0 S).Nonempty ∧ (rowSupport p (m - 2) S).Nonempty ∧
    (rowSupport p (m - 1) S).Nonempty ∧ (rowSupport p m S).Nonempty ∧
    a ∈ rowSupport p (m - 2) S ∧ b ∈ rowSupport p m S ∧
    (a j + b j) % 2 = 1 ∧
    ∀ u ∈ rowSupport p (m - 2) S, ∀ v ∈ rowSupport p m S,
      (∀ k ∈ u.support ∪ v.support ∪ a.support ∪ b.support,
        u k + v k = a k + b k) → u = a ∧ v = b

private noncomputable instance (S : Finset (ℕ →₀ ℕ)) (p m j : ℕ) (a b : ℕ →₀ ℕ) :
    Decidable (ThreeRowsTest S p m j a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private theorem threeRowsSupport_of_test {S : Finset (ℕ →₀ ℕ)} {p m j : ℕ}
    {a b : ℕ →₀ ℕ} (h : ThreeRowsTest S p m j a b) : ThreeRowsSupport S p m := by
  obtain ⟨hm, hb, h0, hl, hi, ht, ha, hc, ho, hu⟩ := h
  refine ⟨hm, hb, h0, hl, hi, ht, a, ha, b, hc, j, ?_, ?_⟩
  · simpa only [Finsupp.add_apply] using ho
  · intro u hu' v hv he
    apply hu u hu' v hv
    intro k _
    exact congrArg (fun d : ℕ →₀ ℕ => d k) he

macro "smooth_decide" : tactic =>
  `(tactic| (
    dsimp only [ThreeRowsTest]
    simp only [binarySmoothSupport_eq, rowSupport_eq, factorizationFunction_eq]
    decide +kernel))

private theorem binarySmooth_low_checked :
    ∀ n ∈ Finset.Icc 25 26,
      ThreeRowsTest (binarySmoothSupport n) 3 2 5 (Nat.factorization 5) 0 ∧
      ThreeRowsTest (rowSupport 3 0 (binarySmoothSupport n)) 5 2 2
        (Nat.factorization 2) 0 ∧
      2 ≤ (rowSupport 5 0 (rowSupport 3 0 (binarySmoothSupport n))).card ∧
      2 ≤ (rowSupport 3 2 (binarySmoothSupport n)).card := by
  smooth_decide

private theorem binarySmooth_middle_checked :
    ∀ n ∈ Finset.Icc 27 48,
      ThreeRowsTest (binarySmoothSupport n) 2 (Nat.log2 n) 3 (Nat.factorization 3) 0 ∧
      ThreeRowsTest (rowSupport 2 0 (binarySmoothSupport n)) 5 2 3
        (Nat.factorization 3) 0 ∧
      2 ≤ (rowSupport 5 0 (rowSupport 2 0 (binarySmoothSupport n))).card := by
  smooth_decide

private theorem binarySmooth_high_checked :
    ∀ n ∈ Finset.Icc 49 66,
      ThreeRowsTest (binarySmoothSupport n) 2 (Nat.log2 n) 3 (Nat.factorization 3) 0 ∧
      ThreeRowsTest (rowSupport 2 0 (binarySmoothSupport n)) 7 2 3
        (Nat.factorization 3) 0 ∧
      ThreeRowsTest (rowSupport 7 0 (rowSupport 2 0 (binarySmoothSupport n)))
        5 2 3 (Nat.factorization 3) 0 ∧
      2 ≤ (rowSupport 5 0 (rowSupport 7 0 (rowSupport 2 0 (binarySmoothSupport n)))).card := by
  smooth_decide

/-- The two nested quadratic rows and two-term top row at twenty-five and twenty-six. -/
theorem binarySmooth_low_data {n : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 26) :
    ThreeRowsSupport (binarySmoothSupport n) 3 2 ∧
    ThreeRowsSupport (rowSupport 3 0 (binarySmoothSupport n)) 5 2 ∧
    2 ≤ (rowSupport 5 0 (rowSupport 3 0 (binarySmoothSupport n))).card ∧
    2 ≤ (rowSupport 3 2 (binarySmoothSupport n)).card := by
  obtain ⟨ho, hi, hleaf, htop⟩ := binarySmooth_low_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)
  exact ⟨threeRowsSupport_of_test ho, threeRowsSupport_of_test hi, hleaf, htop⟩

/-- The outer three-row obstruction and its four-term bottom row on twenty-seven through forty-eight. -/
theorem binarySmooth_middle_data {n : ℕ} (hn : 27 ≤ n) (hn' : n ≤ 48) :
    ThreeRowsSupport (binarySmoothSupport n) 2 (Nat.log2 n) ∧
    ThreeRowsSupport (rowSupport 2 0 (binarySmoothSupport n)) 5 2 ∧
    2 ≤ (rowSupport 5 0 (rowSupport 2 0 (binarySmoothSupport n))).card := by
  obtain ⟨ho, hi, hleaf⟩ := binarySmooth_middle_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)
  exact ⟨threeRowsSupport_of_test ho, threeRowsSupport_of_test hi, hleaf⟩

/-- The three nested support levels at forty-nine through sixty-six. -/
theorem binarySmooth_high_data {n : ℕ} (hn : 49 ≤ n) (hn' : n ≤ 66) :
    ThreeRowsSupport (binarySmoothSupport n) 2 (Nat.log2 n) ∧
    ThreeRowsSupport (rowSupport 2 0 (binarySmoothSupport n)) 7 2 ∧
    ThreeRowsSupport (rowSupport 7 0 (rowSupport 2 0 (binarySmoothSupport n))) 5 2 ∧
    2 ≤ (rowSupport 5 0 (rowSupport 7 0 (rowSupport 2 0 (binarySmoothSupport n)))).card := by
  obtain ⟨ho, hm, hi, hleaf⟩ := binarySmooth_high_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)
  exact ⟨threeRowsSupport_of_test ho, threeRowsSupport_of_test hm,
    threeRowsSupport_of_test hi, hleaf⟩

end WeightedPilz.Arithmetic

namespace WeightedPilz
variable {K : Type*} [Field K]

/-- Arbitrary nonzero weights have exactly the finite smooth support used in the certificates. -/
theorem smoothInterval_support_eq_binarySmoothSupport (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) :
    (smoothInterval (Pilz.primesUpTo (Nat.sqrt n)) n c).support =
      Arithmetic.binarySmoothSupport n := by
  apply support_polynomialOf
  · intro a ha
    exact (Pilz.mem_smoothNumbers _ _ _ |>.mp ha).1
  · intro a ha
    exact hc a (Finset.mem_filter.mp ha).1

end WeightedPilz
