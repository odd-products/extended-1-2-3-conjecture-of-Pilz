import WeightedPilz.Support
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Tactic.Abel

/-! Width additivity for arbitrary additive directions, including integer vectors. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K Γ : Type*} [Field K] [DecidableEq σ]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

def directionalMax (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K) : Γ := by
  classical
  exact if h : P = 0 then 0 else P.support.sup' (MvPolynomial.support_nonempty.mpr h) v

theorem directionalMax_eq (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K) (hP : P ≠ 0) :
    directionalMax v P = P.support.sup' (MvPolynomial.support_nonempty.mpr hP) v := by
  simp only [directionalMax, dif_neg hP]

theorem le_directionalMax (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K)
    {d : σ →₀ ℕ} (hd : d ∈ P.support) : v d ≤ directionalMax v P := by
  have hP : P ≠ 0 := by intro hz; simpa [hz] using hd
  rw [directionalMax_eq v P hP]
  exact Finset.le_sup' v hd

theorem exists_directionalMax (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K) (hP : P ≠ 0) :
    ∃ d ∈ P.support, v d = directionalMax v P := by
  rw [directionalMax_eq v P hP]
  obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_sup' (MvPolynomial.support_nonempty.mpr hP) v
  exact ⟨d, hd, heq.symm⟩

def directionalTop (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K) : MvPolynomial σ K :=
  P.filter (fun d => v d = directionalMax v P)

theorem coeff_directionalTop (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K) (d : σ →₀ ℕ) :
    coeff d (directionalTop v P) = if v d = directionalMax v P then coeff d P else 0 := rfl

theorem support_directionalTop (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K) :
    (directionalTop v P).support = P.support.filter (fun d => v d = directionalMax v P) := rfl

theorem directionalTop_ne_zero (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K) (hP : P ≠ 0) :
    directionalTop v P ≠ 0 := by
  obtain ⟨d, hd, heq⟩ := exists_directionalMax v P hP
  apply MvPolynomial.support_nonempty.mp
  rw [support_directionalTop]
  exact ⟨d, Finset.mem_filter.mpr ⟨hd, heq⟩⟩

theorem coeff_mul_at_directionalMax (v : (σ →₀ ℕ) →+ Γ) (P Q : MvPolynomial σ K)
    (d : σ →₀ ℕ) (hd : v d = directionalMax v P + directionalMax v Q) :
    coeff d (P * Q) = coeff d (directionalTop v P * directionalTop v Q) := by
  classical
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ hab
  have hab' : a + b = d := Finset.mem_antidiagonal.mp hab
  rw [coeff_directionalTop, coeff_directionalTop]
  by_cases ha : a ∈ P.support
  · by_cases hb : b ∈ Q.support
    · have hva := le_directionalMax v P ha
      have hvb := le_directionalMax v Q hb
      have hsum : v a + v b = directionalMax v P + directionalMax v Q := by
        rw [← map_add, hab', hd]
      have hea : v a = directionalMax v P := by
        apply le_antisymm hva
        by_contra hnot
        have hlt := add_lt_add_of_lt_of_le (lt_of_not_ge hnot) hvb
        exact (ne_of_lt hlt) hsum
      have heb : v b = directionalMax v Q := by
        rw [hea] at hsum
        exact add_left_cancel hsum
      rw [if_pos hea, if_pos heb]
    · simp [notMem_support_iff.mp hb]
  · simp [notMem_support_iff.mp ha]

theorem directionalMax_mul (v : (σ →₀ ℕ) →+ Γ) (P Q : MvPolynomial σ K)
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    directionalMax v (P * Q) = directionalMax v P + directionalMax v Q := by
  classical
  apply le_antisymm
  · rw [directionalMax_eq v (P * Q) (mul_ne_zero hP hQ)]
    apply Finset.sup'_le
    intro d hd
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
    rw [map_add]
    exact add_le_add (le_directionalMax v P ha) (le_directionalMax v Q hb)
  · obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr
      (mul_ne_zero (directionalTop_ne_zero v P hP) (directionalTop_ne_zero v Q hQ))
    have hdeg : v d = directionalMax v P + directionalMax v Q := by
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hd)
      rw [support_directionalTop] at ha hb
      rw [map_add, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2]
    have hdPQ : d ∈ (P * Q).support := by
      apply MvPolynomial.mem_support_iff.mpr
      rw [coeff_mul_at_directionalMax v P Q d hdeg]
      exact MvPolynomial.mem_support_iff.mp hd
    rw [← hdeg]
    exact le_directionalMax v (P * Q) hdPQ

/-- Maximum minus minimum; the minimum is the negative maximum in the opposite direction. -/
def directionalWidth (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K) : Γ :=
  directionalMax v P + directionalMax (-v) P

theorem directionalWidth_nonneg (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K) :
    0 ≤ directionalWidth v P := by
  by_cases hP : P = 0
  · simp [directionalWidth, directionalMax, hP]
  · obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hP
    have h := add_le_add (le_directionalMax v P hd) (le_directionalMax (-v) P hd)
    simpa only [AddMonoidHom.neg_apply, add_neg_cancel] using h

theorem directionalWidth_mul (v : (σ →₀ ℕ) →+ Γ) (P Q : MvPolynomial σ K)
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    directionalWidth v (P * Q) = directionalWidth v P + directionalWidth v Q := by
  simp only [directionalWidth, directionalMax_mul v P Q hP hQ,
    directionalMax_mul (-v) P Q hP hQ]
  abel

theorem directionalWidth_eq_zero_iff (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K)
    (hP : P ≠ 0) : directionalWidth v P = 0 ↔
      ∀ a ∈ P.support, ∀ b ∈ P.support, v a = v b := by
  constructor
  · intro hzero a ha b hb
    have hmax : directionalMax v P = -directionalMax (-v) P :=
      eq_neg_of_add_eq_zero_left hzero
    have heq : ∀ d ∈ P.support, v d = directionalMax v P := by
      intro d hd
      apply le_antisymm (le_directionalMax v P hd)
      have h := neg_le_neg (le_directionalMax (-v) P hd)
      simpa only [AddMonoidHom.neg_apply, neg_neg, ← hmax] using h
    exact (heq a ha).trans (heq b hb).symm
  · intro h
    obtain ⟨a, ha, hea⟩ := exists_directionalMax v P hP
    obtain ⟨b, hb, heb⟩ := exists_directionalMax (-v) P hP
    rw [directionalWidth, ← hea, ← heb]
    simp only [AddMonoidHom.neg_apply, h a ha b hb, add_neg_cancel]

theorem directionalWidth_eq_sup_sub_inf (v : (σ →₀ ℕ) →+ Γ) (P : MvPolynomial σ K)
    (hP : P ≠ 0) : directionalWidth v P =
      P.support.sup' (MvPolynomial.support_nonempty.mpr hP) v -
        P.support.inf' (MvPolynomial.support_nonempty.mpr hP) v := by
  have hmin : directionalMax (-v) P = -P.support.inf' (MvPolynomial.support_nonempty.mpr hP) v := by
    apply le_antisymm
    · rw [directionalMax_eq (-v) P hP]
      apply Finset.sup'_le
      intro d hd
      exact neg_le_neg (Finset.inf'_le v hd)
    · obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_inf' (MvPolynomial.support_nonempty.mpr hP) v
      rw [heq]
      exact le_directionalMax (-v) P hd
  rw [directionalWidth, directionalMax_eq v P hP, hmin, sub_eq_add_neg]

def integerDirection (v : σ → ℤ) : (σ →₀ ℕ) →+ ℤ where
  toFun d := d.sum (fun i n => (n : ℤ) * v i)
  map_zero' := by simp
  map_add' a b := by
    apply Finsupp.sum_add_index'
    · intro i
      simp
    · intro i a b
      simp [Nat.cast_add, add_mul]

def integerWidth (v : σ → ℤ) (P : MvPolynomial σ K) : ℤ :=
  directionalWidth (integerDirection v) P

theorem integerWidth_mul (v : σ → ℤ) (P Q : MvPolynomial σ K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    integerWidth v (P * Q) = integerWidth v P + integerWidth v Q :=
  directionalWidth_mul (integerDirection v) P Q hP hQ

end WeightedPilz
