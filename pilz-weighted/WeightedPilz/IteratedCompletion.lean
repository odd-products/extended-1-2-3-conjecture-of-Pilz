import WeightedPilz.SharpCompletion

/-! Repeated sharp completion, with its strict-threshold rigidity statement.
Nested `Option` adds exactly the requested finite number of fresh variables. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial

universe u v

/-- The original variable type together with `r` distinct new variables. -/
def CompletionVariables (σ : Type u) : ℕ → Type u
  | 0 => σ
  | r + 1 => Option (CompletionVariables σ r)

variable {σ : Type u} {K : Type v} [Field K]

/-- Add the independent variables one at a time. -/
def iteratedCompletion (C : MvPolynomial σ K) :
    (r : ℕ) → MvPolynomial (CompletionVariables σ r) K
  | 0 => C
  | r + 1 => freshCompletion (iteratedCompletion C r)

@[simp] theorem iteratedCompletion_zero (C : MvPolynomial σ K) :
    iteratedCompletion C 0 = C := rfl

@[simp] theorem iteratedCompletion_succ (C : MvPolynomial σ K) (r : ℕ) :
    iteratedCompletion C (r + 1) = freshCompletion (iteratedCompletion C r) := rfl

theorem iteratedCompletion_ne_zero (C : MvPolynomial σ K) (hC : C ≠ 0) (r : ℕ) :
    iteratedCompletion C r ≠ 0 := by
  cases r with
  | zero => exact hC
  | succ r => exact freshCompletion_ne_zero _

@[simp] theorem weight_iteratedCompletion (C : MvPolynomial σ K) (r : ℕ) :
    weight (iteratedCompletion C r) = weight C + r := by
  induction r with
  | zero => simp
  | succ r ih => rw [iteratedCompletion_succ, weight_freshCompletion, ih]; omega

/-- The full sharp completion inequality in `thm:completion`. -/
theorem sharp_completion (C : MvPolynomial σ K) (hC : C ≠ 0) (r : ℕ) :
    min (weight C + r) (distance C + 2 * r) ≤ distance (iteratedCompletion C r) := by
  induction r with
  | zero => simp [Nat.min_le_right]
  | succ r ih =>
    have h := sharp_completion_one (iteratedCompletion C r) (iteratedCompletion_ne_zero C hC r)
    rw [weight_iteratedCompletion] at h
    change min (weight C + (r + 1)) (distance C + 2 * (r + 1)) ≤
      distance (freshCompletion (iteratedCompletion C r))
    omega

/-- At the completion threshold the original completed polynomial is already
a minimum multiple. -/
theorem distance_iteratedCompletion_eq_weight (C : MvPolynomial σ K) (hC : C ≠ 0)
    (r : ℕ) (hr : weight C - distance C ≤ r) :
    distance (iteratedCompletion C r) = weight C + r := by
  have hδ := distance_le_weight C
  have hlo := sharp_completion C hC r
  have hhi := distance_le_weight (iteratedCompletion C r)
  rw [weight_iteratedCompletion] at hhi
  omega

/-- Every minimum at the strict completion threshold has the scalar-monomial
Frobenius form. This includes all fields through exponential characteristic. -/
theorem sharp_completion_rigidity (p : ℕ) [ExpChar K p]
    (C : MvPolynomial σ K) (hC : C ≠ 0) (r : ℕ)
    (hr : weight C - distance C < r) (hsize : 3 ≤ weight C + r)
    (G : MvPolynomial (CompletionVariables σ r) K) (hG : G ≠ 0)
    (hdvd : iteratedCompletion C r ∣ G)
    (hmin : weight G = distance (iteratedCompletion C r)) :
    ∃ (e : ℕ) (d : CompletionVariables σ r →₀ ℕ) (c : K), c ≠ 0 ∧
      G = monomial d c * iteratedCompletion C r ^ p ^ e := by
  cases r with
  | zero => omega
  | succ r =>
    have hr' : weight C - distance C ≤ r := by omega
    have hprev := distance_iteratedCompletion_eq_weight C hC r hr'
    have hprev' : distance (iteratedCompletion C r) = weight (iteratedCompletion C r) := by
      rw [hprev, weight_iteratedCompletion]
    have hmany : 2 ≤ weight (iteratedCompletion C r) := by
      rw [weight_iteratedCompletion]
      omega
    have hdist := distance_iteratedCompletion_eq_weight C hC (r + 1) (by omega)
    have hwt : weight G = weight (iteratedCompletion C r) + 1 := by
      rw [hmin, hdist, weight_iteratedCompletion]
      omega
    exact sharp_completion_one_rigidity p (iteratedCompletion C r)
      (iteratedCompletion_ne_zero C hC r) hmany hprev' G hG hdvd hwt

end WeightedPilz
