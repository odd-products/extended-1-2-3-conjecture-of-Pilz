import Pilz.Support
import Pilz.Parity

/-!
# Partial derivatives and fresh exponent parity

These are the support facts behind the synchronization argument in Section 3.
Multiplying a derivative by its variable recovers exactly the odd exponent
part of the original polynomial. Thus differentiation cannot cancel two
surviving terms or introduce a base exponent absent from the original.
-/

noncomputable section

namespace Pilz

open MvPolynomial

/-- Keep the terms whose exponent of `i` is odd. -/
def oddPart (P : Poly) (i : ℕ) : Poly := by
  classical
  exact Finsupp.filter (fun d => Odd (d i)) P

/-- The number of terms with odd exponent in one specified variable. -/
def oddCount (P : Poly) (i : ℕ) : ℕ := by
  classical
  exact (P.support.filter (fun d => Odd (d i))).card

theorem support_oddPart (P : Poly) (i : ℕ) :
    (oddPart P i).support = P.support.filter (fun d => Odd (d i)) := rfl

theorem oddPart_add (P Q : Poly) (i : ℕ) :
    oddPart (P + Q) i = oddPart P i + oddPart Q i := by
  classical
  exact Finsupp.filter_add

theorem oddPart_monomial (d : ℕ →₀ ℕ) (c : ZMod 2) (i : ℕ) :
    oddPart (monomial d c) i = if Odd (d i) then monomial d c else 0 := by
  classical
  by_cases h : Odd (d i)
  · rw [if_pos h]
    exact Finsupp.filter_single_of_pos _ h
  · rw [if_neg h]
    exact Finsupp.filter_single_of_neg _ h

/-- In characteristic two, multiplying a partial derivative by its variable
retains precisely the original odd-exponent terms, coefficient for coefficient. -/
theorem X_mul_pderiv_eq_oddPart (P : Poly) (i : ℕ) :
    X i * pderiv i P = oddPart P i := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [X_mul_pderiv_monomial, smul_monomial, oddPart_monomial]
      by_cases h : Odd (d i)
      · rw [if_pos h]
        simp [nsmul_eq_mul, ZMod.natCast_eq_one_iff_odd.mpr h]
      · rw [if_neg h]
        simp [nsmul_eq_mul, ZMod.natCast_eq_zero_iff_even.mpr (Nat.not_odd_iff_even.mp h)]
  | add P Q hP hQ =>
      rw [map_add, mul_add, hP, hQ, oddPart_add]

theorem weight_pderiv (P : Poly) (i : ℕ) :
    weight (pderiv i P) = oddCount P i := by
  calc
    weight (pderiv i P) = weight (X i * pderiv i P) :=
      (weight_monomial_mul (Finsupp.single i 1) (pderiv i P)).symm
    _ = weight (oddPart P i) := by rw [X_mul_pderiv_eq_oddPart]
    _ = oddCount P i := rfl

theorem oddCount_le_weight (P : Poly) (i : ℕ) : oddCount P i ≤ weight P := by
  classical
  exact Finset.card_filter_le _ _

theorem weight_pderiv_le (P : Poly) (i : ℕ) : weight (pderiv i P) ≤ weight P := by
  rw [weight_pderiv]
  exact oddCount_le_weight P i

/-- The weight budget for a sum of two fresh derivatives. -/
theorem weight_pair_pderiv_le (P : Poly) (i j : ℕ) :
    weight (pderiv i P + pderiv j P) ≤ oddCount P i + oddCount P j := by
  have h : weight (pderiv i P + pderiv j P) ≤
      weight (pderiv i P) + weight (pderiv j P) :=
    (Finset.card_le_card (MvPolynomial.support_add)).trans (Finset.card_union_le _ _)
  simpa [weight_pderiv] using h

/-- Equal derivatives of the factor cancel in a pair derivative, so the
pair maps every multiple back into the same principal ideal. -/
theorem pair_pderiv_mul (F H : Poly) (i j : ℕ)
    (hF : pderiv i F = pderiv j F) :
    pderiv i (F * H) + pderiv j (F * H) = F * (pderiv i H + pderiv j H) := by
  simp only [pderiv_mul]
  rw [hF]
  calc
    (pderiv j F * H + F * pderiv i H) + (pderiv j F * H + F * pderiv j H) =
        (pderiv j F * H + pderiv j F * H) + (F * pderiv i H + F * pderiv j H) := by
      ac_rfl
    _ = F * (pderiv i H + pderiv j H) := by
      rw [CharTwo.add_self_eq_zero, zero_add, mul_add]

theorem dvd_pair_pderiv {F G : Poly} (i j : ℕ)
    (hF : pderiv i F = pderiv j F) (hG : F ∣ G) :
    F ∣ pderiv i G + pderiv j G := by
  obtain ⟨H, rfl⟩ := hG
  rw [pair_pderiv_mul F H i j hF]
  exact dvd_mul_right _ _

/-- Multiplication by `X i` translates the whole support without cancellation. -/
theorem support_X_mul (P : Poly) (i : ℕ) :
    (X i * P).support = P.support.map (addLeftEmbedding (Finsupp.single i 1)) := by
  exact AddMonoidAlgebra.support_single_mul P 1 (by simp) (Finsupp.single i 1)

/-- The derivative support, translated back up by one, is exactly the original
odd support. This gives an explicit support bijection. -/
theorem support_pderiv_shift (P : Poly) (i : ℕ) :
    (pderiv i P).support.map (addLeftEmbedding (Finsupp.single i 1)) =
      P.support.filter (fun d => Odd (d i)) := by
  rw [← support_X_mul, X_mul_pderiv_eq_oddPart, support_oddPart]

theorem mem_support_pderiv_shift {P : Poly} {i : ℕ} {d : ℕ →₀ ℕ}
    (hd : d ∈ (pderiv i P).support) :
    Finsupp.single i 1 + d ∈ P.support ∧ Odd (((Finsupp.single i 1 : ℕ →₀ ℕ) + d) i) := by
  classical
  have hm : Finsupp.single i 1 + d ∈
      (pderiv i P).support.map (addLeftEmbedding (Finsupp.single i 1)) :=
    Finset.mem_map.mpr ⟨d, hd, rfl⟩
  rw [support_pderiv_shift] at hm
  exact Finset.mem_filter.mp hm

/-- A derivative does not introduce any exponent in any other variable. -/
theorem pderiv_base_exponents {P : Poly} {i : ℕ} {d : ℕ →₀ ℕ}
    (hd : d ∈ (pderiv i P).support) :
    ∃ e ∈ P.support, ∀ j : ℕ, j ≠ i → e j = d j := by
  refine ⟨Finsupp.single i 1 + d, (mem_support_pderiv_shift hd).1, ?_⟩
  intro j hji
  simp [Finsupp.add_apply, hji.symm]

/-- At any coordinate distinct from both differentiated variables, a term
of the pair derivative still has an exponent already present in `P`. -/
theorem pair_pderiv_base_exponent {P : Poly} {i j k : ℕ} {d : ℕ →₀ ℕ}
    (hd : d ∈ (pderiv i P + pderiv j P).support)
    (hki : k ≠ i) (hkj : k ≠ j) : ∃ e ∈ P.support, e k = d k := by
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hi | hj
  · obtain ⟨e, he, heq⟩ := pderiv_base_exponents hi
    exact ⟨e, he, heq k hki⟩
  · obtain ⟨e, he, heq⟩ := pderiv_base_exponents hj
    exact ⟨e, he, heq k hkj⟩

/-- Every derivative is even in the variable differentiated. -/
theorem even_exponent_of_mem_support_pderiv {P : Poly} {i : ℕ} {d : ℕ →₀ ℕ}
    (hd : d ∈ (pderiv i P).support) : Even (d i) := by
  have h := (mem_support_pderiv_shift hd).2
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at h
  apply Nat.not_odd_iff_even.mp
  apply Nat.odd_add_one.mp
  simpa only [Nat.add_comm] using h

theorem pderiv_eq_zero_iff_even_exponents (P : Poly) (i : ℕ) :
    pderiv i P = 0 ↔ ∀ d ∈ P.support, Even (d i) := by
  classical
  constructor
  · intro hz d hd
    have hempty : P.support.filter (fun d => Odd (d i)) = ∅ := by
      rw [← support_pderiv_shift, hz]
      simp
    by_contra hnot
    have hodd : Odd (d i) := Nat.not_even_iff_odd.mp hnot
    have hmem : d ∈ P.support.filter (fun d => Odd (d i)) := Finset.mem_filter.mpr ⟨hd, hodd⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  · intro heven
    have hpart : oddPart P i = 0 := by
      apply MvPolynomial.support_eq_empty.mp
      rw [support_oddPart]
      apply Finset.filter_eq_empty_iff.mpr
      intro d hd
      exact Nat.not_odd_iff_even.mpr (heven d hd)
    have hmul : X i * pderiv i P = 0 := by rw [X_mul_pderiv_eq_oddPart, hpart]
    exact (mul_eq_zero.mp hmul).resolve_left (MvPolynomial.X_ne_zero i)

/-- Multiplying by a variable complements its own odd-term count. -/
theorem oddCount_X_mul_self (P : Poly) (i : ℕ) :
    oddCount (X i * P) i + oddCount P i = weight P := by
  classical
  have hshift : oddCount (X i * P) i =
      (P.support.filter (fun d => ¬ Odd (d i))).card := by
    unfold oddCount
    rw [support_X_mul, Finset.filter_map, Finset.card_map]
    congr 1
    apply Finset.filter_congr
    intro d _
    change Odd (((Finsupp.single i 1 : ℕ →₀ ℕ) + d) i) ↔ ¬ Odd (d i)
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [Nat.add_comm 1, Nat.odd_add_one]
  rw [hshift]
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := P.support)
    (fun d : ℕ →₀ ℕ => Odd (d i))
  simpa [oddCount, weight, Nat.add_comm] using h

/-- Multiplying by another variable leaves the specified odd-term count fixed. -/
theorem oddCount_X_mul_of_ne (P : Poly) (i j : ℕ) (hji : j ≠ i) :
    oddCount (X i * P) j = oddCount P j := by
  classical
  unfold oddCount
  rw [support_X_mul, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro d _
  simp [Finsupp.add_apply, hji.symm]

theorem oddCount_X_mul_self_complement (P : Poly) (i : ℕ) :
    oddCount (X i * P) i = weight P - oddCount P i := by
  have h := oddCount_X_mul_self P i
  omega

theorem pderiv_eq_zero_of_exponent_zero (P : Poly) (i : ℕ)
    (h : ∀ d ∈ P.support, d i = 0) : pderiv i P = 0 := by
  apply (pderiv_eq_zero_iff_even_exponents P i).mpr
  intro d hd
  simp [h d hd]

end Pilz
