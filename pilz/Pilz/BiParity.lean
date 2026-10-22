import Pilz.Derivatives
import Mathlib.Tactic.Ring

/-!
# Splitting two variables by exponent parity

This file supplies the four parity blocks in Step 3 of the synchronized
normal-form argument. The blocks themselves are even in both variables;
the accompanying factors record their two parity bits.
-/

noncomputable section

namespace Pilz

open MvPolynomial

/-- Retain the terms whose exponent of the specified variable is even. -/
def evenPart (P : Poly) (i : ℕ) : Poly := by
  classical
  exact Finsupp.filter (fun d => Even (d i)) P

theorem support_evenPart (P : Poly) (i : ℕ) :
    (evenPart P i).support = P.support.filter (fun d => Even (d i)) := rfl

theorem evenPart_even (P : Poly) (i : ℕ) :
    ∀ d ∈ (evenPart P i).support, Even (d i) := by
  intro d hd
  exact (Finset.mem_filter.mp hd).2

theorem evenPart_preserves_even (P : Poly) (i j : ℕ)
    (h : ∀ d ∈ P.support, Even (d j)) :
    ∀ d ∈ (evenPart P i).support, Even (d j) := by
  intro d hd
  exact h d (Finset.mem_filter.mp hd).1

theorem evenPart_add_oddPart (P : Poly) (i : ℕ) :
    evenPart P i + oddPart P i = P := by
  classical
  apply MvPolynomial.ext
  intro d
  change (if Even (d i) then coeff d P else 0) +
    (if Odd (d i) then coeff d P else 0) = coeff d P
  rcases Nat.even_or_odd (d i) with he | ho
  · simp [he, Nat.not_odd_iff_even.mpr he]
  · simp [ho, Nat.not_even_iff_odd.mpr ho]

theorem split_even_pderiv (P : Poly) (i : ℕ) :
    P = evenPart P i + X i * pderiv i P := by
  rw [X_mul_pderiv_eq_oddPart, evenPart_add_oddPart]

theorem weight_evenPart_add_oddCount (P : Poly) (i : ℕ) :
    weight (evenPart P i) + oddCount P i = weight P := by
  have hd : Disjoint (evenPart P i).support (oddPart P i).support := by
    classical
    apply Finset.disjoint_left.mpr
    intro d he ho
    exact (Nat.not_odd_iff_even.mpr (Finset.mem_filter.mp he).2)
      (Finset.mem_filter.mp ho).2
  have hw := weight_add_of_disjoint (evenPart P i) (oddPart P i) hd
  rw [evenPart_add_oddPart] at hw
  exact hw.symm

theorem pderiv_preserves_even_of_ne (P : Poly) (i j : ℕ) (hij : i ≠ j)
    (h : ∀ d ∈ P.support, Even (d j)) :
    ∀ d ∈ (pderiv i P).support, Even (d j) := by
  intro d hd
  obtain ⟨e, he, heq⟩ := pderiv_base_exponents hd
  rw [← heq j hij.symm]
  exact h e he

def bi00 (P : Poly) (i j : ℕ) : Poly := evenPart (evenPart P j) i
def bi10 (P : Poly) (i j : ℕ) : Poly := pderiv i (evenPart P j)
def bi01 (P : Poly) (i j : ℕ) : Poly := evenPart (pderiv j P) i
def bi11 (P : Poly) (i j : ℕ) : Poly := pderiv i (pderiv j P)

/-- The four parity blocks reconstruct the original polynomial. -/
theorem bi_reconstruct (P : Poly) (i j : ℕ) :
    P = bi00 P i j + X i * bi10 P i j + X j * bi01 P i j +
      X i * X j * bi11 P i j := by
  calc
    P = evenPart P j + X j * pderiv j P := split_even_pderiv P j
    _ = (bi00 P i j + X i * bi10 P i j) +
        X j * (bi01 P i j + X i * bi11 P i j) := by
      rw [split_even_pderiv (evenPart P j) i, split_even_pderiv (pderiv j P) i]
      rfl
    _ = _ := by ring

theorem bi00_even (P : Poly) (i j : ℕ) :
    (∀ d ∈ (bi00 P i j).support, Even (d i)) ∧
    (∀ d ∈ (bi00 P i j).support, Even (d j)) := by
  exact ⟨evenPart_even _ _, evenPart_preserves_even _ _ _ (evenPart_even P j)⟩

theorem bi10_even (P : Poly) (i j : ℕ) (hij : i ≠ j) :
    (∀ d ∈ (bi10 P i j).support, Even (d i)) ∧
    (∀ d ∈ (bi10 P i j).support, Even (d j)) := by
  exact ⟨fun _ hd => even_exponent_of_mem_support_pderiv hd,
    pderiv_preserves_even_of_ne _ i j hij (evenPart_even P j)⟩

theorem bi01_even (P : Poly) (i j : ℕ) :
    (∀ d ∈ (bi01 P i j).support, Even (d i)) ∧
    (∀ d ∈ (bi01 P i j).support, Even (d j)) := by
  exact ⟨evenPart_even _ _, evenPart_preserves_even _ _ _
    (fun _ hd => even_exponent_of_mem_support_pderiv hd)⟩

theorem bi11_even (P : Poly) (i j : ℕ) (hij : i ≠ j) :
    (∀ d ∈ (bi11 P i j).support, Even (d i)) ∧
    (∀ d ∈ (bi11 P i j).support, Even (d j)) := by
  exact ⟨fun _ hd => even_exponent_of_mem_support_pderiv hd,
    pderiv_preserves_even_of_ne _ i j hij
      (fun _ hd => even_exponent_of_mem_support_pderiv hd)⟩

/-- A variable shift turns an even support into an odd support. -/
theorem odd_exponents_X_mul_of_even (P : Poly) (i : ℕ)
    (h : ∀ d ∈ P.support, Even (d i)) :
    ∀ d ∈ (X i * P).support, Odd (d i) := by
  classical
  intro d hd
  rw [support_X_mul] at hd
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hd
  simpa only [Function.Embedding.coeFn_mk, addLeftEmbedding_apply,
    Finsupp.add_apply, Finsupp.single_eq_same] using (h e he).one_add

theorem disjoint_support_even_odd (A B : Poly) (i : ℕ)
    (hA : ∀ d ∈ A.support, Even (d i)) (hB : ∀ d ∈ B.support, Odd (d i)) :
    Disjoint A.support B.support := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hdA hdB
  exact (Nat.not_even_iff_odd.mpr (hB d hdB)) (hA d hdA)

/-- Differentiating the four-block decomposition in its first coordinate. -/
theorem bi_pderiv_i (P : Poly) (i j : ℕ) (hij : i ≠ j) :
    pderiv i P = bi10 P i j + X j * bi11 P i j := by
  have h00 := (pderiv_eq_zero_iff_even_exponents _ i).mpr (bi00_even P i j).1
  have h10 := (pderiv_eq_zero_iff_even_exponents _ i).mpr (bi10_even P i j hij).1
  have h01 := (pderiv_eq_zero_iff_even_exponents _ i).mpr (bi01_even P i j).1
  have h11 := (pderiv_eq_zero_iff_even_exponents _ i).mpr (bi11_even P i j hij).1
  have h := congrArg (fun Q : Poly => pderiv i Q) (bi_reconstruct P i j)
  simpa only [map_add, pderiv_mul, pderiv_X_self, pderiv_X_of_ne hij.symm,
    h00, h10, h01, h11, mul_zero, zero_mul, zero_add, add_zero, one_mul,
    mul_one] using h

theorem bi_pderiv_j (P : Poly) (i j : ℕ) (hij : i ≠ j) :
    pderiv j P = bi01 P i j + X i * bi11 P i j := by
  have h00 := (pderiv_eq_zero_iff_even_exponents _ j).mpr (bi00_even P i j).2
  have h10 := (pderiv_eq_zero_iff_even_exponents _ j).mpr (bi10_even P i j hij).2
  have h01 := (pderiv_eq_zero_iff_even_exponents _ j).mpr (bi01_even P i j).2
  have h11 := (pderiv_eq_zero_iff_even_exponents _ j).mpr (bi11_even P i j hij).2
  have h := congrArg (fun Q : Poly => pderiv j Q) (bi_reconstruct P i j)
  simpa only [map_add, pderiv_mul, pderiv_X_self, pderiv_X_of_ne hij,
    h00, h10, h01, h11, mul_zero, zero_mul, zero_add, add_zero, one_mul,
    mul_one] using h

/-- The sum of the two partial derivatives in the balanced-case proof. -/
theorem bi_pair_pderiv (P : Poly) (i j : ℕ) (hij : i ≠ j) :
    pderiv i P + pderiv j P = bi10 P i j + bi01 P i j +
      (X i + X j) * bi11 P i j := by
  rw [bi_pderiv_i P i j hij, bi_pderiv_j P i j hij, add_mul]
  ac_rfl

/-- The four blocks partition the weight of the polynomial. -/
theorem bi_weight (P : Poly) (i j : ℕ) :
    weight P = weight (bi00 P i j) + weight (bi10 P i j) +
      weight (bi01 P i j) + weight (bi11 P i j) := by
  have h0 := weight_evenPart_add_oddCount P j
  have h1 := weight_evenPart_add_oddCount (evenPart P j) i
  have h2 := weight_evenPart_add_oddCount (pderiv j P) i
  simp only [← weight_pderiv] at h0 h1 h2
  change weight (bi00 P i j) + weight (bi10 P i j) = _ at h1
  change weight (bi01 P i j) + weight (bi11 P i j) = _ at h2
  omega

theorem bi_oddCount_i (P : Poly) (i j : ℕ) (hij : i ≠ j) :
    oddCount P i = weight (bi10 P i j) + weight (bi11 P i j) := by
  have hd : Disjoint (bi10 P i j).support (X j * bi11 P i j).support :=
    disjoint_support_even_odd _ _ j (bi10_even P i j hij).2
      (odd_exponents_X_mul_of_even _ j (bi11_even P i j hij).2)
  rw [← weight_pderiv, bi_pderiv_i P i j hij,
    weight_add_of_disjoint _ _ hd]
  exact congrArg (fun k => weight (bi10 P i j) + k)
    (weight_monomial_mul (Finsupp.single j 1) (bi11 P i j))

theorem bi_oddCount_j (P : Poly) (i j : ℕ) :
    oddCount P j = weight (bi01 P i j) + weight (bi11 P i j) := by
  have h := weight_evenPart_add_oddCount (pderiv j P) i
  simpa only [bi01, bi11, weight_pderiv] using h.symm

/-- When both one-odd blocks vanish, differentiating `X i * P` in the
two coordinates leaves exactly the two displayed even blocks. -/
theorem bi_pair_pderiv_X_mul (P : Poly) (i j : ℕ) (hij : i ≠ j)
    (h10 : bi10 P i j = 0) (h01 : bi01 P i j = 0) :
    pderiv i (X i * P) + pderiv j (X i * P) =
      bi00 P i j + X i ^ 2 * bi11 P i j := by
  have hp : P = bi00 P i j + X i * X j * bi11 P i j := by
    simpa only [h10, h01, mul_zero, add_zero] using bi_reconstruct P i j
  rw [pderiv_mul, pderiv_mul, pderiv_X_self, pderiv_X_of_ne hij,
    one_mul, zero_mul, zero_add, bi_pderiv_i P i j hij,
    bi_pderiv_j P i j hij, h10, h01, zero_add, zero_add]
  calc
    (P + X i * (X j * bi11 P i j)) + X i * (X i * bi11 P i j) =
      (bi00 P i j + X i * X j * bi11 P i j) +
        X i * X j * bi11 P i j + X i ^ 2 * bi11 P i j := by
      conv_lhs => lhs; lhs; rw [hp]
      simp only [pow_two, mul_assoc]
    _ = _ := by rw [CharTwo.add_cancel_right]

/-- The odd count in the first coordinate of the pair derivative is the
weight of the double-odd block. -/
theorem oddCount_bi_pair_pderiv (P : Poly) (i j : ℕ) (hij : i ≠ j) :
    oddCount (pderiv i P + pderiv j P) i = weight (bi11 P i j) := by
  rw [← weight_pderiv, bi_pair_pderiv P i j hij]
  have h10 := (pderiv_eq_zero_iff_even_exponents _ i).mpr (bi10_even P i j hij).1
  have h01 := (pderiv_eq_zero_iff_even_exponents _ i).mpr (bi01_even P i j).1
  have h11 := (pderiv_eq_zero_iff_even_exponents _ i).mpr (bi11_even P i j hij).1
  simp only [map_add, pderiv_mul, pderiv_X_self, pderiv_X_of_ne hij.symm,
    h10, h01, h11, zero_add, add_zero, mul_zero, one_mul]

/-- Equal half-weight odd counts force the opposite block weights to agree. -/
theorem bi_balanced_weights (P : Poly) (i j : ℕ) (hij : i ≠ j)
    (hi : 2 * oddCount P i = weight P) (hj : 2 * oddCount P j = weight P) :
    weight (bi10 P i j) = weight (bi01 P i j) ∧
      weight (bi00 P i j) = weight (bi11 P i j) ∧
      weight P = 2 * (weight (bi00 P i j) + weight (bi10 P i j)) := by
  have hm := bi_weight P i j
  rw [bi_oddCount_i P i j hij] at hi
  rw [bi_oddCount_j P i j] at hj
  omega

end Pilz
