import WeightedPilz.BinomialZeroSlices
import WeightedPilz.Frobenius

/-! Two transverse triples of support points force six terms in binomial multiples. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K]

private theorem axis_triple_card [DecidableEq σ] (i : σ) {q : ℕ} (hq : 0 < q) :
    ({0, Finsupp.single i q, Finsupp.single i (2 * q)} : Finset (σ →₀ ℕ)).card = 3 := by
  classical
  have h0 : (0 : σ →₀ ℕ) ≠ Finsupp.single i q := by
    intro h
    have he := congrArg (fun d : σ →₀ ℕ => d i) h
    simp only [Finsupp.zero_apply, Finsupp.single_eq_same] at he
    omega
  have h02 : (0 : σ →₀ ℕ) ≠ Finsupp.single i (2 * q) := by
    intro h
    have he := congrArg (fun d : σ →₀ ℕ => d i) h
    simp only [Finsupp.zero_apply, Finsupp.single_eq_same] at he
    omega
  have h12 : Finsupp.single i q ≠ Finsupp.single i (2 * q) := by
    intro h
    have he := congrArg (fun d : σ →₀ ℕ => d i) h
    simp only [Finsupp.single_eq_same] at he
    omega
  simp [h0, h02, h12]

theorem weight_mul_binomial_of_two_axis_triples (F : MvPolynomial σ K)
    (i j : σ) (hij : i ≠ j) {q : ℕ} (hq : 0 < q)
    (h0 : 0 ∈ F.support)
    (hi : Finsupp.single i q ∈ F.support) (hi2 : Finsupp.single i (2 * q) ∈ F.support)
    (hj : Finsupp.single j q ∈ F.support) (hj2 : Finsupp.single j (2 * q) ∈ F.support)
    (B : MvPolynomial σ K) (hB : weight B = 2) : 6 ≤ weight (F * B) := by
  classical
  obtain ⟨a, b, u, v, hab, hu, hv, rfl⟩ := exists_two_monomials_of_weight_two B hB
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
    by_contra! hn
    exact hab (Finsupp.ext hn)
  have aux (l : σ) (hl : l ≠ k) (hl1 : Finsupp.single l q ∈ F.support)
      (hl2 : Finsupp.single l (2 * q) ∈ F.support) :
      6 ≤ weight (F * (monomial a u + monomial b v)) := by
    let T : Finset (σ →₀ ℕ) := {0, Finsupp.single l q, Finsupp.single l (2 * q)}
    have hT : T ⊆ F.support := by
      intro d hd
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl
      · exact h0
      · exact hl1
      · exact hl2
    have hz : ∀ d ∈ T, d k = 0 := by
      intro d hd
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl <;> simp [hl.symm]
    have h := weight_mul_binomial_of_zero_slice F T hT a b u v hu hv k hk hz
    simpa only [T, axis_triple_card l hq] using h
  by_cases hik : i = k
  · subst k
    exact aux j hij.symm hj hj2
  · exact aux i hik hi hi2

theorem weight_distinguished_power_mul_binomial_of_two_axes
    (p e : ℕ) [ExpChar K p] (F : MvPolynomial σ K) (i j : σ) (hij : i ≠ j)
    (h0 : 0 ∈ F.support)
    (hi : Finsupp.single i 1 ∈ F.support) (hi2 : Finsupp.single i 2 ∈ F.support)
    (hj : Finsupp.single j 1 ∈ F.support) (hj2 : Finsupp.single j 2 ∈ F.support)
    (B : MvPolynomial σ K) (hB : weight B = 2) :
    6 ≤ weight (F ^ p ^ e * B) := by
  classical
  have hq : 0 < p ^ e := pow_pos (expChar_pos K p) e
  have hlift (d : σ →₀ ℕ) (hd : d ∈ F.support) :
      scaleExponent (p ^ e) d ∈ (F ^ p ^ e).support := by
    rw [support_pow_expChar]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  apply weight_mul_binomial_of_two_axis_triples (F ^ p ^ e) i j hij hq
  · simpa [scaleExponent] using hlift 0 h0
  · simpa [scaleExponent, Finsupp.smul_single, smul_eq_mul] using hlift _ hi
  · simpa [scaleExponent, Finsupp.smul_single, smul_eq_mul, Nat.mul_comm] using hlift _ hi2
  · simpa [scaleExponent, Finsupp.smul_single, smul_eq_mul] using hlift _ hj
  · simpa [scaleExponent, Finsupp.smul_single, smul_eq_mul, Nat.mul_comm] using hlift _ hj2
  · exact hB

end WeightedPilz
