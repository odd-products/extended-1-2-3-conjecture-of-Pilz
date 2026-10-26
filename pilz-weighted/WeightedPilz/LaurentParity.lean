import WeightedPilz.ParityPattern
import WeightedPilz.Laurent

/-! Parity class counts survive Laurent monomial clearing. -/
noncomputable section
namespace WeightedPilz
variable {σ K : Type*} [DecidableEq σ] [Field K]

def laurentParity (d : σ →₀ ℤ) : σ →₀ ℕ :=
  d.mapRange (fun z => (z % 2).toNat) (by decide)

@[simp] theorem laurentParity_apply (d : σ →₀ ℤ) (i : σ) :
    laurentParity d i = (d i % 2).toNat := rfl

theorem laurentParity_integerExponent (d : σ →₀ ℕ) :
    laurentParity (integerExponent d) = residueExponent 2 d := by
  ext i
  simp only [laurentParity_apply, integerExponent_apply, residueExponent_apply]
  omega

theorem laurentParity_translate_eq (e d f : σ →₀ ℤ) :
    laurentParity (e + d) = laurentParity (e + f) ↔ laurentParity d = laurentParity f := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun a : σ →₀ ℕ => a i) h
    simp only [laurentParity_apply, Finsupp.add_apply] at hi ⊢
    omega
  · intro h
    ext i
    have hi := congrArg (fun a : σ →₀ ℕ => a i) h
    simp only [laurentParity_apply, Finsupp.add_apply] at hi ⊢
    omega

def laurentParityWeight (H : LaurentPoly σ K) (α : σ →₀ ℕ) : ℕ := by
  classical
  exact (H.support.filter (fun d => laurentParity d = α)).card

theorem laurentParityWeight_translate (e d : σ →₀ ℤ) (H : LaurentPoly σ K) :
    laurentParityWeight (AddMonoidAlgebra.single e (1 : K) * H) (laurentParity (e + d)) =
      laurentParityWeight H (laurentParity d) := by
  classical
  unfold laurentParityWeight
  rw [AddMonoidAlgebra.support_single_mul H 1 (by simp) e, Finset.filter_map,
    Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro f hf
  exact laurentParity_translate_eq e f d

theorem laurentParityWeight_toLaurent (P : MvPolynomial σ K) (α : σ →₀ ℕ) :
    laurentParityWeight (toLaurent P) α = residueWeight 2 P α := by
  classical
  unfold laurentParityWeight
  rw [support_toLaurent, Finset.filter_image,
    Finset.card_image_of_injective _ integerExponent_injective]
  unfold residueWeight weight
  rw [support_residuePart]
  congr 1
  ext d
  simp only [Finset.mem_filter, laurentParity_integerExponent]

/-- The sharp small interval costs hold for Laurent three-term inputs too. -/
theorem laurent_interval_three_term_cost [ExpChar K 2] (k : ℕ) (hk : k ≤ 6)
    (c : ℕ → K) (hc : NonzeroWeights k c) (H : LaurentPoly ℕ K)
    (hH : H.support.card = 3) :
    tripleIntervalCost k ≤ (toLaurent (interval k c) * H).support.card := by
  classical
  have hH0 : H ≠ 0 := by intro hz; simp [hz] at hH
  obtain ⟨e, Q, hQ, hclear⟩ := exists_laurent_clearing H hH0
  have hQwt : weight Q = 3 := by
    rw [← card_support_toLaurent, hclear, card_support_laurent_translate]
    exact hH
  have hb := interval_three_term_cost k hk c hc Q hQwt
  rw [← card_support_toLaurent, map_mul, hclear, mul_left_comm,
    card_support_laurent_translate] at hb
  exact hb

theorem laurent_interval_four_term_three_class_bound [ExpChar K 2] (n : ℕ)
    (hn : n = 27 ∨ n = 28 ∨ n = 36)
    (c : ℕ → K) (hc : NonzeroWeights n c) (H : LaurentPoly ℕ K)
    (hH : H.support.card = 4) (hthree : ∃α, laurentParityWeight H α = 3) :
    (if n = 36 then 44 else 36) ≤ (toLaurent (interval n c) * H).support.card := by
  classical
  have hH0 : H ≠ 0 := by intro hz; simp [hz] at hH
  obtain ⟨e, Q, hQ, hclear⟩ := exists_laurent_clearing H hH0
  have hQwt : weight Q = 4 := by
    rw [← card_support_toLaurent, hclear, card_support_laurent_translate]
    exact hH
  obtain ⟨α, hα⟩ := hthree
  have hne : (H.support.filter (fun d => laurentParity d = α)).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < laurentParityWeight H α
    omega
  obtain ⟨d, hd⟩ := hne
  have hdα := (Finset.mem_filter.mp hd).2
  have hQthree : residueWeight 2 Q (laurentParity (e + d)) = 3 := by
    rw [← laurentParityWeight_toLaurent, hclear, laurentParityWeight_translate, hdα]
    exact hα
  have hb := interval_four_term_three_class_bound n hn c hc Q hQwt ⟨_, hQthree⟩
  rw [← card_support_toLaurent, map_mul, hclear, mul_left_comm,
    card_support_laurent_translate] at hb
  exact hb

end WeightedPilz
