import Pilz.F9Valuations

/-! The at-most-four-term contradiction after the exceptional-core substitution. -/

noncomputable section

namespace Pilz.F9Param

open Polynomial
open scoped BigOperators

def term (t : ℕ × ℕ) : R := U ^ t.1 * V ^ t.2

theorem sum_U_powers_ne_zero (A : Finset ℕ) (hA : A.Nonempty) :
    (∑ a ∈ A, U ^ a) ≠ 0 := by
  classical
  let P : R := ∑ a ∈ A, X ^ a
  have hP : P ≠ 0 := by
    obtain ⟨a, ha⟩ := hA
    intro hz
    have hc : P.coeff a = 1 := by simp [P, finset_sum_coeff, coeff_X_pow, ha]
    rw [hz, coeff_zero] at hc
    exact zero_ne_one hc
  have hU : U ≠ Polynomial.C (U.coeff 0) := by
    intro hz
    have hd := congrArg Polynomial.natDegree hz
    rw [U_degree, Polynomial.natDegree_C] at hd
    omega
  intro hz
  have hc : P.comp U = 0 := by simpa [P, Polynomial.sum_comp] using hz
  rcases Polynomial.comp_eq_zero_iff.mp hc with hp | ⟨_, hu⟩
  · exact hP hp
  · exact hU hu

/-- The y-free part cannot vanish identically after substitution. -/
theorem sum_terms_ne_zero_of_all_second_zero (S : Finset (ℕ × ℕ))
    (hS : S.Nonempty) (hzero : ∀ t ∈ S, t.2 = 0) :
    (∑ t ∈ S, term t) ≠ 0 := by
  classical
  have hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact Prod.ext hab ((hzero a ha).trans (hzero b hb).symm)
  have hsum : (∑ t ∈ S, term t) = ∑ a ∈ S.image Prod.fst, U ^ a := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro t ht
    simp [term, hzero t ht]
  rw [hsum]
  exact sum_U_powers_ne_zero _ (hS.image _)

theorem sum_positive_terms_not_fixed (S : Finset (ℕ × ℕ))
    (hS : S.Nonempty) (hcard : S.card ≤ 2) (hpos : ∀ t ∈ S, 0 < t.2) :
    shift (∑ t ∈ S, term t) ≠ ∑ t ∈ S, term t := by
  classical
  have hc : S.card = 1 ∨ S.card = 2 := by
    have := Finset.card_pos.mpr hS
    omega
  rcases hc with hc | hc
  · obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hc
    simpa [term] using positive_term_not_fixed t.1 t.2 (hpos t (by simp))
  · obtain ⟨t, u, htu, rfl⟩ := Finset.card_eq_two.mp hc
    have ht := hpos t (by simp)
    have hu := hpos u (by simp)
    simpa [term, htu] using two_positive_terms_not_fixed t.1 u.1 t.2 u.2 ht hu
      (by simpa only [Prod.mk.eta] using htu)

/-- Any nonempty normalized set of at most four bivariate monomials
survives the parametrization. Normalization here needs only one term free
of y. This is the combinatorial heart of `distance(f₉) ≥ 5`. -/
theorem sum_terms_ne_zero_of_card_le_four (S : Finset (ℕ × ℕ))
    (hcard : S.card ≤ 4) (hfree : ∃ t ∈ S, t.2 = 0) :
    (∑ t ∈ S, term t) ≠ 0 := by
  classical
  let A := S.filter (fun t => t.2 = 0)
  let B := S.filter (fun t => t.2 ≠ 0)
  have hA : A.Nonempty := by
    obtain ⟨t, ht, he⟩ := hfree
    exact ⟨t, Finset.mem_filter.mpr ⟨ht, he⟩⟩
  have hsplit : (∑ t ∈ A, term t) + (∑ t ∈ B, term t) = ∑ t ∈ S, term t :=
    Finset.sum_filter_add_sum_filter_not S (fun t => t.2 = 0) term
  intro hz
  have hB : B.Nonempty := by
    by_contra hb
    have hb0 : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
    have hall : ∀ t ∈ S, t.2 = 0 := by
      intro t ht
      by_contra he
      have hm : t ∈ B := Finset.mem_filter.mpr ⟨ht, he⟩
      rw [hb0] at hm
      exact Finset.notMem_empty _ hm
    exact sum_terms_ne_zero_of_all_second_zero S
      (by obtain ⟨t, ht, _⟩ := hfree; exact ⟨t, ht⟩) hall hz
  have hpar : (A.card : ZMod 2) = 0 := by
    have hAval : Polynomial.eval 0 (∑ t ∈ A, term t) = (A.card : ZMod 2) := by
      rw [Polynomial.eval_finset_sum]
      calc
        (∑ t ∈ A, Polynomial.eval 0 (term t)) = ∑ _t ∈ A, (1 : ZMod 2) := by
          apply Finset.sum_congr rfl
          intro t ht
          have ht0 := (Finset.mem_filter.mp ht).2
          simp [term, U, V, ht0]
        _ = (A.card : ZMod 2) := by simp
    have hBval : Polynomial.eval 0 (∑ t ∈ B, term t) = 0 := by
      rw [Polynomial.eval_finset_sum]
      apply Finset.sum_eq_zero
      intro t ht
      have ht0 := (Finset.mem_filter.mp ht).2
      simp [term, U, V, ht0]
    have hev := congrArg (Polynomial.eval (0 : ZMod 2)) hz
    rw [← hsplit, Polynomial.eval_add, hAval, hBval, add_zero,
      Polynomial.eval_zero] at hev
    exact hev
  have htwo : 2 ≤ A.card := by
    obtain ⟨k, hk⟩ := ZMod.natCast_eq_zero_iff_even.mp hpar
    have hpos := Finset.card_pos.mpr hA
    omega
  have hcardAB : A.card + B.card = S.card := Finset.filter_card_add_filter_neg_card_eq_card _
  have hBcard : B.card ≤ 2 := by omega
  have hfixedA : shift (∑ t ∈ A, term t) = ∑ t ∈ A, term t := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have ht0 := (Finset.mem_filter.mp ht).2
    simp [term, ht0]
  have hBA : (∑ t ∈ B, term t) = ∑ t ∈ A, term t := by
    have hh := congrArg (fun P : R => P + ∑ t ∈ A, term t) (hsplit.trans hz)
    have hcancel : (∑ t ∈ A, term t) + (∑ t ∈ B, term t) + (∑ t ∈ A, term t) =
        ∑ t ∈ B, term t := by
      rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
    simpa only [hcancel, zero_add] using hh
  apply sum_positive_terms_not_fixed B hB hBcard
    (fun t ht => Nat.pos_of_ne_zero (Finset.mem_filter.mp ht).2)
  rw [hBA, hfixedA]

end Pilz.F9Param
