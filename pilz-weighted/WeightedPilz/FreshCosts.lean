import WeightedPilz.FreshResidueSectors
import WeightedPilz.Frobenius
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.Data.Sym.Card

/-! Exact costs of aggregate fresh degrees below the characteristic. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

private theorem card_finset_sym (V : Finset σ) (j : ℕ) :
    (V.sym j).card = (V.card + j - 1).choose j := by
  classical
  have himage : (Finset.univ : Finset (Sym ↥V j)).image (Sym.map Subtype.val) = V.sym j := by
    ext m
    constructor
    · rintro hm
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hm
      apply Finset.mem_sym_iff.mpr
      intro z hz
      obtain ⟨a, _, rfl⟩ := Sym.mem_map.mp hz
      exact a.property
    · intro hm
      let s : Sym ↥V j := m.attach.map (fun a => ⟨a.val, Finset.mem_sym_iff.mp hm a.val a.property⟩)
      refine Finset.mem_image.mpr ⟨s, Finset.mem_univ _, ?_⟩
      simpa only [s, Sym.map_map, Function.comp_def] using m.attach_map_coe
  rw [← himage, Finset.card_image_of_injective _ (Sym.map_injective Subtype.val_injective j)]
  simpa using (Sym.card_sym_eq_choose (α := ↥V) j)

private theorem multiset_prod_X (m : Multiset σ) :
    (m.map (fun z => (X z : MvPolynomial σ K))).prod = monomial m.toFinsupp 1 := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.toFinsupp_zero]
    rfl
  | cons z m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, MvPolynomial.X, monomial_mul, one_mul]
    have hexp : Finsupp.single z 1 + m.toFinsupp = (z ::ₘ m).toFinsupp := by
      ext a
      simp [Finsupp.single_apply, Multiset.count_cons, eq_comm, add_comm]
    rw [hexp]

private theorem multinomial_cast_ne_zero (m : Multiset σ)
    (hfac : (m.card.factorial : K) ≠ 0) : (m.multinomial : K) ≠ 0 := by
  have hs : (∏ z ∈ m.toFinsupp.support, (m.toFinsupp z).factorial) *
      m.multinomial = m.card.factorial := by
    have hsum : (∑ z ∈ m.toFinsupp.support, m.toFinsupp z) = m.card :=
      Multiset.toFinsupp_sum_eq m
    simpa only [Multiset.multinomial, Finsupp.multinomial_eq, hsum] using
      Nat.multinomial_spec m.toFinsupp.support m.toFinsupp
  intro hzero
  have hc := congrArg (fun n : ℕ => (n : K)) hs
  dsimp only at hc
  rw [Nat.cast_mul, hzero, mul_zero] at hc
  exact hfac hc.symm

private theorem sum_variables_pow (V : Finset σ) (j : ℕ) :
    (∑ z ∈ V, (X z : MvPolynomial σ K)) ^ j =
      ∑ m ∈ V.sym j, monomial m.val.toFinsupp (m.val.multinomial : K) := by
  rw [Finset.sum_pow]
  apply Finset.sum_congr rfl
  intro m hm
  rw [multiset_prod_X]
  change C (m.val.multinomial : K) * monomial m.val.toFinsupp 1 = _
  rw [C_mul_monomial, mul_one]

private theorem sym_exponent_injective (j : ℕ) :
    Function.Injective (fun m : Sym σ j => m.val.toFinsupp) := by
  intro m n h
  exact Subtype.ext (Multiset.toFinsupp.injective h)

/-- When `j!` is nonzero, every monomial of total degree `j` survives. -/
theorem weight_sum_variables_pow_of_factorial_ne_zero (V : Finset σ) (j : ℕ)
    (hfac : (j.factorial : K) ≠ 0) :
    weight ((∑ z ∈ V, (X z : MvPolynomial σ K)) ^ j) =
      (V.card + j - 1).choose j := by
  classical
  rw [sum_variables_pow, weight_sum_of_pairwise_disjoint]
  · have hcoeff (m : Sym σ j) : (m.val.multinomial : K) ≠ 0 :=
      multinomial_cast_ne_zero m.val (by simpa only [m.property] using hfac)
    simp only [weight, support_monomial, if_neg (hcoeff _), Finset.card_singleton,
      Finset.sum_const, smul_eq_mul, mul_one]
    exact card_finset_sym V j
  · intro m hm n hn hmn
    rw [support_monomial, support_monomial]
    split_ifs <;> simp only [Finset.disjoint_empty_left, Finset.disjoint_empty_right,
      Finset.disjoint_singleton_left, Finset.mem_singleton]
    exact fun heq => hmn (sym_exponent_injective j heq)

namespace FreshData

/-- Residue-separated monomial translates give an exact aggregate row cost. -/
theorem weight_freshSum_pow_mul_of_factorial_ne_zero (S : FreshData σ K)
    (q j : ℕ) (A : MvPolynomial σ K) (hj : j < q)
    (hfac : (j.factorial : K) ≠ 0) (hA : S.PowersInFresh q A) :
    weight (S.freshSum ^ j * A) = (S.vars.card + j - 1).choose j * weight A := by
  classical
  have hcoeff (m : Sym σ j) : (m.val.multinomial : K) ≠ 0 :=
    multinomial_cast_ne_zero m.val (by simpa only [m.property] using hfac)
  have hsupport (m : Sym σ j) :
      (monomial m.val.toFinsupp (m.val.multinomial : K) * A).support =
        A.support.map (addLeftEmbedding m.val.toFinsupp) :=
    AddMonoidAlgebra.support_single_mul A (m.val.multinomial : K)
      (by intro y; exact mul_eq_zero.trans (or_iff_right (hcoeff m))) _
  rw [freshSum, sum_variables_pow, Finset.sum_mul, weight_sum_of_pairwise_disjoint]
  · simp only [weight_scalar_monomial_mul _ (hcoeff _), Finset.sum_const, smul_eq_mul]
    rw [card_finset_sym]
  · intro m hm n hn hmn
    rw [hsupport m, hsupport n]
    apply Finset.disjoint_left.mpr
    intro d hdm hdn
    obtain ⟨e, he, hed⟩ := Finset.mem_map.mp hdm
    obtain ⟨f, hf, hfd⟩ := Finset.mem_map.mp hdn
    have hef : m.val.toFinsupp + e = n.val.toFinsupp + f := hed.trans hfd.symm
    apply hmn
    apply sym_exponent_injective j
    ext z
    by_cases hz : z ∈ S.vars
    · have hmz : m.val.count z < q :=
        lt_of_le_of_lt (Multiset.count_le_card z m.val) (m.property.symm ▸ hj)
      have hnz : n.val.count z < q :=
        lt_of_le_of_lt (Multiset.count_le_card z n.val) (n.property.symm ▸ hj)
      have hmod := congrArg (fun a : σ →₀ ℕ => a z % q) hef
      simpa only [Finsupp.add_apply, Nat.add_mod,
        Nat.mod_eq_zero_of_dvd (hA z hz e he), Nat.mod_eq_zero_of_dvd (hA z hz f hf),
        add_zero, Nat.mod_mod, Multiset.toFinsupp_apply,
        Nat.mod_eq_of_lt hmz, Nat.mod_eq_of_lt hnz] using hmod
    · have hmz : z ∉ m.val := fun h => hz (Finset.mem_sym_iff.mp hm z h)
      have hnz : z ∉ n.val := fun h => hz (Finset.mem_sym_iff.mp hn z h)
      simp only [Multiset.toFinsupp_apply, Multiset.count_eq_zero_of_notMem hmz,
        Multiset.count_eq_zero_of_notMem hnz]

/-- The exact degree cost for every residue row below the characteristic. -/
theorem weight_freshSum_pow_mul_lt_char (S : FreshData σ K) (p j : ℕ)
    [Fact p.Prime] [CharP K p] (A : MvPolynomial σ K)
    (hj : j < p) (hA : S.PowersInFresh p A) :
    weight (S.freshSum ^ j * A) = (S.vars.card + j - 1).choose j * weight A := by
  exact S.weight_freshSum_pow_mul_of_factorial_ne_zero p j A hj
    (((IsUnit.natCast_factorial_iff_of_charP (A := K) p).mpr hj).ne_zero) hA

/-- Every aggregate row below the characteristic contributes its exact expanded cost. -/
theorem weight_aggregate_rows_lt_char (S : FreshData σ K) (p : ℕ)
    [Fact p.Prime] [CharP K p] (A : ℕ → MvPolynomial σ K)
    (hA : ∀ j < p, S.PowersInFresh p (A j)) :
    weight (∑ j ∈ Finset.range p, S.freshSum ^ j * A j) =
      ∑ j ∈ Finset.range p, (S.vars.card + j - 1).choose j * weight (A j) := by
  rw [S.aggregate_rows_weight p A hA]
  apply Finset.sum_congr rfl
  intro j hj
  exact S.weight_freshSum_pow_mul_lt_char p j (A j)
    (Finset.mem_range.mp hj) (hA j (Finset.mem_range.mp hj))

/-- Fresh aggregate degree has the usual stars-and-bars cost in characteristic zero. -/
theorem weight_freshSum_pow_charZero [CharZero K] (S : FreshData σ K) (j : ℕ) :
    weight (S.freshSum ^ j) = (S.vars.card + j - 1).choose j := by
  apply weight_sum_variables_pow_of_factorial_ne_zero
  exact_mod_cast Nat.factorial_ne_zero j

/-- Below the characteristic, the fresh aggregate degree has its ordinary multinomial cost. -/
theorem weight_freshSum_pow_lt_char (S : FreshData σ K) (p j : ℕ)
    [Fact p.Prime] [CharP K p] (hj : j < p) :
    weight (S.freshSum ^ j) = (S.vars.card + j - 1).choose j := by
  apply weight_sum_variables_pow_of_factorial_ne_zero
  exact ((IsUnit.natCast_factorial_iff_of_charP (A := K) p).mpr hj).ne_zero

/-- Every characteristic-power polynomial has coordinate exponents divisible by that characteristic. -/
theorem powersInFresh_pow_char (S : FreshData σ K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (A : MvPolynomial σ K) : S.PowersInFresh p (A ^ p) := by
  classical
  intro z hz d hd
  have hs := support_pow_expChar p 1 A
  simp only [pow_one] at hs
  rw [hs] at hd
  simp only [Finset.mem_image] at hd
  obtain ⟨e, he, rfl⟩ := hd
  simp only [scaleExponent_apply]
  exact dvd_mul_right p (e z)

/-- The complete characteristic-`p` digit-product formula for aggregate fresh powers. -/
theorem weight_freshSum_pow_digits (S : FreshData σ K) (p : ℕ)
    [Fact p.Prime] [CharP K p] (d : ℕ) :
    weight (S.freshSum ^ d) =
      ((Nat.digits p d).map (fun j => (S.vars.card + j - 1).choose j)).prod := by
  classical
  have hp : Nat.Prime p := Fact.out
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d = 0
    · simp only [hd, pow_zero, Nat.digits_zero, List.map_nil, List.prod_nil, weight,
        MvPolynomial.one_def, MvPolynomial.support_monomial, if_neg one_ne_zero,
        Finset.card_singleton]
    have hq : d / p < d := Nat.div_lt_self (Nat.pos_of_ne_zero hd) hp.one_lt
    have hpow : S.freshSum ^ d =
        S.freshSum ^ (d % p) * (S.freshSum ^ (d / p)) ^ p := by
      rw [← pow_mul, ← pow_add]
      congr 1
      simpa only [Nat.mul_comm] using (Nat.mod_add_div d p).symm
    rw [hpow, S.weight_freshSum_pow_mul_lt_char p (d % p) _
      (Nat.mod_lt _ hp.pos) (S.powersInFresh_pow_char p _)]
    have hw : weight ((S.freshSum ^ (d / p)) ^ p) = weight (S.freshSum ^ (d / p)) := by
      simpa only [pow_one] using weight_pow_expChar p 1 (S.freshSum ^ (d / p))
    rw [hw, ih (d / p) hq, Nat.digits_eq_cons_digits_div hp.one_lt hd]
    rfl

end FreshData
end WeightedPilz
