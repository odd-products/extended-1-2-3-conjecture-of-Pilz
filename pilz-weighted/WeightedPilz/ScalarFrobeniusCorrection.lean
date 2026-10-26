import WeightedPilz.AggregateAlgebra
import WeightedPilz.FreshResidueTheorem
import WeightedPilz.AggregateResidueGrouping
import Mathlib.Algebra.Ring.GeomSum

/-! The correction quotient is itself scalar in the characteristic power of the fresh sum. -/
noncomputable section
namespace WeightedPilz.FreshData
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

/-- The explicit base-only coefficients of the geometric correction quotient. -/
def scalarCorrectionCoefficient (S : FreshData σ K) (p : ℕ)
    (B : ℕ → MvPolynomial σ K) (n i : ℕ) : MvPolynomial σ K :=
  (-S.C) ^ (n % p) * B n * ((-S.C) ^ p) ^ (n / p - 1 - i)

/-- A finite scalar expression in `Z^p`, with no coefficient roots. -/
def scalarCorrectionQuotient (S : FreshData σ K) (p : ℕ)
    (t : Finset ℕ) (B : ℕ → MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ n ∈ t, ∑ i ∈ Finset.range (n / p),
    (S.freshSum ^ p) ^ i * S.scalarCorrectionCoefficient p B n i

/-- The same quotient before aggregate evaluation. -/
def scalarCorrectionPolynomial (S : FreshData σ K) (p : ℕ)
    (t : Finset ℕ) (B : ℕ → MvPolynomial σ K) : Polynomial (MvPolynomial σ K) :=
  ∑ n ∈ t, ∑ i ∈ Finset.range (n / p),
    Polynomial.monomial i (S.scalarCorrectionCoefficient p B n i)

private theorem baseOnly_pow {S : FreshData σ K} {P : MvPolynomial σ K}
    (hP : S.BaseOnly P) (n : ℕ) : S.BaseOnly (P ^ n) := by
  intro z hz d hd
  exact support_pow_zero_at z P (hP z hz) n d hd

private theorem baseOnly_sum {ι : Type*} {S : FreshData σ K} (t : Finset ι)
    (B : ι → MvPolynomial σ K) (hB : ∀ n ∈ t, S.BaseOnly (B n)) :
    S.BaseOnly (∑ n ∈ t, B n) := by
  intro z hz d hd
  obtain ⟨n, hn, hdn⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  exact hB n hn z hz d hdn

private theorem baseOnly_zero (S : FreshData σ K) : S.BaseOnly 0 := by
  intro z hz d hd
  simpa using hd

theorem scalarCorrectionCoefficient_baseOnly (S : FreshData σ K) (p : ℕ)
    (B : ℕ → MvPolynomial σ K) {n : ℕ} (hB : S.BaseOnly (B n)) (i : ℕ) :
    S.BaseOnly (S.scalarCorrectionCoefficient p B n i) := by
  have hC : S.BaseOnly (-S.C) := (show S.BaseOnly S.C from S.independent).neg
  exact ((baseOnly_pow hC (n % p)).mul hB).mul
    (baseOnly_pow (baseOnly_pow hC p) (n / p - 1 - i))

theorem scalarCorrectionPolynomial_baseOnly (S : FreshData σ K) (p : ℕ)
    (t : Finset ℕ) (B : ℕ → MvPolynomial σ K) (hB : ∀ n ∈ t, S.BaseOnly (B n))
    (k : ℕ) : S.BaseOnly ((S.scalarCorrectionPolynomial p t B).coeff k) := by
  classical
  simp only [scalarCorrectionPolynomial, Polynomial.finset_sum_coeff]
  apply baseOnly_sum
  intro n hn
  apply baseOnly_sum
  intro i hi
  rw [Polynomial.coeff_monomial]
  split_ifs
  · exact S.scalarCorrectionCoefficient_baseOnly p B (hB n hn) i
  · exact S.baseOnly_zero

theorem scalarCorrectionPolynomial_eval (S : FreshData σ K) (p : ℕ)
    (t : Finset ℕ) (B : ℕ → MvPolynomial σ K) :
    Polynomial.eval (S.freshSum ^ p) (S.scalarCorrectionPolynomial p t B) =
      S.scalarCorrectionQuotient p t B := by
  simp only [scalarCorrectionPolynomial, Polynomial.eval_finset_sum, scalarCorrectionQuotient]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.eval_monomial, mul_comm]

/-- The finite grouped correction equals its ungrouped scalar expression. -/
theorem correction_aggregateResidueRow_eq (S : FreshData σ K) (p : ℕ) (hp : 0 < p)
    (t : Finset ℕ) (B : ℕ → MvPolynomial σ K) :
    S.correction p (S.aggregateResidueRow p t B) =
      ∑ n ∈ t, (-S.C) ^ (n % p) * B n * (S.freshSum ^ p) ^ (n / p) := by
  classical
  unfold correction
  calc
    (∑ j ∈ Finset.range p, (-S.C) ^ j * S.aggregateResidueRow p t B j) =
        ∑ j ∈ Finset.range p, ∑ n ∈ t.filter (fun n => n % p = j),
          (-S.C) ^ (n % p) * B n * (S.freshSum ^ p) ^ (n / p) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [aggregateResidueRow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [(Finset.mem_filter.mp hn).2, pow_mul]
      ring
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hp)) _

/-- A geometric sum supplies an explicit scalar quotient from the core relation. -/
theorem scalar_correction_factorization_of_relation (S : FreshData σ K) (p : ℕ)
    [ExpChar K p] (t : Finset ℕ) (B : ℕ → MvPolynomial σ K)
    (hrel : (∑ n ∈ t, (-S.C) ^ n * B n) = 0) :
    S.correction p (S.aggregateResidueRow p t B) =
      S.F ^ p * S.scalarCorrectionQuotient p t B := by
  letI : ExpChar (MvPolynomial σ K) p :=
    expChar_of_injective_ringHom (MvPolynomial.C_injective (σ := σ) (R := K)) p
  have hfactor : S.F ^ p = S.freshSum ^ p - (-S.C) ^ p := by
    rw [← sub_pow_expChar]
    congr 1
    simp only [F, sub_neg_eq_add, add_comm]
  have hcore (n : ℕ) :
      (-S.C) ^ (n % p) * B n * ((-S.C) ^ p) ^ (n / p) = (-S.C) ^ n * B n := by
    rw [← pow_mul, mul_right_comm, ← pow_add, Nat.mod_add_div]
  have hsum : (∑ n ∈ t, (-S.C) ^ (n % p) * B n * ((-S.C) ^ p) ^ (n / p)) = 0 := by
    simpa only [hcore] using hrel
  have hgeom (n : ℕ) :
      (S.freshSum ^ p - (-S.C) ^ p) *
        (∑ i ∈ Finset.range (n / p), (S.freshSum ^ p) ^ i *
          S.scalarCorrectionCoefficient p B n i) =
      ((-S.C) ^ (n % p) * B n) *
        ((S.freshSum ^ p) ^ (n / p) - ((-S.C) ^ p) ^ (n / p)) := by
    have hsum' : (∑ i ∈ Finset.range (n / p), (S.freshSum ^ p) ^ i *
        S.scalarCorrectionCoefficient p B n i) =
        ((-S.C) ^ (n % p) * B n) *
          (∑ i ∈ Finset.range (n / p), (S.freshSum ^ p) ^ i *
            ((-S.C) ^ p) ^ (n / p - 1 - i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [scalarCorrectionCoefficient]
      ring
    rw [hsum', mul_left_comm, (Commute.all (S.freshSum ^ p) ((-S.C) ^ p)).mul_geom_sum₂]
  symm
  rw [hfactor, scalarCorrectionQuotient, Finset.mul_sum]
  calc
    (∑ n ∈ t, (S.freshSum ^ p - (-S.C) ^ p) *
        (∑ i ∈ Finset.range (n / p), (S.freshSum ^ p) ^ i *
          S.scalarCorrectionCoefficient p B n i)) =
      ∑ n ∈ t, ((-S.C) ^ (n % p) * B n) *
        ((S.freshSum ^ p) ^ (n / p) - ((-S.C) ^ p) ^ (n / p)) := by
      exact Finset.sum_congr rfl (fun n hn => hgeom n)
    _ = _ := by
      rw [Finset.sum_congr rfl (fun n hn => mul_sub _ _ _), Finset.sum_sub_distrib,
        hsum, sub_zero, S.correction_aggregateResidueRow_eq p (expChar_pos K p) t B]

/-- The stronger residue-correction statement: the quotient has base-only coefficients in `Z^p`. -/
theorem exists_scalar_correction_quotient (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (t : Finset ℕ) (B : ℕ → MvPolynomial σ K) (hB : ∀ n ∈ t, S.BaseOnly (B n))
    (hdiv : S.F ∣ ∑ n ∈ t, S.freshSum ^ n * B n) :
    ∃ Q : Polynomial (MvPolynomial σ K),
      (∀ k : ℕ, S.BaseOnly (Q.coeff k)) ∧
      S.correction p (S.aggregateResidueRow p t B) =
        S.F ^ p * Polynomial.eval (S.freshSum ^ p) Q := by
  refine ⟨S.scalarCorrectionPolynomial p t B, S.scalarCorrectionPolynomial_baseOnly p t B hB, ?_⟩
  rw [S.scalarCorrectionPolynomial_eval]
  exact S.scalar_correction_factorization_of_relation p t B (S.aggregate_relation_of_dvd t B hB hdiv)

end WeightedPilz.FreshData
