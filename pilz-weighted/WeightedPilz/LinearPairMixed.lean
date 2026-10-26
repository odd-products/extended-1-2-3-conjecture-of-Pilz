import WeightedPilz.MixedRowSurvival
import Mathlib.Tactic.FinCases

/-! The six rows of a square of a polynomial linear in two fresh variables. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

def pairGrade (z w : σ) : (σ →₀ ℕ) →+ (ℕ × ℕ) where
  toFun d := (d z, d w)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pairGrade_of_degree_zero (z w : σ) (P : MvPolynomial σ K)
    (hz : P.degreeOf z = 0) (hw : P.degreeOf w = 0) : PureGrade (pairGrade z w) 0 P := by
  intro d hd
  have hdz := monomial_le_degreeOf z hd
  have hdw := monomial_le_degreeOf w hd
  rw [hz] at hdz
  rw [hw] at hdw
  exact Prod.ext (Nat.eq_zero_of_le_zero hdz) (Nat.eq_zero_of_le_zero hdw)

def linearPairRows (z w : σ) (A L D : MvPolynomial σ K) : Fin 3 → MvPolynomial σ K :=
  ![A, L * X z, D * X w]

def squarePairRows (z w : σ) (A L D : MvPolynomial σ K) : Fin 6 → MvPolynomial σ K :=
  ![A ^ 2, C (2 : K) * (A * L) * X z, C (2 : K) * (A * D) * X w,
    L ^ 2 * X z ^ 2, C (2 : K) * (L * D) * X z * X w, D ^ 2 * X w ^ 2]

def linearPairGrades : Fin 3 → ℕ × ℕ := ![(0, 0), (1, 0), (0, 1)]
def squarePairGrades : Fin 6 → ℕ × ℕ := ![(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]

theorem linear_pair_mixed_power_weight (z w : σ) (hzw : z ≠ w)
    (A L D : MvPolynomial σ K)
    (hAz : A.degreeOf z = 0) (hAw : A.degreeOf w = 0)
    (hLz : L.degreeOf z = 0) (hLw : L.degreeOf w = 0)
    (hDz : D.degreeOf z = 0) (hDw : D.degreeOf w = 0)
    (h2 : (2 : K) ≠ 0)
    (hAA : 4 ≤ weight (A ^ 2)) (hAL : 4 ≤ weight (A * L))
    (hAD : 4 ≤ weight (A * D)) (hLL : 4 ≤ weight (L ^ 2))
    (hLD : 4 ≤ weight (L * D)) (hDD : 3 ≤ weight (D ^ 2))
    (p e r : ℕ) [ExpChar K p] (a b : σ →₀ ℕ) (u v : K) (hv : v ≠ 0) :
    11 ≤ weight (monomial a u * (A + L * X z + D * X w) ^ p ^ e +
      monomial b v * (A + L * X z + D * X w) ^ (2 * p ^ r)) := by
  let f := pairGrade z w
  have hA : PureGrade f 0 A := pairGrade_of_degree_zero z w A hAz hAw
  have hL : PureGrade f 0 L := pairGrade_of_degree_zero z w L hLz hLw
  have hD : PureGrade f 0 D := pairGrade_of_degree_zero z w D hDz hDw
  have hZ : PureGrade f (1, 0) (X z : MvPolynomial σ K) := by
    simpa [f, pairGrade, X, hzw, hzw.symm] using
      (PureGrade.monomial f (Finsupp.single z 1) (1 : K))
  have hW : PureGrade f (0, 1) (X w : MvPolynomial σ K) := by
    simpa [f, pairGrade, X, hzw, hzw.symm] using
      (PureGrade.monomial f (Finsupp.single w 1) (1 : K))
  have hTwo : PureGrade f 0 (C (2 : K)) := by
    simpa only [map_zero, C_apply] using (PureGrade.monomial f 0 (2 : K))
  have hU : A + L * X z + D * X w = ∑ i, linearPairRows z w A L D i := by
    simp [linearPairRows, Fin.sum_univ_succ]
    ring
  have hV : (A + L * X z + D * X w) ^ 2 = ∑ i, squarePairRows z w A L D i := by
    simp [squarePairRows, Fin.sum_univ_succ, map_ofNat]
    ring
  have hUg : ∀ i, PureGrade f (linearPairGrades i) (linearPairRows z w A L D i) := by
    intro i
    fin_cases i
    · simpa [linearPairGrades, linearPairRows] using hA
    · simpa [linearPairGrades, linearPairRows] using hL.mul hZ
    · simpa [linearPairGrades, linearPairRows] using hD.mul hW
  have hVg : ∀ i, PureGrade f (squarePairGrades i) (squarePairRows z w A L D i) := by
    intro i
    fin_cases i
    · simpa [squarePairGrades, squarePairRows] using hA.pow 2
    · simpa [squarePairGrades, squarePairRows] using (hTwo.mul (hA.mul hL)).mul hZ
    · simpa [squarePairGrades, squarePairRows] using (hTwo.mul (hA.mul hD)).mul hW
    · simpa [squarePairGrades, squarePairRows] using (hL.pow 2).mul (hZ.pow 2)
    · simpa [squarePairGrades, squarePairRows] using ((hTwo.mul (hL.mul hD)).mul hZ).mul hW
    · simpa [squarePairGrades, squarePairRows] using (hD.pow 2).mul (hW.pow 2)
  have hinj : Function.Injective squarePairGrades := by decide +kernel
  have hweights (i : Fin 6) : weight (squarePairRows z w A L D i) =
      ![weight (A ^ 2), weight (A * L), weight (A * D), weight (L ^ 2),
        weight (L * D), weight (D ^ 2)] i := by
    fin_cases i <;> simp [squarePairRows, X, monomial_pow, C_apply, -monomial_zero',
      weight_scalar_monomial_mul 0 h2]
  have hlow : ∀ i, 3 ≤ weight (squarePairRows z w A L D i) := by
    intro i
    rw [hweights]
    fin_cases i <;> dsimp <;> omega
  have hhigh : ∀ i, i ≠ (5 : Fin 6) → 4 ≤ weight (squarePairRows z w A L D i) := by
    intro i hi
    rw [hweights]
    fin_cases i <;> simp_all
  exact mixed_distinguished_weight_of_six_rows f (A + L * X z + D * X w)
    (linearPairRows z w A L D) (squarePairRows z w A L D)
    linearPairGrades squarePairGrades hU hV hUg hVg hinj 5 hlow hhigh p e r a b u v hv

end WeightedPilz
