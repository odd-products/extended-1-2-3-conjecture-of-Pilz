import WeightedPilz.BinaryOddCoefficients
import WeightedPilz.BinarySmoothRows

/-! Support certificates for repeated three-row distance estimates. Every
certificate applies to arbitrary nonzero coefficients on its support. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def SupportDistanceBound (K : Type*) [Field K]
    (S : Finset (ℕ →₀ ℕ)) (N : ℕ) : Prop :=
  ∀ P : Poly K, P.support = S → N ≤ distance P

theorem supportDistanceBound_one (S : Finset (ℕ →₀ ℕ)) (hS : S.Nonempty) :
    SupportDistanceBound K S 1 := by
  intro P hP
  exact distance_pos (support_nonempty.mp (hP.symm ▸ hS))

theorem supportDistanceBound_two (S : Finset (ℕ →₀ ℕ)) (hS : 2 ≤ S.card) :
    SupportDistanceBound K S 2 := by
  intro P hP
  apply nonmonomial_distance_two P
  simpa only [weight, hP] using hS

theorem supportDistanceBound_three_rows [CharP K 2]
    (S : Finset (ℕ →₀ ℕ)) (p m l h : ℕ)
    (hc : Arithmetic.ThreeRowsSupport S p m)
    (hl : SupportDistanceBound K (Arithmetic.rowSupport p 0 S) l)
    (hh : SupportDistanceBound K (Arithmetic.rowSupport p m S) h) :
    SupportDistanceBound K S (l + h + 1) := by
  intro P hP
  let Q := coordinateEquiv p P
  have hrow (k : ℕ) : (coordinateRow p k P).support = Arithmetic.rowSupport p k S := by
    rw [support_coordinateRow, hP]
    rfl
  have hne (k : ℕ) (hk : (Arithmetic.rowSupport p k S).Nonempty) : Q.coeff k ≠ 0 := by
    have hne' : coordinateRow p k P ≠ 0 := support_nonempty.mp ((hrow k).symm ▸ hk)
    intro hz
    apply hne'
    change rename Subtype.val (Q.coeff k) = 0
    rw [hz, map_zero]
  have hdeg : Q.natDegree = m := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · rw [show Q = coordinateEquiv p P from rfl, natDegree_coordinateEquiv]
      apply degreeOf_le_iff.mpr
      intro d hd
      exact hc.degree_bound d (hP ▸ hd)
    · exact hne m hc.top_nonempty
  have hobs : ∀ a : K, a ≠ 0 →
      Q.coeff (Q.natDegree - 2) * Q.leadingCoeff ≠
        C a * Q.coeff (Q.natDegree - 1) ^ 2 := by
    intro c _ heq
    obtain ⟨a, ha, b, hb, j, hodd, huniq⟩ := hc.odd_unique
    have ha' : a ∈ (coordinateRow p (m - 2) P).support := by rwa [hrow]
    have hb' : b ∈ (coordinateRow p m P).support := by rwa [hrow]
    have hu' : ∀ u ∈ (coordinateRow p (m - 2) P).support,
        ∀ v ∈ (coordinateRow p m P).support, u + v = a + b → u = a ∧ v = b := by
      simpa only [hrow] using huniq
    apply mul_ne_scalar_square_of_unique_odd_sum
      (coordinateRow p (m - 2) P) (coordinateRow p m P)
      (coordinateRow p (m - 1) P) a b ha' hb' hu' j hodd c
    have hm := congrArg
      (rename (Subtype.val : {q : ℕ // q ≠ p} → ℕ)) heq
    simpa only [coordinateRow, Q, Polynomial.leadingCoeff, hdeg,
      map_mul, map_pow, rename_C] using hm
  have hend := top_three_endpoint_distance p P
    (show 2 ≤ Q.natDegree by rw [hdeg]; exact hc.degree_ge_two)
    (hne 0 hc.bottom_nonempty)
    (by change Q.coeff (Q.natDegree - 2) ≠ 0; rw [hdeg]; exact hne _ hc.lower_nonempty)
    (by change Q.coeff (Q.natDegree - 1) ≠ 0; rw [hdeg]; exact hne _ hc.middle_nonempty)
    hobs
  change distance (Q.coeff 0) + distance (Q.coeff Q.natDegree) + 1 ≤ distance P at hend
  rw [hdeg] at hend
  have hlo := hl (coordinateRow p 0 P) (hrow 0)
  have hhi := hh (coordinateRow p m P) (hrow m)
  rw [distance_coordinateRow] at hlo hhi
  change l ≤ distance (Q.coeff 0) at hlo
  change h ≤ distance (Q.coeff m) at hhi
  omega

end WeightedPilz
