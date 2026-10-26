import WeightedPilz.ThreeRowShape
import WeightedPilz.InitialTenBase
import WeightedPilz.LinearExtensionOps

/-! Endpoint costs and the exact seven-term shape for a linear extension. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K]

theorem linearExtension_multiple_endpoint_costs (R D : MvPolynomial σ K)
    (hR : R ≠ 0) (hD : D ≠ 0) (G : MvPolynomial (Option σ) K)
    (hG : G ≠ 0) (hdiv : linearExtension R D ∣ G) :
    distance R ≤ weight (optionEquivLeft K σ G).trailingCoeff ∧
    distance D ≤ weight (optionEquivLeft K σ G).leadingCoeff ∧
    (optionEquivLeft K σ G).natTrailingDegree < (optionEquivLeft K σ G).natDegree := by
  obtain ⟨H, rfl⟩ := hdiv
  let E := optionEquivLeft K σ
  let Q := E (linearExtension R D)
  let V := E H
  have hH : H ≠ 0 := fun hz => hG (by simp [hz])
  have hV : V ≠ 0 := by
    intro hz
    exact hH (E.injective (hz.trans (map_zero E).symm))
  have hQdeg : Q.natDegree = 1 := by
    simpa only [Q, E, optionEquiv_linearExtension, add_comm] using
      Polynomial.natDegree_linear hD (b := R)
  have hQlc : Q.leadingCoeff = D := by
    simpa only [Q, E, optionEquiv_linearExtension, add_comm] using
      Polynomial.leadingCoeff_linear hD (b := R)
  have hQt : Q.natTrailingDegree = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero.mpr
    right
    simpa [Q, E, optionEquiv_linearExtension] using hR
  have hQtc : Q.trailingCoeff = R := by
    rw [Polynomial.trailingCoeff, hQt]
    simp [Q, E, optionEquiv_linearExtension]
  have hQ : Q ≠ 0 := by intro hz; simp [hz] at hQdeg
  have hmap : E (linearExtension R D * H) = Q * V := map_mul E _ _
  change distance R ≤ weight (E (linearExtension R D * H)).trailingCoeff ∧
    distance D ≤ weight (E (linearExtension R D * H)).leadingCoeff ∧ _
  rw [hmap, Polynomial.trailingCoeff_mul, Polynomial.leadingCoeff_mul, hQtc, hQlc]
  refine ⟨distance_le_weight_mul R V.trailingCoeff (mt Polynomial.trailingCoeff_eq_zero.mp hV),
    distance_le_weight_mul D V.leadingCoeff (mt Polynomial.leadingCoeff_eq_zero.mp hV), ?_⟩
  change (Q * V).natTrailingDegree < (Q * V).natDegree
  rw [Polynomial.natTrailingDegree_mul hQ hV, Polynomial.natDegree_mul hQ hV, hQt, hQdeg]
  have h := Polynomial.natTrailingDegree_le_natDegree V
  omega

theorem linearExtension_small_multiple_shape (R D : MvPolynomial σ K)
    (hR : R ≠ 0) (hD : D ≠ 0) (hRd : 4 ≤ distance R) (hDd : 2 ≤ distance D)
    (G : MvPolynomial (Option σ) K) (hG : G ≠ 0)
    (hdiv : linearExtension R D ∣ G)
    (hrows : 3 ≤ (optionEquivLeft K σ G).support.card) (hw : weight G ≤ 7) :
    ∃ mid : ℕ, mid ≠ (optionEquivLeft K σ G).natTrailingDegree ∧
      mid ≠ (optionEquivLeft K σ G).natDegree ∧
      (optionEquivLeft K σ G).support =
        {(optionEquivLeft K σ G).natTrailingDegree, mid, (optionEquivLeft K σ G).natDegree} ∧
      weight (optionEquivLeft K σ G).trailingCoeff = 4 ∧
      weight ((optionEquivLeft K σ G).coeff mid) = 1 ∧
      weight (optionEquivLeft K σ G).leadingCoeff = 2 := by
  obtain ⟨hlo, hhi, hlt⟩ := linearExtension_multiple_endpoint_costs R D hR hD G hG hdiv
  exact three_row_shape_four_one_two G _ _ hlt.ne (hRd.trans hlo) (hDd.trans hhi) hrows hw

end WeightedPilz
