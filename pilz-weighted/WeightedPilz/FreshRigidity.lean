import WeightedPilz.FreshCompletion

/-! The strict-threshold equality case for designated fresh variables. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

theorem sharp_completion_coordinate_rigidity (p : ℕ) [ExpChar K p]
    (A : MvPolynomial σ K) (z : σ) (hA : A ≠ 0)
    (hind : ∀ d ∈ A.support, d z = 0) (hmany : 2 ≤ weight A)
    (hminA : distance A = weight A)
    (G : MvPolynomial σ K) (hG : G ≠ 0) (hdvd : A + X z ∣ G)
    (hw : weight G = weight A + 1) :
    ∃ (e : ℕ) (d : σ →₀ ℕ) (c : K), c ≠ 0 ∧
      G = monomial d c * (A + X z) ^ p ^ e := by
  obtain ⟨A0, hrename, hF⟩ := independent_option_form A z hind
  let E := renameEquiv K (Equiv.optionSubtypeNe z).symm
  have hA0 : A0 ≠ 0 := by
    intro hz
    have hh : E A = 0 := by rw [hrename, hz, map_zero]
    exact hA (E.injective (by simpa using hh))
  have hwA := weight_renameEquiv (Equiv.optionSubtypeNe z).symm A
  rw [hrename, weight_rename_some] at hwA
  have hdA := distance_renameEquiv (Equiv.optionSubtypeNe z).symm A
  rw [hrename, distance_rename_of_injective some (Option.some_injective _)] at hdA
  have hEG : E G ≠ 0 := fun hz => hG (E.injective (by simpa using hz))
  have hEdvd : freshCompletion A0 ∣ E G := by
    obtain ⟨H, hH⟩ := hdvd
    refine ⟨E H, ?_⟩
    rw [hH, map_mul]
    exact congrArg (· * E H) hF
  have hEweight : weight (E G) = weight A0 + 1 := by
    rw [weight_renameEquiv, hwA, hw]
  obtain ⟨e, d, c, hc, hform⟩ := sharp_completion_one_rigidity p A0 hA0
    (by omega) (by omega) (E G) hEG hEdvd hEweight
  refine ⟨e, d.mapDomain (Equiv.optionSubtypeNe z), c, hc, ?_⟩
  have hmono : E.symm (monomial d c) =
      monomial (d.mapDomain (Equiv.optionSubtypeNe z)) c := by
    change rename (Equiv.optionSubtypeNe z) (monomial d c) = _
    exact rename_monomial _ _ _
  have hback : E.symm (freshCompletion A0) = A + X z := by
    rw [← hF]
    exact E.symm_apply_apply _
  have hh := congrArg E.symm hform
  simpa only [map_mul, map_pow, E.symm_apply_apply, hmono, hback] using hh

theorem sharp_completion_finset_rigidity (p : ℕ) [ExpChar K p]
    (V : Finset σ) (C : MvPolynomial σ K) (hC : C ≠ 0)
    (hind : ∀ z ∈ V, ∀ d ∈ C.support, d z = 0)
    (hr : weight C - distance C < V.card) (hsize : 3 ≤ weight C + V.card)
    (G : MvPolynomial σ K) (hG : G ≠ 0)
    (hdvd : (C + ∑ z ∈ V, X z) ∣ G)
    (hmin : weight G = distance (C + ∑ z ∈ V, (X z : MvPolynomial σ K))) :
    ∃ (e : ℕ) (d : σ →₀ ℕ) (c : K), c ≠ 0 ∧
      G = monomial d c * (C + ∑ z ∈ V, X z) ^ p ^ e := by
  have hV : V.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z, hz⟩ := hV
  let W := V.erase z
  let A : MvPolynomial σ K := C + ∑ i ∈ W, X i
  have hzW : z ∉ W := Finset.notMem_erase z V
  have hW : ∀ q ∈ W, ∀ d ∈ C.support, d q = 0 :=
    fun q hq => hind q (Finset.mem_of_mem_erase hq)
  have hcard : V.card = W.card + 1 := by
    simpa [W] using (Finset.card_erase_add_one hz).symm
  have hwtA : weight A = weight C + W.card := weight_add_sum_variables W C hW
  have hδ : distance A = weight A := by
    have hlo := sharp_completion_finset W C hC hW
    have hhi := distance_le_weight A
    have hle := distance_le_weight C
    change min (weight C + W.card) (distance C + 2 * W.card) ≤ distance A at hlo
    rw [hwtA] at hhi ⊢
    omega
  have hA : A ≠ 0 := by
    intro heq
    have hpos := distance_pos hC
    have hle := distance_le_weight C
    have hzwt : weight A = 0 := by rw [heq]; rfl
    omega
  have hAind : ∀ d ∈ A.support, d z = 0 :=
    independent_sum_variables C W z (hind z hz) hzW
  have hmany : 2 ≤ weight A := by omega
  have heq : C + ∑ i ∈ V, (X i : MvPolynomial σ K) = A + X z := by
    have hi : insert z W = V := Finset.insert_erase hz
    rw [← hi, Finset.sum_insert hzW]
    dsimp [A]
    ac_rfl
  have hdist : distance (A + X z) = weight A + 1 := by
    have hlo := sharp_completion_coordinate A z hA hAind
    have hhi := distance_le_weight (A + X z)
    rw [weight_add_independent_variable A z hAind] at hhi
    rw [hδ] at hlo
    omega
  have hweight : weight G = weight A + 1 := by rw [hmin, heq, hdist]
  rw [heq] at hdvd ⊢
  exact sharp_completion_coordinate_rigidity p A z hA hAind hmany hδ G hG hdvd hweight

namespace FreshData

theorem sharp_completion_rigidity (p : ℕ) [ExpChar K p] (S : FreshData σ K)
    (hr : weight S.C - distance S.C < S.vars.card)
    (hsize : 3 ≤ weight S.C + S.vars.card)
    (G : MvPolynomial σ K) (hG : G ≠ 0) (hdvd : S.F ∣ G)
    (hmin : weight G = distance S.F) :
    ∃ (e : ℕ) (d : σ →₀ ℕ) (c : K), c ≠ 0 ∧ G = monomial d c * S.F ^ p ^ e :=
  sharp_completion_finset_rigidity p S.vars S.C S.C_ne_zero S.independent
    hr hsize G hG hdvd hmin

end FreshData
end WeightedPilz
