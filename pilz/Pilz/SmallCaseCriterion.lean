import Pilz.CoreBudget
import Pilz.Protection

/-! The common normal-form argument behind the paper's small-case tables. -/

noncomputable section

namespace Pilz

/-- A finite numerical row bounds the synchronized multiplier. A capacity
bound and a lower bound for those few-term products then exclude a short
multiple. The statement keeps each table input explicit. -/
theorem conjectureAt_of_core_capacity (n κ r T U M : ℕ) (S : FreshData)
    (hF : S.F = interval n) (hr : S.vars.card = r)
    (hκ : κ ≤ distance S.C) (hκpos : 2 ≤ κ)
    (hbound : ∀ m : ℕ, m < n → (Even n → Even m) → m ≤ T)
    (hreduce : ∀ m u : ℕ, 0 < u → r * u < m → 2 * u ≤ m → m ≤ T →
      u < κ ∧ (r * u + κ ≤ m → u ≤ U))
    (hcapacity : ∀ nf : NormalFormData S n, weight nf.D ≤ U →
      ∀ ε : ℕ → ℕ, classWeight (S.C * nf.D) ε ≤ M)
    (hprod : ∀ D : Poly, D ≠ 0 → weight D ≤ U → n ≤ weight (interval n * D))
    (hNM : 2 * M ≤ n) : ConjectureAt n := by
  intro H hH
  by_contra hnot
  have hshort : weight (interval n * H) < n := by omega
  have hex : ∃ G : Poly, ShortMultiple S.F n G := by
    refine ⟨S.F * H, mul_ne_zero S.prime_F.ne_zero hH, dvd_mul_right _ _, ?_⟩
    simpa only [hF] using hshort
  have hC : 2 ≤ weight S.C :=
    hκpos.trans (hκ.trans (distance_le_termWeight S.C))
  obtain ⟨nf⟩ := exists_normalForm S n hC hex
  have hm : weight nf.G < n := nf.extremal.1.2.2
  have hpar : Even n → Even (weight nf.G) := by
    intro hn
    obtain ⟨V, hV⟩ := nf.extremal.1.2.1
    have hp : Even (weight (S.F * V)) :=
      even_weight_mul (P := S.F) (by simpa [hF] using hn) V
    rwa [← hV] at hp
  have hmT := hbound (weight nf.G) hm hpar
  have hu : 0 < weight nf.D := weight_pos nf.D_ne_zero
  have hG₀ : 0 < weight nf.G₀ := weight_pos nf.G₀_ne_zero
  have hw := normalForm_weight S n nf
  rw [hr] at hw
  have hru : r * weight nf.D < weight nf.G := by omega
  obtain ⟨husmall, huU⟩ := hreduce (weight nf.G) (weight nf.D) hu hru nf.half hmT
  have hcore := normalForm_core_budget S n nf (husmall.trans_le hκ)
  rw [hr] at hcore
  have huU' : weight nf.D ≤ U := huU ((Nat.add_le_add_left hκ _).trans hcore)
  have hN : n ≤ weight S.C + S.vars.card := by
    rw [← S.weight_F, hF, weight_interval]
  have hproduct : n ≤ weight (S.F * nf.D) := by
    rw [hF]
    exact hprod nf.D nf.D_ne_zero huU'
  exact normalForm_excluded_of_twice_capacity S n nf hN M
    (hcapacity nf huU') hNM hproduct

end Pilz
