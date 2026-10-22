import Pilz.Basic
import Mathlib.Data.Finset.Max

/-!
# Minimality under deletion of terms

The first paragraph of Section `sec:cut`, before monomial normalization.
Deleting terms preserves every restriction expressible as a condition on
support monomials. No assertion about normalization is used here.
-/

noncomputable section

namespace Pilz

/-- Keep exactly the terms whose exponents lie in `S`. -/
def restrictTerms (P : Poly) (S : Finset (ℕ →₀ ℕ)) : Poly := by
  classical
  exact Finsupp.filter (fun d => d ∈ S) P

theorem support_restrictTerms (P : Poly) (S : Finset (ℕ →₀ ℕ)) :
    (restrictTerms P S).support = P.support ∩ S := by
  classical
  change (P.support.filter (fun d => d ∈ S)) = P.support ∩ S
  ext d
  simp

theorem support_restrictTerms_of_subset (P : Poly) (S : Finset (ℕ →₀ ℕ))
    (hS : S ⊆ P.support) : (restrictTerms P S).support = S := by
  rw [support_restrictTerms]
  exact Finset.inter_eq_right.mpr hS

theorem restrictTerms_support (P : Poly) : restrictTerms P P.support = P := by
  classical
  apply (Finsupp.filter_eq_self_iff _ _).mpr
  intro d hd
  exact Finsupp.mem_support_iff.mpr hd

theorem restrictTerms_restrictTerms (P : Poly) (S T : Finset (ℕ →₀ ℕ))
    (hTS : T ⊆ S) : restrictTerms (restrictTerms P S) T = restrictTerms P T := by
  classical
  apply MvPolynomial.ext
  intro d
  change (if d ∈ T then (if d ∈ S then MvPolynomial.coeff d P else 0) else 0) =
    (if d ∈ T then MvPolynomial.coeff d P else 0)
  by_cases hd : d ∈ T
  · simp [hd, hTS hd]
  · simp [hd]

/-- No nonempty proper deletion still violates the target at `n`. -/
def DeletionMinimal (n : ℕ) (D : Poly) : Prop :=
  ∀ T : Finset (ℕ →₀ ℕ), T ⊆ D.support → T.Nonempty → T ≠ D.support →
    n ≤ weight (interval n * restrictTerms D T)

/-- Every counterexample contains one minimal under deletion. This theorem
also records the support inclusion needed to preserve prime restrictions. -/
theorem exists_deletionMinimal (n : ℕ) (H : Poly)
    (hH : H ≠ 0) (hshort : weight (interval n * H) < n) :
    ∃ D : Poly, D ≠ 0 ∧ weight (interval n * D) < n ∧
      DeletionMinimal n D ∧ D.support ⊆ H.support := by
  classical
  let candidates := H.support.powerset.filter fun S =>
    S.Nonempty ∧ weight (interval n * restrictTerms H S) < n
  have hfull : H.support ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (fun _ hd => hd), ?_⟩
    refine ⟨MvPolynomial.support_nonempty.mpr hH, ?_⟩
    simpa [restrictTerms_support] using hshort
  obtain ⟨S, hS, hmin⟩ := candidates.exists_min_image Finset.card ⟨_, hfull⟩
  obtain ⟨hSpow, hSnonempty, hSshort⟩ := Finset.mem_filter.mp hS
  have hSsub : S ⊆ H.support := Finset.mem_powerset.mp hSpow
  have hsupp : (restrictTerms H S).support = S :=
    support_restrictTerms_of_subset H S hSsub
  refine ⟨restrictTerms H S, ?_, hSshort, ?_, ?_⟩
  · intro hz
    have hne : (restrictTerms H S).support.Nonempty := by rw [hsupp]; exact hSnonempty
    simpa [hz] using hne
  · intro T hT hTnonempty hTproper
    rw [hsupp] at hT hTproper
    by_contra hnot
    have hTshort : weight (interval n * restrictTerms H T) < n := by
      rw [← restrictTerms_restrictTerms H S T hT]
      omega
    have hTcand : T ∈ candidates := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (hT.trans hSsub), hTnonempty, hTshort⟩
    have hcard := hmin T hTcand
    have hlt : T.card < S.card := Finset.card_lt_card
      ⟨hT, fun hST => hTproper (Finset.Subset.antisymm hT hST)⟩
    omega
  · rw [hsupp]
    exact hSsub

end Pilz
