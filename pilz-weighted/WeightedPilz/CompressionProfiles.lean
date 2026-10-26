import WeightedPilz.Fresh
import WeightedPilz.Width
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max

/-! The genuinely finite profile maximization in `thm:compression`. -/
noncomputable section
namespace WeightedPilz.Compression
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

def baseExponent (V : Finset σ) (e : σ →₀ ℕ) : σ →₀ ℕ :=
  e.filter (fun i => i ∉ V)

def freshDegree (V : Finset σ) (e : σ →₀ ℕ) : ℕ := ∑ i ∈ V, e i

def profile (V : Finset σ) (e : σ →₀ ℕ) : (σ →₀ ℕ) × ℕ :=
  (baseExponent V e, freshDegree V e)

def profileCount (V : Finset σ) (S : Finset (σ →₀ ℕ))
    (p : (σ →₀ ℕ) × ℕ) : ℕ := (S.filter (fun e => profile V e = p)).card

def SameProfiles (V : Finset σ) (S T : Finset (σ →₀ ℕ)) : Prop :=
  ∀ p, profileCount V S p = profileCount V T p

def admissible (P : MvPolynomial σ K) (S : Finset (σ →₀ ℕ)) : Prop :=
  ∃ G : MvPolynomial σ K, G ≠ 0 ∧ P ∣ G ∧ G.support ⊆ S

def potential (V : Finset σ) (w : σ → ℕ) (S : Finset (σ →₀ ℕ)) : ℕ :=
  ∑ e ∈ S, ∑ i ∈ V, w i * e i

/-- A finite coordinate bound containing every redistribution in one profile. -/
def expandedBound (V : Finset σ) (e : σ →₀ ℕ) : σ →₀ ℕ :=
  baseExponent V e + ∑ i ∈ V, Finsupp.single i (freshDegree V e)

theorem le_expandedBound_of_profile_eq (V : Finset σ) (d e : σ →₀ ℕ)
    (h : profile V d = profile V e) : d ≤ expandedBound V e := by
  classical
  intro i
  by_cases hi : i ∈ V
  · have hdegree : freshDegree V d = freshDegree V e := congrArg Prod.snd h
    have hle : d i ≤ freshDegree V d :=
      Finset.single_le_sum (fun j hj => Nat.zero_le (d j)) hi
    rw [hdegree] at hle
    simpa [expandedBound, baseExponent, Finsupp.filter_apply, Finsupp.finset_sum_apply,
      Finsupp.single_apply, hi] using hle
  · have hbase : baseExponent V d i = baseExponent V e i :=
      congrArg (fun p : (σ →₀ ℕ) × ℕ => p.1 i) h
    simp only [baseExponent, Finsupp.filter_apply, hi, not_false_eq_true, if_true] at hbase
    simp [expandedBound, baseExponent, Finsupp.filter_apply, Finsupp.finset_sum_apply,
      Finsupp.single_apply, hi, hbase]

theorem SameProfiles.exists_match {V : Finset σ} {S T : Finset (σ →₀ ℕ)}
    (h : SameProfiles V S T) {e : σ →₀ ℕ} (he : e ∈ T) :
    ∃ d ∈ S, profile V d = profile V e := by
  classical
  have hp : 0 < profileCount V T (profile V e) :=
    Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
  rw [← h (profile V e)] at hp
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hp
  exact ⟨d, (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2⟩

/-- A finite box suffices even when the ambient variable type is infinite. -/
def profileUniverse (V : Finset σ) (S : Finset (σ →₀ ℕ)) : Finset (σ →₀ ℕ) :=
  Finset.Icc 0 (∑ e ∈ S, expandedBound V e)

theorem sameProfiles_subset_universe {V : Finset σ} {S T : Finset (σ →₀ ℕ)}
    (h : SameProfiles V S T) : T ⊆ profileUniverse V S := by
  intro e he
  obtain ⟨d, hd, hprof⟩ := h.exists_match he
  apply Finset.mem_Icc.mpr
  refine ⟨zero_le e, ?_⟩
  exact (le_expandedBound_of_profile_eq V e d hprof.symm).trans
    (Finset.single_le_sum (fun j hj => zero_le (expandedBound V j)) hd)

theorem SameProfiles.card_eq {V : Finset σ} {S T : Finset (σ →₀ ℕ)}
    (h : SameProfiles V S T) : S.card = T.card := by
  classical
  have hT : ∀ e ∈ T, profile V e ∈ S.image (profile V) := by
    intro e he
    obtain ⟨d, hd, hde⟩ := h.exists_match he
    exact Finset.mem_image.mpr ⟨d, hd, hde⟩
  rw [Finset.card_eq_sum_card_fiberwise (fun e he =>
    Finset.mem_image_of_mem (profile V) he), Finset.card_eq_sum_card_fiberwise hT]
  exact Finset.sum_congr rfl (fun p hp => h p)

/-- The paper's support candidate family is a subset of the powerset of a
finite coordinate box. Its coefficients range over the original field. -/
def candidates (V : Finset σ) (P : MvPolynomial σ K) (S : Finset (σ →₀ ℕ)) :
    Finset (Finset (σ →₀ ℕ)) := by
  classical
  exact (profileUniverse V S).powerset.filter
    (fun T => SameProfiles V S T ∧ admissible P T)

theorem mem_candidates_iff (V : Finset σ) (P : MvPolynomial σ K)
    (S T : Finset (σ →₀ ℕ)) : T ∈ candidates V P S ↔
      SameProfiles V S T ∧ admissible P T := by
  classical
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨sameProfiles_subset_universe h.1, h⟩

/-- Actual maximization over all supports with the original profile counts
that contain a nonzero multiple. There is no assumption of a finite field. -/
theorem exists_maximal_profile (V : Finset σ) (w : σ → ℕ)
    (P G : MvPolynomial σ K) (hG : G ≠ 0) (hdiv : P ∣ G) :
    ∃ S : Finset (σ →₀ ℕ), SameProfiles V G.support S ∧ admissible P S ∧
      ∀ T, SameProfiles V G.support T → admissible P T →
        potential V w T ≤ potential V w S := by
  classical
  have hseed : G.support ∈ candidates V P G.support := by
    rw [mem_candidates_iff]
    exact ⟨fun _ => rfl, G, hG, hdiv, Finset.Subset.refl _⟩
  obtain ⟨S, hS, hmax⟩ := (candidates V P G.support).exists_max_image
    (potential V w) ⟨G.support, hseed⟩
  obtain ⟨hprof, hadm⟩ := (mem_candidates_iff V P G.support S).mp hS
  refine ⟨S, hprof, hadm, ?_⟩
  intro T hT hTa
  exact hmax T ((mem_candidates_iff V P G.support T).mpr ⟨hT, hTa⟩)

/-- At a maximum, an admissible profile-preserving transition that strictly
increases the potential whenever it changes the set must fix the set. -/
theorem maximal_profile_fixed {V : Finset σ} {w : σ → ℕ}
    {P : MvPolynomial σ K} {original S T : Finset (σ →₀ ℕ)}
    (hmax : ∀ A, SameProfiles V original A → admissible P A →
      potential V w A ≤ potential V w S)
    (hT : SameProfiles V original T) (hadm : admissible P T)
    (hstrict : T ≠ S → potential V w S < potential V w T) : T = S := by
  by_contra hne
  exact (Nat.not_lt_of_ge (hmax T hT hadm)) (hstrict hne)

theorem SameProfiles.base_match {V : Finset σ} {S T : Finset (σ →₀ ℕ)}
    (h : SameProfiles V S T) {d : σ →₀ ℕ} (hd : d ∈ T) :
    ∃ e ∈ S, ∀ i ∉ V, d i = e i := by
  obtain ⟨e, he, hprof⟩ := h.exists_match hd
  refine ⟨e, he, ?_⟩
  intro i hi
  have hbase := congrArg (fun p : (σ →₀ ℕ) × ℕ => p.1 i) hprof
  simpa only [profile, baseExponent, Finsupp.filter_apply, hi,
    not_false_eq_true, if_true] using hbase.symm

/-- The chosen maximum has an actual witness over K with no new base
exponents and at most the original number of terms. -/
theorem exists_maximal_profile_multiple (V : Finset σ) (w : σ → ℕ)
    (P G : MvPolynomial σ K) (hG : G ≠ 0) (hdiv : P ∣ G) :
    ∃ (S : Finset (σ →₀ ℕ)) (G₀ : MvPolynomial σ K),
      SameProfiles V G.support S ∧ G₀ ≠ 0 ∧ P ∣ G₀ ∧ G₀.support ⊆ S ∧
      weight G₀ ≤ weight G ∧
      (∀ d ∈ G₀.support, ∃ e ∈ G.support, ∀ i ∉ V, d i = e i) ∧
      (∀ i ∉ V, widthOf i G₀ ≤ widthOf i G) ∧
      ∀ T, SameProfiles V G.support T → admissible P T →
        potential V w T ≤ potential V w S := by
  obtain ⟨S, hS, ⟨G₀, hG₀, hdvd, hsub⟩, hmax⟩ :=
    exists_maximal_profile V w P G hG hdiv
  have hbase : ∀ d ∈ G₀.support, ∃ e ∈ G.support, ∀ i ∉ V, d i = e i :=
    fun d hd => hS.base_match (hsub hd)
  refine ⟨S, G₀, hS, hG₀, hdvd, hsub, ?_, hbase, ?_, hmax⟩
  · change G₀.support.card ≤ G.support.card
    rw [hS.card_eq]
    exact Finset.card_le_card hsub
  · intro i hi
    apply widthOf_mono_exponents i hG₀
    intro d hd
    obtain ⟨e, he, heq⟩ := hbase d hd
    exact ⟨e, he, heq i hi⟩

end WeightedPilz.Compression
