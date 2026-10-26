import WeightedPilz.Endpoints
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Polynomial.Div

/-! Adding one independent variable, the first step of `thm:completion`. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial

variable {σ K : Type*} [Field K]

/-- Append one new variable to a base polynomial. -/
def freshCompletion (A : MvPolynomial σ K) : MvPolynomial (Option σ) K :=
  rename some A + X none

theorem optionEquivLeft_rename_some (A : MvPolynomial σ K) :
    optionEquivLeft K σ (rename some A) = Polynomial.C A := by
  have h : (optionEquivLeft K σ).toRingHom.comp
      (rename (some : σ → Option σ)).toRingHom = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [optionEquivLeft_C]
    · intro i
      simp [optionEquivLeft_X_some]
  exact RingHom.congr_fun h A

theorem optionEquivLeft_freshCompletion (A : MvPolynomial σ K) :
    optionEquivLeft K σ (freshCompletion A) = Polynomial.X + Polynomial.C A := by
  rw [freshCompletion, map_add, optionEquivLeft_rename_some, optionEquivLeft_X_none, add_comm]

theorem freshCompletion_ne_zero (A : MvPolynomial σ K) : freshCompletion A ≠ 0 := by
  intro hz
  have h := congrArg (optionEquivLeft K σ) hz
  rw [optionEquivLeft_freshCompletion, map_zero] at h
  have hdeg := congrArg Polynomial.natDegree h
  simpa using hdeg

/-- Divisibility by the completion is the substitution equation at `-A`. -/
theorem freshCompletion_dvd_iff (A : MvPolynomial σ K)
    (G : MvPolynomial (Option σ) K) :
    freshCompletion A ∣ G ↔ (optionEquivLeft K σ G).eval (-A) = 0 := by
  constructor
  · rintro ⟨H, rfl⟩
    rw [map_mul, optionEquivLeft_freshCompletion, Polynomial.eval_mul]
    simp
  · intro h
    have hd : Polynomial.X - Polynomial.C (-A) ∣ optionEquivLeft K σ G :=
      Polynomial.dvd_iff_isRoot.mpr h
    obtain ⟨H, hH⟩ := hd
    refine ⟨(optionEquivLeft K σ).symm H, ?_⟩
    apply (optionEquivLeft K σ).injective
    rw [map_mul, optionEquivLeft_freshCompletion, AlgEquiv.apply_symm_apply]
    simpa using hH

private theorem monomial_mul_divMonomial_exact
    (G : MvPolynomial (Option σ) K) (α : Option σ →₀ ℕ)
    (hα : ∀ d ∈ G.support, α ≤ d) : monomial α 1 * divMonomial G α = G := by
  have hrem : modMonomial G α = 0 := by
    ext d
    by_cases hd : d ∈ G.support
    · exact coeff_modMonomial_of_le G (hα d hd)
    · by_cases had : α ≤ d
      · exact coeff_modMonomial_of_le G had
      · rw [coeff_modMonomial_of_not_le G had]
        exact notMem_support_iff.mp hd
  simpa [hrem] using divMonomial_add_modMonomial G α

/-- Remove the lowest fresh-variable power. Divisibility and the number of
terms survive, and the resulting constant row is nonzero. -/
theorem freshCompletion_normalize (A : MvPolynomial σ K) (hA : A ≠ 0)
    (G : MvPolynomial (Option σ) K) (hG : G ≠ 0) (hdvd : freshCompletion A ∣ G) :
    ∃ (k : ℕ) (F : MvPolynomial (Option σ) K),
      G = monomial (Finsupp.single none k) 1 * F ∧
      weight F = weight G ∧ F ≠ 0 ∧ freshCompletion A ∣ F ∧
      (optionEquivLeft K σ F).coeff 0 ≠ 0 := by
  classical
  have hS : G.support.Nonempty := support_nonempty.mpr hG
  let k := G.support.inf' hS (fun d => d none)
  let α : Option σ →₀ ℕ := Finsupp.single none k
  let F := divMonomial G α
  have hα : ∀ d ∈ G.support, α ≤ d := by
    intro d hd i
    cases i with
    | none => simpa [α, k] using Finset.inf'_le (fun d : Option σ →₀ ℕ => d none) hd
    | some i => simp [α]
  have hfactor : G = monomial α 1 * F := (monomial_mul_divMonomial_exact G α hα).symm
  have hF : F ≠ 0 := by
    intro hz
    rw [hfactor, hz, mul_zero] at hG
    exact hG rfl
  refine ⟨k, F, hfactor, ?_, hF, ?_, ?_⟩
  · rw [hfactor, weight_monomial_mul]
  · apply (freshCompletion_dvd_iff A F).mpr
    have heval := (freshCompletion_dvd_iff A G).mp hdvd
    rw [hfactor, map_mul, Polynomial.eval_mul, optionEquivLeft_monomial] at heval
    have hleft : (optionEquivLeft K σ (monomial α (1 : K))).eval (-A) ≠ 0 := by
      rw [optionEquivLeft_monomial]
      simpa [α, Finsupp.some_single_none] using pow_ne_zero k (neg_ne_zero.mpr hA)
    exact (mul_eq_zero.mp heval).resolve_left (by
      simpa only [optionEquivLeft_monomial] using hleft)
  · obtain ⟨d, hd, hk⟩ := Finset.exists_mem_eq_inf' hS (fun d => d none)
    have hdF : d - α ∈ F.support := by
      apply mem_support_iff.mpr
      change coeff (d - α) (divMonomial G α) ≠ 0
      rw [coeff_divMonomial, add_tsub_cancel_of_le (hα d hd)]
      exact mem_support_iff.mp hd
    have hzcoord : (d - α) none = 0 := by
      simp only [Finsupp.tsub_apply, α, Finsupp.single_eq_same]
      change d none - G.support.inf' hS (fun d => d none) = 0
      omega
    intro hz
    have hc := optionEquivLeft_coeff_coeff K σ (d - α) F
    rw [hzcoord, hz, coeff_zero] at hc
    exact mem_support_iff.mp hdF hc.symm

private def freshZeroPart (G : MvPolynomial (Option σ) K) : MvPolynomial (Option σ) K := by
  classical
  exact Finsupp.filter (fun d => d none = 0) G

private def freshPositivePart (G : MvPolynomial (Option σ) K) : MvPolynomial (Option σ) K := by
  classical
  exact Finsupp.filter (fun d => d none ≠ 0) G

private theorem coeff_option_lift (G : MvPolynomial (Option σ) K) (n : ℕ) (d : σ →₀ ℕ) :
    coeff d ((optionEquivLeft K σ G).coeff n) =
      coeff (d.embDomain .some + Finsupp.single none n) G := by
  let m : Option σ →₀ ℕ := d.embDomain .some + Finsupp.single none n
  have hn : m none = n := by simp [m]
  have hs : m.some = d := by
    ext i
    simp [m]
  change coeff d ((optionEquivLeft K σ G).coeff n) = coeff m G
  simpa only [hn, hs] using optionEquivLeft_coeff_coeff K σ
    m G

private theorem option_freshZeroPart (G : MvPolynomial (Option σ) K) :
    optionEquivLeft K σ (freshZeroPart G) =
      Polynomial.C ((optionEquivLeft K σ G).coeff 0) := by
  classical
  apply Polynomial.ext
  intro n
  apply MvPolynomial.ext
  intro d
  rw [coeff_option_lift, Polynomial.coeff_C]
  change (if ((d.embDomain .some + Finsupp.single none n : Option σ →₀ ℕ) none) = 0 then
    coeff (d.embDomain .some + Finsupp.single none n) G else 0) = _
  by_cases hn : n = 0
  · subst n
    simp only [Finsupp.single_zero, add_zero, Finsupp.embDomain_some_none, ↓reduceIte]
    simpa only [Finsupp.single_zero, add_zero] using (coeff_option_lift G 0 d).symm
  · simp [hn, coeff_zero]

private theorem freshZeroPart_eq (G : MvPolynomial (Option σ) K) :
    freshZeroPart G = rename some ((optionEquivLeft K σ G).coeff 0) := by
  apply (optionEquivLeft K σ).injective
  rw [option_freshZeroPart, optionEquivLeft_rename_some]

private theorem fresh_parts_add (G : MvPolynomial (Option σ) K) :
    freshZeroPart G + freshPositivePart G = G := by
  classical
  exact Finsupp.filter_pos_add_filter_neg G (fun d => d none = 0)

theorem weight_rename_some (A : MvPolynomial σ K) :
    weight (rename (some : σ → Option σ) A) = weight A := by
  classical
  rw [weight, support_rename_of_injective (Option.some_injective σ)]
  exact Finset.card_image_of_injective _ (Finsupp.mapDomain_injective (Option.some_injective σ))

private theorem fresh_parts_weight (G : MvPolynomial (Option σ) K) :
    weight G = weight ((optionEquivLeft K σ G).coeff 0) + weight (freshPositivePart G) := by
  classical
  have hdis : Disjoint (freshZeroPart G).support (freshPositivePart G).support := by
    apply Finset.disjoint_left.mpr
    intro d hd he
    exact (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hd).2
  calc
    weight G = weight (freshZeroPart G + freshPositivePart G) :=
      congrArg weight (fresh_parts_add G).symm
    _ = weight (freshZeroPart G) + weight (freshPositivePart G) :=
      weight_add_of_disjoint _ _ hdis
    _ = _ := by rw [freshZeroPart_eq, weight_rename_some]

/-- The nonzero constant row of a completion multiple is a base multiple. -/
theorem freshCompletion_constant_dvd (A : MvPolynomial σ K)
    (G : MvPolynomial (Option σ) K) (hG : freshCompletion A ∣ G) :
    A ∣ (optionEquivLeft K σ G).coeff 0 := by
  have h := Polynomial.sub_dvd_eval_sub 0 (-A) (optionEquivLeft K σ G)
  rw [← Polynomial.coeff_zero_eq_eval_zero] at h
  simpa [(freshCompletion_dvd_iff A G).mp hG] using h

/-- Below the endpoint budget plus one, precisely one positive fresh term
is possible. This is the sparse-shape step of sharp completion. -/
theorem freshCompletion_short_shape (A : MvPolynomial σ K)
    (G : MvPolynomial (Option σ) K) (hG : freshCompletion A ∣ G)
    (h0 : (optionEquivLeft K σ G).coeff 0 ≠ 0)
    (hshort : weight G < distance A + 2) :
    ∃ (d : Option σ →₀ ℕ) (c : K), c ≠ 0 ∧ 0 < d none ∧
      G = rename some ((optionEquivLeft K σ G).coeff 0) + monomial d c ∧
      weight G = weight ((optionEquivLeft K σ G).coeff 0) + 1 := by
  classical
  let B := (optionEquivLeft K σ G).coeff 0
  have hB : distance A ≤ weight B := by
    obtain ⟨H, hH⟩ := freshCompletion_constant_dvd A G hG
    have hHn : H ≠ 0 := by
      intro hz
      rw [hH, hz, mul_zero] at h0
      exact h0 rfl
    simpa only [B, hH] using distance_le_weight_mul A H hHn
  have hpos : freshPositivePart G ≠ 0 := by
    intro hz
    have heq : G = rename some B := by
      rw [← fresh_parts_add G, hz, add_zero, freshZeroPart_eq]
    have hroot := (freshCompletion_dvd_iff A G).mp hG
    rw [heq, optionEquivLeft_rename_some, Polynomial.eval_C] at hroot
    exact h0 hroot
  have hcardpos : 0 < weight (freshPositivePart G) := by
    simpa [weight, Finset.card_pos, support_nonempty] using hpos
  have hsum := fresh_parts_weight G
  have hcard : (freshPositivePart G).support.card = 1 := by
    change (freshPositivePart G).support.card = 1
    change 0 < (freshPositivePart G).support.card at hcardpos
    change weight G = weight B + (freshPositivePart G).support.card at hsum
    omega
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hcard
  have hdsupp : d ∈ (freshPositivePart G).support := by simp [hd]
  have hdne : d none ≠ 0 := (Finset.mem_filter.mp hdsupp).2
  let c := coeff d (freshPositivePart G)
  have hc : c ≠ 0 := mem_support_iff.mp hdsupp
  have hmono : freshPositivePart G = monomial d c :=
    (Finsupp.support_eq_singleton.mp hd).2
  refine ⟨d, c, hc, by omega, ?_, ?_⟩
  · calc
      G = freshZeroPart G + freshPositivePart G := (fresh_parts_add G).symm
      _ = _ := by rw [freshZeroPart_eq, hmono]
  · change weight G = weight B + 1
    change weight G = weight B + (freshPositivePart G).support.card at hsum
    rwa [hcard] at hsum

end WeightedPilz
