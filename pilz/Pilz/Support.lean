import Pilz.Minimal

/-!
# Support bounds used in the directed cut

These are the elementary support estimates from the proof of
`lem:directed-cut`, and the invariance under monomial multiplication in
`lem:reductions` (a). The cancellation estimate holds over every
commutative semiring, so in particular over every field used in the paper.
-/

noncomputable section

namespace Pilz

open MvPolynomial

section GeneralSupport

variable {σ R : Type*} [DecidableEq σ] [CommSemiring R]

/-- A term present on either side survives addition unless it occurs on both sides. -/
theorem support_union_subset_add_union_inter
    (P Q : MvPolynomial σ R) :
    P.support ∪ Q.support ⊆ (P + Q).support ∪ (P.support ∩ Q.support) := by
  classical
  intro d hd
  by_cases hi : d ∈ P.support ∩ Q.support
  · exact Finset.mem_union_right _ hi
  · apply Finset.mem_union_left
    rcases Finset.mem_union.mp hd with hp | hq
    · have hq : d ∉ Q.support := fun hq => hi (Finset.mem_inter.mpr ⟨hp, hq⟩)
      have hq0 := MvPolynomial.notMem_support_iff.mp hq
      simpa only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add,
        hq0, add_zero] using hp
    · have hp : d ∉ P.support := fun hp => hi (Finset.mem_inter.mpr ⟨hp, hq⟩)
      have hp0 := MvPolynomial.notMem_support_iff.mp hp
      simpa only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add,
        hp0, zero_add] using hq

/-- The support cancellation inequality, in a form without truncated subtraction. -/
theorem support_card_add_cancellation (P Q : MvPolynomial σ R) :
    P.support.card + Q.support.card ≤
      (P + Q).support.card + 2 * (P.support ∩ Q.support).card := by
  classical
  have h₁ := Finset.card_le_card (support_union_subset_add_union_inter P Q)
  have h₂ := Finset.card_union_le (P + Q).support (P.support ∩ Q.support)
  have h₃ := Finset.card_union_add_card_inter P.support Q.support
  omega

/-- Disjoint supports add without cancellation. -/
theorem support_card_add_of_disjoint (P Q : MvPolynomial σ R)
    (h : Disjoint P.support Q.support) :
    (P + Q).support.card = P.support.card + Q.support.card := by
  classical
  change (Finsupp.support (P + Q)).card = _
  rw [Finsupp.support_add_eq h]
  exact Finset.card_union_of_disjoint h

end GeneralSupport

/-- Paper, directed cut: at most two terms are lost for each common support point. -/
theorem weight_add_cancellation (P Q : Poly) :
    weight P + weight Q ≤
      weight (P + Q) + 2 * (P.support ∩ Q.support).card :=
  support_card_add_cancellation P Q

theorem weight_add_of_disjoint (P Q : Poly)
    (h : Disjoint P.support Q.support) :
    weight (P + Q) = weight P + weight Q :=
  support_card_add_of_disjoint P Q h

/-- Paper, elementary reductions (a): multiplying by a monomial preserves weight. -/
@[simp] theorem weight_monomial_mul (s : ℕ →₀ ℕ) (P : Poly) :
    weight ((MvPolynomial.monomial s 1 : Poly) * P) = weight P := by
  have hs : (MvPolynomial.monomial s 1 * P : Poly).support =
      P.support.map (addLeftEmbedding s) :=
    AddMonoidAlgebra.support_single_mul P 1 (by simp) s
  simp only [weight, hs, Finset.card_map]

@[simp] theorem weight_mul_monomial (s : ℕ →₀ ℕ) (P : Poly) :
    weight (P * (MvPolynomial.monomial s 1 : Poly)) = weight P := by
  rw [mul_comm]
  exact weight_monomial_mul s P

/-- The product support has no more elements than the set of pairs of terms. -/
theorem weight_mul_le (P Q : Poly) :
    weight (P * Q) ≤ weight P * weight Q := by
  classical
  unfold weight
  exact (Finset.card_le_card (MvPolynomial.support_mul P Q)).trans
    Finset.card_add_le

/-- The singleton multipliers attain the conjectured lower bound exactly. -/
@[simp] theorem weight_interval_mul_monomialOf (n a : ℕ) :
    weight (interval n * monomialOf a) = n := by
  simp only [monomialOf, weight_mul_monomial, weight_interval]

/-- The cancellation step at the start of the directed-cut argument. -/
theorem directed_cut_intersection (n : ℕ) (P Q : Poly)
    (hP : n ≤ weight P) (hQ : n ≤ weight Q)
    (hshort : weight (P + Q) < n) :
    n < 2 * (P.support ∩ Q.support).card := by
  have h := weight_add_cancellation P Q
  omega

/-- The strict numerical conclusion of the directed cut, once the overlap
bound has supplied its floor inequality. This lemma does not assume or prove
that overlap bound. -/
theorem directed_cut_prime_bound (n u₀ q b : ℕ)
    (hq : 1 ≤ q) (hb : 0 < b)
    (hcut : n < 2 * u₀ * (n / q ^ b)) :
    q < 2 * u₀ := by
  by_contra hnot
  have hqp : q ≤ q ^ b := by
    simpa only [pow_one] using
      (pow_le_pow_right' hq (show 1 ≤ b by omega))
  have hsmall : 2 * u₀ ≤ q ^ b := (Nat.le_of_not_gt hnot).trans hqp
  have hmul := Nat.mul_le_mul_right (n / q ^ b) hsmall
  have hdiv := Nat.div_mul_le_self n (q ^ b)
  exact (not_lt_of_ge (hmul.trans (by simpa only [Nat.mul_comm] using hdiv))) hcut

/-- Multiplication cannot reduce the exponent of a variable in an upper slice. -/
theorem support_mul_exponent_lower_bound (P U : Poly) (q b : ℕ)
    (hU : ∀ e ∈ U.support, b ≤ e q) :
    ∀ d ∈ (P * U).support, b ≤ d q := by
  classical
  intro d hd
  obtain ⟨s, hs, t, ht, hst⟩ :=
    Finset.mem_add.mp (MvPolynomial.support_mul P U hd)
  rw [← hst, Finsupp.add_apply]
  exact (hU t ht).trans (Nat.le_add_left _ _)

/-- The support overlap in a cut is bounded by the number of lower-side
term pairs whose exponent reaches the upper threshold. This is the
combinatorial part of the paper's overlap bound; evaluating this pair
count for `interval n` requires the separate prime-valuation count. -/
theorem support_cut_pair_bound (P L U : Poly) (q b : ℕ)
    (hU : ∀ e ∈ U.support, b ≤ e q) :
    ((P * L).support ∩ (P * U).support).card ≤
      ((P.support ×ˢ L.support).filter
        (fun st => b ≤ st.1 q + st.2 q)).card := by
  classical
  let S := (P.support ×ˢ L.support).filter
    (fun st => b ≤ st.1 q + st.2 q)
  have hsub : (P * L).support ∩ (P * U).support ⊆
      S.image (fun st => st.1 + st.2) := by
    intro d hd
    have hdU := support_mul_exponent_lower_bound P U q b hU d
      (Finset.mem_inter.mp hd).2
    obtain ⟨s, hs, t, ht, hst⟩ :=
      Finset.mem_add.mp (MvPolynomial.support_mul P L (Finset.mem_inter.mp hd).1)
    apply Finset.mem_image.mpr
    refine ⟨(s, t), ?_, hst⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hs, ht⟩, ?_⟩
    simpa only [← hst, Finsupp.add_apply] using hdU
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

/-- The directed-cut inequality before evaluating the interval pair count. -/
theorem directed_cut_pair_count (n q b : ℕ) (P L U : Poly)
    (hU : ∀ e ∈ U.support, b ≤ e q)
    (hLprod : n ≤ weight (P * L)) (hUprod : n ≤ weight (P * U))
    (hshort : weight (P * (L + U)) < n) :
    n < 2 * ((P.support ×ˢ L.support).filter
      (fun st => b ≤ st.1 q + st.2 q)).card := by
  rw [mul_add] at hshort
  have hcut := directed_cut_intersection n (P * L) (P * U)
    hLprod hUprod hshort
  exact hcut.trans_le (Nat.mul_le_mul_left 2 (support_cut_pair_bound P L U q b hU))

/-- Exactly `⌊n / q^b⌋` interval terms reach `q`-exponent `b`. -/
theorem interval_exponent_count (n q b : ℕ) (hq : Nat.Prime q) :
    ((interval n).support.filter (fun d => b ≤ d q)).card = n / q ^ b := by
  classical
  have hpos : ∀ a ∈ Finset.Icc 1 n, 0 < a := by
    intro a ha
    exact (Finset.mem_Icc.mp ha).1
  rw [interval_eq_polynomialOf, support_polynomialOf _ hpos, Finset.filter_image]
  have hinj : Set.InjOn Nat.factorization
      ((Finset.Icc 1 n).filter (fun a => b ≤ a.factorization q)) := by
    intro a ha c hc hac
    exact Nat.factorization_inj
      (ne_of_gt (hpos a (Finset.mem_filter.mp ha).1))
      (ne_of_gt (hpos c (Finset.mem_filter.mp hc).1)) hac
  rw [Finset.card_image_iff.mpr hinj]
  have hfilter : (Finset.Icc 1 n).filter (fun a => b ≤ a.factorization q) =
      (Finset.range n.succ).filter (fun a => a ≠ 0 ∧ q ^ b ∣ a) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨ha, han⟩, hval⟩
      have ha0 : a ≠ 0 := by omega
      exact ⟨by omega, ha0, (hq.pow_dvd_iff_le_factorization ha0).mpr hval⟩
    · rintro ⟨han, ha0, hdvd⟩
      exact ⟨⟨by omega, by omega⟩, (hq.pow_dvd_iff_le_factorization ha0).mp hdvd⟩
  rw [hfilter]
  exact Nat.card_multiples' n (q ^ b)

/-- At the least positive occupied exponent the lower slice is independent
of `x_q`; this specializes the pair-count cut to the paper's floor bound. -/
theorem directed_cut_interval_floor (n q b : ℕ) (L U : Poly)
    (hq : Nat.Prime q)
    (hL : ∀ e ∈ L.support, e q = 0)
    (hU : ∀ e ∈ U.support, b ≤ e q)
    (hLprod : n ≤ weight (interval n * L))
    (hUprod : n ≤ weight (interval n * U))
    (hshort : weight (interval n * (L + U)) < n) :
    n < 2 * weight L * (n / q ^ b) := by
  classical
  have hcut := directed_cut_pair_count n q b (interval n) L U
    hU hLprod hUprod hshort
  have hfilter : ((interval n).support ×ˢ L.support).filter
      (fun st => b ≤ st.1 q + st.2 q) =
      ((interval n).support.filter (fun d => b ≤ d q)) ×ˢ L.support := by
    ext st
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hs, ht⟩, he⟩
      exact ⟨⟨hs, by simpa [hL st.2 ht] using he⟩, ht⟩
    · rintro ⟨⟨hs, he⟩, ht⟩
      exact ⟨⟨hs, ht⟩, by simpa [hL st.2 ht] using he⟩
  rw [hfilter, Finset.card_product, interval_exponent_count n q b hq] at hcut
  simpa [weight, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcut

/-- The prime restriction follows from a cut at the least positive
occupied exponent. Existence and deletion minimality of the cut are
separate hypotheses supplied by the paper's reduction step. -/
theorem directed_cut_interval_prime_bound (n q b : ℕ) (L U : Poly)
    (hq : Nat.Prime q) (hb : 0 < b)
    (hL : ∀ e ∈ L.support, e q = 0)
    (hU : ∀ e ∈ U.support, b ≤ e q)
    (hLprod : n ≤ weight (interval n * L))
    (hUprod : n ≤ weight (interval n * U))
    (hshort : weight (interval n * (L + U)) < n) :
    q < 2 * weight L :=
  directed_cut_prime_bound n (weight L) q b (Nat.le_of_lt hq.one_lt) hb
    (directed_cut_interval_floor n q b L U hq hL hU hLprod hUprod hshort)

/-- Paper, directed cut: a deletion-minimal counterexample with a term of
`q`-exponent zero and a term of positive `q`-exponent satisfies the strict
prime bound. The normalization step is recorded by the zero-exponent
hypothesis rather than assumed implicitly. -/
theorem deletionMinimal_prime_bound (n q : ℕ) (D : Poly)
    (hq : Nat.Prime q)
    (hzero : ∃ d ∈ D.support, d q = 0)
    (hpos : ∃ d ∈ D.support, 0 < d q)
    (hmin : DeletionMinimal n D)
    (hshort : weight (interval n * D) < n) :
    q < 2 * (weight D - 1) := by
  classical
  let S := D.support.filter (fun d => d q = 0)
  let T := D.support.filter (fun d => d q ≠ 0)
  let L := restrictTerms D S
  let U := restrictTerms D T
  have hSsub : S ⊆ D.support := Finset.filter_subset _ _
  have hTsub : T ⊆ D.support := Finset.filter_subset _ _
  have hSnonempty : S.Nonempty := by
    obtain ⟨d, hd, hdq⟩ := hzero
    exact ⟨d, Finset.mem_filter.mpr ⟨hd, hdq⟩⟩
  have hTnonempty : T.Nonempty := by
    obtain ⟨d, hd, hdq⟩ := hpos
    exact ⟨d, Finset.mem_filter.mpr ⟨hd, ne_of_gt hdq⟩⟩
  have hSproper : S ≠ D.support := by
    intro h
    obtain ⟨d, hd, hdq⟩ := hpos
    have hmem : d ∈ S := by rw [h]; exact hd
    have := (Finset.mem_filter.mp hmem).2
    omega
  have hTproper : T ≠ D.support := by
    intro h
    obtain ⟨d, hd, hdq⟩ := hzero
    have hmem : d ∈ T := by rw [h]; exact hd
    exact (Finset.mem_filter.mp hmem).2 hdq
  have hLsupp : L.support = S := support_restrictTerms_of_subset D S hSsub
  have hUsupp : U.support = T := support_restrictTerms_of_subset D T hTsub
  have hsplit : L + U = D := by
    apply MvPolynomial.ext
    intro d
    change (if d ∈ S then MvPolynomial.coeff d D else 0) +
      (if d ∈ T then MvPolynomial.coeff d D else 0) = MvPolynomial.coeff d D
    by_cases hd : d ∈ D.support
    · by_cases hdq : d q = 0 <;> simp [S, T, hd, hdq]
    · have hz : MvPolynomial.coeff d D = 0 := MvPolynomial.notMem_support_iff.mp hd
      simp [S, T, hd, hz]
  have hL : ∀ e ∈ L.support, e q = 0 := by
    intro e he
    rw [hLsupp] at he
    exact (Finset.mem_filter.mp he).2
  have hU : ∀ e ∈ U.support, 1 ≤ e q := by
    intro e he
    rw [hUsupp] at he
    have := (Finset.mem_filter.mp he).2
    omega
  have hLprod : n ≤ weight (interval n * L) := hmin S hSsub hSnonempty hSproper
  have hUprod : n ≤ weight (interval n * U) := hmin T hTsub hTnonempty hTproper
  have hshort' : weight (interval n * (L + U)) < n := by
    rw [hsplit]
    exact hshort
  have hbound := directed_cut_interval_prime_bound n q 1 L U hq (by omega)
    hL hU hLprod hUprod hshort'
  have hcard := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hSsub, hSproper⟩)
  unfold weight at hbound ⊢
  rw [hLsupp] at hbound
  omega

end Pilz
