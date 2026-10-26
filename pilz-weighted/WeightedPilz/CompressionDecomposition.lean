import WeightedPilz.CompressionBlocks

/-! Exact finite support decomposition into pair blocks for scalar compression. -/

noncomputable section
namespace WeightedPilz.Compression
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ]

def pairKey (i j : σ) (e : σ →₀ ℕ) : (σ →₀ ℕ) × ℕ :=
  (pairBase i j e, e i + e j)

def pairKeys (S : Finset (σ →₀ ℕ)) (i j : σ) : Finset ((σ →₀ ℕ) × ℕ) :=
  S.image (pairKey i j)

def pairBlock (S : Finset (σ →₀ ℕ)) (i j : σ) (k : (σ →₀ ℕ) × ℕ) :
    Finset (σ →₀ ℕ) :=
  (pairIndices S i j k.1 k.2).image (pairExponent i j k.1 k.2)

theorem pairExponent_left (i j : σ) (hij : i ≠ j) (b : σ →₀ ℕ)
    (hi : b i = 0) (d : ℕ) (a : Fin (d + 1)) : pairExponent i j b d a i = a.val := by
  simp [pairExponent, hi, hij]

theorem pairExponent_right (i j : σ) (hij : i ≠ j) (b : σ →₀ ℕ)
    (hj : b j = 0) (d : ℕ) (a : Fin (d + 1)) :
    pairExponent i j b d a j = d - a.val := by
  simp [pairExponent, hj, hij.symm]

theorem pairExponent_injective (i j : σ) (hij : i ≠ j) (b : σ →₀ ℕ) (d : ℕ) :
    Function.Injective (pairExponent i j b d) := by
  intro a a' heq
  have h := congrArg (fun e => e i) heq
  simp [pairExponent, hij] at h
  exact Fin.ext h

theorem pairBase_pairExponent (i j : σ) (hij : i ≠ j) (b : σ →₀ ℕ)
    (hi : b i = 0) (hj : b j = 0) (d : ℕ) (a : Fin (d + 1)) :
    pairBase i j (pairExponent i j b d a) = b := by
  ext q
  by_cases hqi : q = i
  · subst q
    simp [hi]
  · by_cases hqj : q = j
    · subst q
      simp [hj]
    · simp [pairBase, pairExponent, Finsupp.erase_apply, hqi, hqj]

theorem pairKey_pairExponent (i j : σ) (hij : i ≠ j) (b : σ →₀ ℕ)
    (hi : b i = 0) (hj : b j = 0) (d : ℕ) (a : Fin (d + 1)) :
    pairKey i j (pairExponent i j b d a) = (b, d) := by
  apply Prod.ext
  · exact pairBase_pairExponent i j hij b hi hj d a
  · change pairExponent i j b d a i + pairExponent i j b d a j = d
    rw [pairExponent_left i j hij b hi, pairExponent_right i j hij b hj]
    exact Nat.add_sub_of_le (Nat.le_of_lt_succ a.isLt)

theorem pairExponent_canonical (i j : σ) (hij : i ≠ j) (e : σ →₀ ℕ) :
    pairExponent i j (pairBase i j e) (e i + e j)
      ⟨e i, by omega⟩ = e := by
  simpa only [pairExponent, Nat.add_sub_cancel_left] using pairBase_reconstruct i j hij e

theorem pairKeys_base_zero (S : Finset (σ →₀ ℕ)) (i j : σ)
    {k : (σ →₀ ℕ) × ℕ} (hk : k ∈ pairKeys S i j) : k.1 i = 0 ∧ k.1 j = 0 := by
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
  simp [pairKey]

theorem pairKey_mem_pairKeys (S : Finset (σ →₀ ℕ)) (i j : σ)
    {e : σ →₀ ℕ} (he : e ∈ S) : pairKey i j e ∈ pairKeys S i j :=
  Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem mem_pairBlock_iff (S : Finset (σ →₀ ℕ)) (i j : σ) (hij : i ≠ j)
    (k : (σ →₀ ℕ) × ℕ) (hi : k.1 i = 0) (hj : k.1 j = 0) (e : σ →₀ ℕ) :
    e ∈ pairBlock S i j k ↔ e ∈ S ∧ pairKey i j e = k := by
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    refine ⟨(mem_pairIndices S i j k.1 k.2 a).mp ha, ?_⟩
    exact pairKey_pairExponent i j hij k.1 hi hj k.2 a
  · rintro ⟨he, hk⟩
    subst k
    let a : Fin (e i + e j + 1) := ⟨e i, by omega⟩
    have hexp : pairExponent i j (pairBase i j e) (e i + e j) a = e :=
      pairExponent_canonical i j hij e
    refine Finset.mem_image.mpr ⟨a, ?_, hexp⟩
    apply (mem_pairIndices S i j (pairBase i j e) (e i + e j) a).mpr
    rwa [hexp]

theorem pairBlock_subset (S : Finset (σ →₀ ℕ)) (i j : σ)
    (k : (σ →₀ ℕ) × ℕ) : pairBlock S i j k ⊆ S := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  exact (mem_pairIndices S i j k.1 k.2 a).mp ha

theorem pairBlocks_disjoint (S : Finset (σ →₀ ℕ)) (i j : σ) (hij : i ≠ j)
    {k l : (σ →₀ ℕ) × ℕ} (hk : k ∈ pairKeys S i j) (hl : l ∈ pairKeys S i j)
    (hkl : k ≠ l) : Disjoint (pairBlock S i j k) (pairBlock S i j l) := by
  apply Finset.disjoint_left.mpr
  intro e hek hel
  obtain ⟨hki, hkj⟩ := pairKeys_base_zero S i j hk
  obtain ⟨hli, hlj⟩ := pairKeys_base_zero S i j hl
  have hekey := (mem_pairBlock_iff S i j hij k hki hkj e).mp hek
  have helkey := (mem_pairBlock_iff S i j hij l hli hlj e).mp hel
  exact hkl (hekey.2.symm.trans helkey.2)

theorem pairBlocks_pairwiseDisjoint (S : Finset (σ →₀ ℕ)) (i j : σ) (hij : i ≠ j) :
    (pairKeys S i j).toSet.PairwiseDisjoint (pairBlock S i j) := by
  intro k hk l hl hkl
  exact pairBlocks_disjoint S i j hij hk hl hkl

theorem pairBlocks_biUnion (S : Finset (σ →₀ ℕ)) (i j : σ) (hij : i ≠ j) :
    (pairKeys S i j).biUnion (pairBlock S i j) = S := by
  ext e
  constructor
  · intro he
    obtain ⟨k, hk, hek⟩ := Finset.mem_biUnion.mp he
    exact pairBlock_subset S i j k hek
  · intro he
    refine Finset.mem_biUnion.mpr ⟨pairKey i j e, pairKey_mem_pairKeys S i j he, ?_⟩
    apply (mem_pairBlock_iff S i j hij (pairKey i j e)
      (pairBase_left i j e) (pairBase_right i j e) e).mpr
    exact ⟨he, rfl⟩

theorem card_pairBlock (S : Finset (σ →₀ ℕ)) (i j : σ) (hij : i ≠ j)
    (k : (σ →₀ ℕ) × ℕ) :
    (pairBlock S i j k).card = (pairIndices S i j k.1 k.2).card :=
  Finset.card_image_of_injective _ (pairExponent_injective i j hij k.1 k.2)

theorem card_eq_sum_pairIndices (S : Finset (σ →₀ ℕ)) (i j : σ) (hij : i ≠ j) :
    S.card = ∑ k ∈ pairKeys S i j, (pairIndices S i j k.1 k.2).card := by
  calc
    S.card = ((pairKeys S i j).biUnion (pairBlock S i j)).card :=
      congrArg Finset.card (pairBlocks_biUnion S i j hij).symm
    _ = ∑ k ∈ pairKeys S i j, (pairBlock S i j k).card :=
      Finset.card_biUnion (pairBlocks_pairwiseDisjoint S i j hij)
    _ = _ := Finset.sum_congr rfl (fun k _ => card_pairBlock S i j hij k)

section Polynomial
variable [CommSemiring K]

def pairBlockPolynomial (S : Finset (σ →₀ ℕ)) (i j : σ) (Q : MvPolynomial σ K)
    (k : (σ →₀ ℕ) × ℕ) : MvPolynomial σ K :=
  ∑ e ∈ pairBlock S i j k, monomial e (coeff e Q)

theorem coeff_pairBlockPolynomial (S : Finset (σ →₀ ℕ)) (i j : σ)
    (Q : MvPolynomial σ K) (k : (σ →₀ ℕ) × ℕ) (e : σ →₀ ℕ) :
    coeff e (pairBlockPolynomial S i j Q k) =
      if e ∈ pairBlock S i j k then coeff e Q else 0 := by
  classical
  simp [pairBlockPolynomial, coeff_sum, coeff_monomial]

theorem support_pairBlockPolynomial (S : Finset (σ →₀ ℕ)) (i j : σ)
    (Q : MvPolynomial σ K) (k : (σ →₀ ℕ) × ℕ) :
    (pairBlockPolynomial S i j Q k).support = Q.support ∩ pairBlock S i j k := by
  ext e
  rw [mem_support_iff, coeff_pairBlockPolynomial]
  by_cases he : e ∈ pairBlock S i j k <;> simp [he, mem_support_iff]

theorem pairBlockPolynomial_as_sum_indices (S : Finset (σ →₀ ℕ)) (i j : σ)
    (hij : i ≠ j) (Q : MvPolynomial σ K) (k : (σ →₀ ℕ) × ℕ) :
    pairBlockPolynomial S i j Q k = ∑ a ∈ pairIndices S i j k.1 k.2,
      monomial (pairExponent i j k.1 k.2 a) (coeff (pairExponent i j k.1 k.2 a) Q) := by
  rw [pairBlockPolynomial, pairBlock, Finset.sum_image]
  intro a ha b hb hab
  exact pairExponent_injective i j hij k.1 k.2 hab

theorem eq_sum_pairBlockPolynomial (S : Finset (σ →₀ ℕ)) (i j : σ) (hij : i ≠ j)
    (Q : MvPolynomial σ K) (hQ : Q.support ⊆ S) :
    Q = ∑ k ∈ pairKeys S i j, pairBlockPolynomial S i j Q k := by
  have hsum : Q = ∑ e ∈ S, monomial e (coeff e Q) := by
    calc
      Q = ∑ e ∈ Q.support, monomial e (coeff e Q) := Q.as_sum
      _ = _ := by
        apply Finset.sum_subset hQ
        intro e heS heQ
        rw [notMem_support_iff.mp heQ, monomial_zero]
  calc
    Q = ∑ e ∈ S, monomial e (coeff e Q) := hsum
    _ = ∑ k ∈ pairKeys S i j, pairBlockPolynomial S i j Q k := by
      conv_lhs => rw [← pairBlocks_biUnion S i j hij]
      rw [Finset.sum_biUnion (pairBlocks_pairwiseDisjoint S i j hij)]
      rfl

theorem eq_sum_pairIndices (S : Finset (σ →₀ ℕ)) (i j : σ) (hij : i ≠ j)
    (Q : MvPolynomial σ K) (hQ : Q.support ⊆ S) :
    Q = ∑ k ∈ pairKeys S i j, ∑ a ∈ pairIndices S i j k.1 k.2,
      monomial (pairExponent i j k.1 k.2 a) (coeff (pairExponent i j k.1 k.2 a) Q) := by
  calc
    Q = ∑ k ∈ pairKeys S i j, pairBlockPolynomial S i j Q k :=
      eq_sum_pairBlockPolynomial S i j hij Q hQ
    _ = _ := Finset.sum_congr rfl (fun k _ => pairBlockPolynomial_as_sum_indices S i j hij Q k)

theorem coeff_pairBlockPolynomial_at_index (S : Finset (σ →₀ ℕ)) (i j : σ)
    (hij : i ≠ j) (Q : MvPolynomial σ K) {k l : (σ →₀ ℕ) × ℕ}
    (hk : k ∈ pairKeys S i j) (hl : l ∈ pairKeys S i j)
    (a : Fin (k.2 + 1)) (ha : a ∈ pairIndices S i j k.1 k.2) :
    coeff (pairExponent i j k.1 k.2 a) (pairBlockPolynomial S i j Q l) =
      if k = l then coeff (pairExponent i j k.1 k.2 a) Q else 0 := by
  obtain ⟨hki, hkj⟩ := pairKeys_base_zero S i j hk
  obtain ⟨hli, hlj⟩ := pairKeys_base_zero S i j hl
  simp only [coeff_pairBlockPolynomial, mem_pairBlock_iff S i j hij l hli hlj,
    pairKey_pairExponent i j hij k.1 hki hkj,
    (mem_pairIndices S i j k.1 k.2 a).mp ha, true_and]

/-- Full coordinate sums within one block have their specified coefficients. -/
theorem coeff_sum_pairExponent (i j : σ) (hij : i ≠ j) (b : σ →₀ ℕ) (d : ℕ)
    (v : Fin (d + 1) → K) (a : Fin (d + 1)) :
    coeff (pairExponent i j b d a)
      (∑ t : Fin (d + 1), monomial (pairExponent i j b d t) (v t)) = v a := by
  classical
  rw [coeff_sum, Finset.sum_eq_single a]
  · simp
  · intro t ht hta
    have he : pairExponent i j b d t ≠ pairExponent i j b d a :=
      fun h => hta (pairExponent_injective i j hij b d h)
    simp [coeff_monomial, he]
  · simp

/-- Different pair keys cannot contribute to the same coefficient, even when
each block uses all of its possible first exponents. -/
theorem coeff_sum_pairBlocks (B : Finset ((σ →₀ ℕ) × ℕ)) (i j : σ) (hij : i ≠ j)
    (hB : ∀ k ∈ B, k.1 i = 0 ∧ k.1 j = 0)
    (v : ∀ k : (σ →₀ ℕ) × ℕ, Fin (k.2 + 1) → K)
    {q : (σ →₀ ℕ) × ℕ} (hq : q ∈ B) (a : Fin (q.2 + 1)) :
    coeff (pairExponent i j q.1 q.2 a)
      (∑ k ∈ B, ∑ t : Fin (k.2 + 1), monomial (pairExponent i j k.1 k.2 t) (v k t)) =
      v q a := by
  classical
  rw [coeff_sum, Finset.sum_eq_single q]
  · exact coeff_sum_pairExponent i j hij q.1 q.2 (v q) a
  · intro k hk hkq
    rw [coeff_sum]
    apply Finset.sum_eq_zero
    intro t ht
    have he : pairExponent i j k.1 k.2 t ≠ pairExponent i j q.1 q.2 a := by
      intro heq
      have hkkey := pairKey_pairExponent i j hij k.1 (hB k hk).1 (hB k hk).2 k.2 t
      have hqkey := pairKey_pairExponent i j hij q.1 (hB q hq).1 (hB q hq).2 q.2 a
      exact hkq (hkkey.symm.trans ((congrArg (pairKey i j) heq).trans hqkey))
    simp [coeff_monomial, he]
  · exact fun hn => False.elim (hn hq)

end Polynomial
end WeightedPilz.Compression
