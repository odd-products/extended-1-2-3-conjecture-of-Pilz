import Density.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Tauto

/-!
# The exact divisibility cut for odd products

Unlike a bound by the number of uncancelled representation pairs, this cut keeps
the parity cancellations already present in the lower part. The proof is finite
and works for every positive modulus coprime to the lower coefficients.
-/

noncomputable section

namespace PilzDensity

open scoped symmDiff

theorem representationCount_union (B C I : Finset ℕ) (m : ℕ)
    (hBC : Disjoint B C) :
    Pilz.representationCount (B ∪ C) I m =
      Pilz.representationCount B I m + Pilz.representationCount C I m := by
  classical
  unfold Pilz.representationCount
  rw [Finset.union_product, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter (Finset.disjoint_product.mpr (Or.inl hBC)))

theorem oddProduct_union (B C I : Finset ℕ) (hBC : Disjoint B C) :
    Pilz.oddProduct (B ∪ C) I = Pilz.oddProduct B I ∆ Pilz.oddProduct C I := by
  classical
  ext m
  simp only [Pilz.mem_oddProduct_iff, Finset.mem_symmDiff,
    representationCount_union B C I m hBC, Nat.odd_add, ← Nat.not_odd_iff_even]
  tauto

/-- Scaling the output by a modulus coprime to every lower coefficient scales
the interval parameter down by exactly that modulus. -/
theorem representationCount_mul (B : Finset ℕ) (n Q m : ℕ) (hQ : 0 < Q)
    (hB : ∀ a ∈ B, Nat.Coprime Q a) :
    Pilz.representationCount B (Finset.Icc 1 n) (Q * m) =
      Pilz.representationCount B (Finset.Icc 1 (n / Q)) m := by
  classical
  symm
  unfold Pilz.representationCount
  apply Finset.card_bij (fun ab _ => (ab.1, Q * ab.2))
  · rintro ⟨a, b⟩ hab
    rcases Finset.mem_filter.mp hab with ⟨hab, heq⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    rcases Finset.mem_Icc.mp hb with ⟨hbpos, hble⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · exact Nat.mul_pos hQ hbpos
    · simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hQ).mp hble
    · change a * (Q * b) = Q * m
      calc
        a * (Q * b) = Q * (a * b) := by ac_rfl
        _ = Q * m := congrArg (Q * ·) heq
  · intro ab hab cd hcd heq
    apply Prod.ext
    · have hf := congrArg (fun x : ℕ × ℕ => x.1) heq
      exact hf
    · have hs := congrArg (fun x : ℕ × ℕ => x.2) heq
      exact Nat.eq_of_mul_eq_mul_left hQ hs
  · rintro ⟨a, b⟩ hab
    rcases Finset.mem_filter.mp hab with ⟨hab, heq⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    rcases Finset.mem_Icc.mp hb with ⟨hbpos, hble⟩
    have hdiv : Q ∣ b := (hB a ha).dvd_of_dvd_mul_left (heq.symm ▸ dvd_mul_right Q m)
    obtain ⟨c, rfl⟩ := hdiv
    refine ⟨(a, c), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · exact Nat.pos_of_mul_pos_left hbpos
    · exact (Nat.le_div_iff_mul_le hQ).mpr (by simpa only [Nat.mul_comm] using hble)
    · apply Nat.eq_of_mul_eq_mul_left hQ
      calc
        Q * (a * c) = a * (Q * c) := by ac_rfl
        _ = Q * m := heq

/-- Exact parity-preserving identification of the lower outputs divisible by Q. -/
theorem oddProduct_filter_dvd (B : Finset ℕ) (n Q : ℕ) (hQ : 0 < Q)
    (hB : ∀ a ∈ B, Nat.Coprime Q a) :
    (Pilz.oddProduct B (Finset.Icc 1 n)).filter (Q ∣ ·) =
      (Pilz.oddProduct B (Finset.Icc 1 (n / Q))).image (Q * ·) := by
  classical
  ext m
  constructor
  · intro hm
    rcases Finset.mem_filter.mp hm with ⟨hm, ⟨k, rfl⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, rfl⟩
    rw [Pilz.mem_oddProduct_iff] at hm ⊢
    rwa [representationCount_mul B n Q k hQ hB] at hm
  · intro hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨?_, dvd_mul_right Q k⟩
    rw [Pilz.mem_oddProduct_iff] at hk ⊢
    rwa [representationCount_mul B n Q k hQ hB]

theorem oddProduct_filter_dvd_card (B : Finset ℕ) (n Q : ℕ) (hQ : 0 < Q)
    (hB : ∀ a ∈ B, Nat.Coprime Q a) :
    ((Pilz.oddProduct B (Finset.Icc 1 n)).filter (Q ∣ ·)).card = count B (n / Q) := by
  rw [oddProduct_filter_dvd B n Q hQ hB]
  exact Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left hQ h)

theorem dvd_of_mem_oddProduct (C I : Finset ℕ) (Q : ℕ)
    (hC : ∀ a ∈ C, Q ∣ a) {m : ℕ} (hm : m ∈ Pilz.oddProduct C I) : Q ∣ m := by
  classical
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hm).1
  exact dvd_mul_of_dvd_left (hC a (Finset.mem_product.mp hab).1) b

/-- The cardinality cancellation inequality, without truncated subtraction. -/
theorem card_symmDiff_cancellation (S T : Finset ℕ) :
    S.card + T.card ≤ (S ∆ T).card + 2 * (S ∩ T).card := by
  classical
  have hsub : S ∪ T ⊆ (S ∆ T) ∪ (S ∩ T) := by
    intro m hm
    simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter] at hm ⊢
    tauto
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le (S ∆ T) (S ∩ T)
  have h₃ := Finset.card_union_add_card_inter S T
  omega

/-- The finite exact divisibility cut. Its overlap term retains all lower-side
parity cancellation and is the lower odd-product count at the divided length. -/
theorem count_exact_cut (B C : Finset ℕ) (n Q : ℕ) (hQ : 0 < Q)
    (hBC : Disjoint B C) (hB : ∀ a ∈ B, Nat.Coprime Q a)
    (hC : ∀ a ∈ C, Q ∣ a) :
    count B n + count C n ≤ count (B ∪ C) n + 2 * count B (n / Q) := by
  classical
  have hsub : Pilz.oddProduct B (Finset.Icc 1 n) ∩
      Pilz.oddProduct C (Finset.Icc 1 n) ⊆
      (Pilz.oddProduct B (Finset.Icc 1 n)).filter (Q ∣ ·) := by
    intro m hm
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hm).1,
      dvd_of_mem_oddProduct C (Finset.Icc 1 n) Q hC (Finset.mem_inter.mp hm).2⟩
  have hi := Finset.card_le_card hsub
  rw [oddProduct_filter_dvd_card B n Q hQ hB] at hi
  have hc := card_symmDiff_cancellation
    (Pilz.oddProduct B (Finset.Icc 1 n)) (Pilz.oddProduct C (Finset.Icc 1 n))
  rw [← oddProduct_union B C (Finset.Icc 1 n) hBC] at hc
  change count B n + count C n ≤ count (B ∪ C) n +
    2 * (Pilz.oddProduct B (Finset.Icc 1 n) ∩ Pilz.oddProduct C (Finset.Icc 1 n)).card at hc
  omega

end PilzDensity

