import Density.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat

noncomputable section

namespace PilzDensity

theorem representationCount_scale (A I : Finset ℕ) (c m : ℕ) (hc : 0 < c) :
    Pilz.representationCount (A.image (c * ·)) I (c * m) =
      Pilz.representationCount A I m := by
  classical
  symm
  unfold Pilz.representationCount
  apply Finset.card_bij (fun ab _ => (c * ab.1, ab.2))
  · rintro ⟨a, b⟩ hab
    rcases Finset.mem_filter.mp hab with ⟨hab, heq⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, hb⟩, ?_⟩
    change (c * a) * b = c * m
    rw [mul_assoc, heq]
  · rintro ⟨a, b⟩ hab ⟨d, e⟩ hde heq
    have h := Prod.mk.inj heq
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hc h.1) h.2
  · rintro ⟨a, b⟩ hab
    rcases Finset.mem_filter.mp hab with ⟨hab, heq⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    change a ∈ A.image (c * ·) at ha
    obtain ⟨a', ha', haa⟩ := Finset.mem_image.mp ha
    subst a
    refine ⟨(a', b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha', hb⟩, ?_⟩, rfl⟩
    exact Nat.eq_of_mul_eq_mul_left hc (by simpa only [mul_assoc] using heq)

theorem oddProduct_scale (A I : Finset ℕ) (c : ℕ) (hc : 0 < c) :
    Pilz.oddProduct (A.image (c * ·)) I =
      (Pilz.oddProduct A I).image (c * ·) := by
  classical
  ext m
  constructor
  · intro hm
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hm).1
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha
    change (c * a) * b = m at heq
    rw [mul_assoc] at heq
    subst m
    apply Finset.mem_image.mpr
    refine ⟨a * b, ?_, rfl⟩
    rw [Pilz.mem_oddProduct_iff] at hm ⊢
    rwa [representationCount_scale A I c (a * b) hc] at hm
  · intro hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    rw [Pilz.mem_oddProduct_iff] at hk ⊢
    rwa [representationCount_scale A I c k hc]

theorem count_scale (A : Finset ℕ) (c n : ℕ) (hc : 0 < c) :
    count (A.image (c * ·)) n = count A n := by
  unfold count
  rw [oddProduct_scale A (Finset.Icc 1 n) c hc]
  exact Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left hc h)

theorem hasDensity_scale_iff (A : Finset ℕ) (c : ℕ) (hc : 0 < c) (d : ℝ) :
    HasDensity (A.image (c * ·)) d ↔ HasDensity A d := by
  unfold HasDensity
  simp only [count_scale A c _ hc]

theorem density_scale (A : Finset ℕ) (c : ℕ) (hc : 0 < c) :
    density (A.image (c * ·)) = density A := by
  classical
  by_cases h : ∃ d, HasDensity A d
  · exact ((hasDensity_scale_iff A c hc _).mpr (hasDensity_of_exists h)).eq_density
  · have h' : ¬ ∃ d, HasDensity (A.image (c * ·)) d := by
      simpa only [hasDensity_scale_iff A c hc] using h
    simp [density, h, h']

theorem exceptional_scale_iff (A : Finset ℕ) (c : ℕ) (hc : 0 < c) :
    Exceptional (A.image (c * ·)) ↔ Exceptional A := by
  classical
  have hinj : Function.Injective (c * ·) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hc h
  constructor
  · rintro ⟨x, hx, hxA⟩
    have hxmem : x ∈ A.image (c * ·) := by rcases hxA with h | h <;> simp [h]
    obtain ⟨a, ha, hca⟩ := Finset.mem_image.mp hxmem
    have hapos : 0 < a := Nat.pos_of_mul_pos_left (hca.symm ▸ hx)
    refine ⟨a, hapos, ?_⟩
    rcases hxA with h | h
    · left
      apply Finset.image_injective hinj
      simpa only [Finset.image_singleton, hca] using h
    · right
      apply Finset.image_injective hinj
      have htwice : c * (2 * a) = 2 * x := by rw [mul_left_comm, hca]
      simpa only [Finset.image_insert, Finset.image_singleton, hca, htwice] using h
  · rintro ⟨a, ha, hA⟩
    refine ⟨c * a, Nat.mul_pos hc ha, ?_⟩
    rcases hA with rfl | rfl
    · left; simp
    · right; simp [mul_left_comm]

/-- Dividing a finite set by its common greatest divisor. -/
def normalize (A : Finset ℕ) : Finset ℕ :=
  A.image (fun a => a / A.gcd id)

theorem gcd_positive (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    0 < A.gcd id := by
  obtain ⟨a, ha⟩ := hne
  exact Nat.pos_of_ne_zero (Finset.gcd_ne_zero_iff.mpr ⟨a, ha, ne_of_gt (hA a ha)⟩)

theorem image_normalize (A : Finset ℕ) :
    (normalize A).image (A.gcd id * ·) = A := by
  classical
  unfold normalize
  rw [Finset.image_image]
  have h : ∀ a ∈ A, A.gcd id * (a / A.gcd id) = a := by
    intro a ha
    exact Nat.mul_div_cancel' (Finset.gcd_dvd ha)
  exact Finset.image_congr h |>.trans Finset.image_id

theorem normalize_positive (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ∀ b ∈ normalize A, 0 < b := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  exact Nat.div_pos (Nat.le_of_dvd (hA a ha) (Finset.gcd_dvd ha))
    (gcd_positive A hA ⟨a, ha⟩)

theorem normalize_card (A : Finset ℕ) : (normalize A).card = A.card := by
  classical
  unfold normalize
  apply Finset.card_image_iff.mpr
  intro a ha b hb heq
  have hmul := congrArg (A.gcd id * ·) heq
  have ha' : A.gcd id * (a / A.gcd id) = a :=
    Nat.mul_div_cancel' (Finset.gcd_dvd ha)
  have hb' : A.gcd id * (b / A.gcd id) = b :=
    Nat.mul_div_cancel' (Finset.gcd_dvd hb)
  exact ha'.symm.trans (hmul.trans hb')

theorem normalize_nonempty (A : Finset ℕ) (hne : A.Nonempty) : (normalize A).Nonempty :=
  hne.image _

theorem normalize_gcd (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    (normalize A).gcd id = 1 := by
  obtain ⟨a, ha⟩ := hne
  unfold normalize
  rw [Finset.gcd_image]
  exact Finset.gcd_div_id_eq_one ha (ne_of_gt (hA a ha))

theorem density_normalize (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    density (normalize A) = density A := by
  simpa only [image_normalize] using
    (density_scale (normalize A) (A.gcd id) (gcd_positive A hA hne)).symm

theorem exceptional_normalize_iff (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hne : A.Nonempty) : Exceptional (normalize A) ↔ Exceptional A := by
  simpa only [image_normalize] using
    (exceptional_scale_iff (normalize A) (A.gcd id) (gcd_positive A hA hne)).symm

theorem exists_normalized (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    ∃ B : Finset ℕ, (∀ b ∈ B, 0 < b) ∧ B.Nonempty ∧ B.gcd id = 1 ∧
      B.card = A.card ∧ density B = density A ∧ (Exceptional B ↔ Exceptional A) :=
  ⟨normalize A, normalize_positive A hA, normalize_nonempty A hne,
    normalize_gcd A hA hne, normalize_card A, density_normalize A hA hne,
    exceptional_normalize_iff A hA hne⟩

end PilzDensity
