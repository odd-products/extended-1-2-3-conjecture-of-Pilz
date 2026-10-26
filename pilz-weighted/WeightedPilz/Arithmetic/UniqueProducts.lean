import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

/-!
# Persistent unique products of middle-interval cores

The seven final-column counts in `eq:fin-block-budgets` of the frozen
manuscript. All pairs are unordered by retaining only pairs `(a,b)` with
`a ≤ b`. The persistence argument is independent of the finite computations.
-/

namespace WeightedPilz.Arithmetic

set_option Elab.async false

/-- Integer support remaining after the primes in `(n/2,n]` are removed. -/
def core (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun a => ¬(Nat.Prime a ∧ n / 2 < a))

/-- All unordered multiplicative representations by members of the core. -/
def representations (n m : ℕ) : Finset (ℕ × ℕ) :=
  ((core n) ×ˢ (core n)).filter (fun ab => ab.1 ≤ ab.2 ∧ ab.1 * ab.2 = m)

/-- The finite product support of the core. -/
def products (n : ℕ) : Finset ℕ :=
  ((core n) ×ˢ (core n)).image (fun ab => ab.1 * ab.2)

/-- Products with exactly one unordered representation. -/
def uniqueProducts (n : ℕ) : Finset ℕ :=
  (products n).filter (fun m => (representations n m).card = 1)

/-- Products present at the first endpoint and unique at the last endpoint. -/
def persistentProducts (a b : ℕ) : Finset ℕ :=
  (products a).filter (fun m => (representations b m).card = 1)

/-- The manuscript's persistent unique-product count `ell(a,b)`. -/
def ell (a b : ℕ) : ℕ := (persistentProducts a b).card

theorem core_mono : Monotone core := by
  intro a b hab x hx
  simp only [core, Finset.mem_filter, Finset.mem_Icc, not_and] at hx ⊢
  refine ⟨⟨hx.1.1, hx.1.2.trans hab⟩, ?_⟩
  intro hp hlt
  exact hx.2 hp (lt_of_le_of_lt (Nat.div_le_div_right hab) hlt)

theorem representations_mono {a b : ℕ} (hab : a ≤ b) (m : ℕ) :
    representations a m ⊆ representations b m := by
  intro p hp
  simp only [representations, Finset.mem_filter, Finset.mem_product] at hp ⊢
  exact ⟨⟨core_mono hab hp.1.1, core_mono hab hp.1.2⟩, hp.2⟩

theorem products_mono : Monotone products := by
  intro a b hab m hm
  obtain ⟨⟨x,y⟩, hp, rfl⟩ := Finset.mem_image.mp hm
  exact Finset.mem_image.mpr ⟨(x,y),
    Finset.mem_product.mpr ⟨core_mono hab (Finset.mem_product.mp hp).1,
      core_mono hab (Finset.mem_product.mp hp).2⟩, rfl⟩

theorem representations_nonempty_iff {n m : ℕ} :
    (representations n m).Nonempty ↔ m ∈ products n := by
  constructor
  · rintro ⟨⟨x,y⟩, hp⟩
    simp only [representations, Finset.mem_filter] at hp
    exact Finset.mem_image.mpr ⟨(x,y), hp.1, hp.2.2⟩
  · intro hm
    obtain ⟨⟨x,y⟩, hp, hprod⟩ := Finset.mem_image.mp hm
    rcases le_total x y with hxy | hyx
    · exact ⟨(x,y), Finset.mem_filter.mpr ⟨hp, hxy, hprod⟩⟩
    · refine ⟨(y,x), Finset.mem_filter.mpr ⟨?_, hyx, ?_⟩⟩
      · exact Finset.mem_product.mpr (Finset.mem_product.mp hp).symm
      · simpa [Nat.mul_comm] using hprod

/-- Endpoint uniqueness survives at every intermediate core. -/
theorem persistentProducts_subset {a n b : ℕ} (han : a ≤ n) (hnb : n ≤ b) :
    persistentProducts a b ⊆ uniqueProducts n := by
  intro m hm
  obtain ⟨ha, hb⟩ := Finset.mem_filter.mp hm
  have hn := products_mono han ha
  refine Finset.mem_filter.mpr ⟨hn, ?_⟩
  apply Nat.le_antisymm
  · exact hb ▸ Finset.card_le_card (representations_mono hnb m)
  · exact Finset.card_pos.mpr (representations_nonempty_iff.mpr hn)

/-- The exact persistent count is a lower bound for every intermediate count. -/
theorem ell_le_uniqueProducts_card {a n b : ℕ} (han : a ≤ n) (hnb : n ≤ b) :
    ell a b ≤ (uniqueProducts n).card :=
  Finset.card_le_card (persistentProducts_subset han hnb)

theorem ell_self (n : ℕ) : ell n n = (uniqueProducts n).card := rfl

/-- An equivalent divisor enumeration, avoiding a quadratic search for each product. -/
def representationDivisors (n m : ℕ) : Finset ℕ :=
  (core n).filter (fun d => d ≤ m / d ∧ m % d = 0 ∧ m / d ∈ core n)

theorem representations_card_eq (n m : ℕ) :
    (representations n m).card = (representationDivisors n m).card := by
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    obtain ⟨⟨hx, hy⟩, hxy, hprod⟩ :=
      (by simpa only [representations, Finset.mem_filter, Finset.mem_product] using hp)
    have hxpos : 0 < p.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).1
    have hdiv : m / p.1 = p.2 := by
      rw [← hprod, Nat.mul_div_cancel_left _ hxpos]
    refine Finset.mem_filter.mpr ⟨hx, ?_, ?_, ?_⟩
    · simpa only [hdiv] using hxy
    · rw [← hprod, Nat.mul_mod_right]
    · simpa only [hdiv] using hy
  · intro p hp q hq heq
    obtain ⟨⟨hx, _⟩, _, hprod⟩ :=
      (by simpa only [representations, Finset.mem_filter, Finset.mem_product] using hp)
    have hxpos : 0 < p.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).1
    have hprodq := (Finset.mem_filter.mp hq).2.2
    apply Prod.ext heq
    apply Nat.eq_of_mul_eq_mul_left hxpos
    exact hprod.trans (heq ▸ hprodq.symm)
  · intro d hd
    obtain ⟨hd, hle, hmod, hdiv⟩ := Finset.mem_filter.mp hd
    refine ⟨(d, m / d), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hd, hdiv⟩, hle,
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)⟩

theorem products_mem_bounds {n m : ℕ} (hm : m ∈ products n) : 1 ≤ m ∧ m ≤ n * n := by
  obtain ⟨⟨x,y⟩, hp, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
  have hxx := Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
  have hyy := Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1
  exact ⟨Nat.mul_pos hxx.1 hyy.1, Nat.mul_le_mul hxx.2 hyy.2⟩

/-- The explicit finite divisor formula used in the manuscript. -/
theorem ell_eq_divisor_count (a b : ℕ) :
    ell a b = ((Finset.Icc 1 (a*a)).filter (fun m =>
      0 < (representationDivisors a m).card ∧
      (representationDivisors b m).card = 1)).card := by
  unfold ell
  congr 1
  apply Finset.ext
  intro m
  simp only [persistentProducts, Finset.mem_filter]
  rw [← representations_card_eq, ← representations_card_eq, Finset.card_pos,
    representations_nonempty_iff]
  constructor
  · intro h
    exact ⟨Finset.mem_Icc.mpr (products_mem_bounds h.1), h⟩
  · exact fun h => h.2

theorem not_mem_products_iff (n m : ℕ) :
    m ∉ products n ↔ (representationDivisors n m).card = 0 := by
  rw [← representations_nonempty_iff, ← Finset.card_pos, representations_card_eq]
  simp

/-- Parameterizing the core sets keeps their finite computation outside every divisor test. -/
private def persistentCount (A B : Finset ℕ) (bound : ℕ) : ℕ :=
  ((Finset.Icc 1 bound).filter (fun m =>
    0 < (A.filter (fun d => d ≤ m / d ∧ m % d = 0 ∧ m / d ∈ A)).card ∧
    (B.filter (fun d => d ≤ m / d ∧ m % d = 0 ∧ m / d ∈ B)).card = 1)).card

private theorem ell_eq_persistentCount (a b : ℕ) :
    ell a b = persistentCount (core a) (core b) (a*a) := ell_eq_divisor_count a b

/-- Direct recursion avoids constructing and traversing a large interval list in the kernel. -/
private def persistentCountRec (A B : Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => persistentCountRec A B n + if
      0 < (A.filter (fun d => d ≤ (n+1) / d ∧ (n+1) % d = 0 ∧ (n+1) / d ∈ A)).card ∧
      (B.filter (fun d => d ≤ (n+1) / d ∧ (n+1) % d = 0 ∧ (n+1) / d ∈ B)).card = 1
      then 1 else 0

private theorem persistentCount_eq_rec (A B : Finset ℕ) (n : ℕ) :
    persistentCount A B n = persistentCountRec A B n := by
  induction n with
  | zero => simp [persistentCount, persistentCountRec]
  | succ n ih =>
    rw [persistentCountRec, ← ih]
    unfold persistentCount
    rw [← Nat.Icc_insert_succ_right (Nat.succ_le_succ (Nat.zero_le n)),
      Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem]
      intro hm
      exact Nat.not_succ_le_self n (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    · simp

/-- A bounded segment of the recurrence, used to keep each kernel certificate small. -/
private def persistentSegment (A B : Finset ℕ) (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => persistentSegment A B start n + if
      0 < (A.filter (fun d => d ≤ (start+n+1) / d ∧ (start+n+1) % d = 0 ∧ (start+n+1) / d ∈ A)).card ∧
      (B.filter (fun d => d ≤ (start+n+1) / d ∧ (start+n+1) % d = 0 ∧ (start+n+1) / d ∈ B)).card = 1
      then 1 else 0

private theorem persistentCountRec_add (A B : Finset ℕ) (start len : ℕ) :
    persistentCountRec A B (start + len) =
      persistentCountRec A B start + persistentSegment A B start len := by
  induction len with
  | zero => simp [persistentSegment]
  | succ n ih =>
    rw [Nat.add_succ, persistentCountRec, persistentSegment, ih]
    simp only [Nat.add_assoc]

section FiniteCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def coreData25 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_25 : core 25 = coreData25 := by decide +kernel
private def coreData26 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_26 : core 26 = coreData26 := by decide +kernel
private def coreData27 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_27 : core 27 = coreData27 := by decide +kernel
private def coreData28 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_28 : core 28 = coreData28 := by decide +kernel
private def coreData29 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_29 : core 29 = coreData29 := by decide +kernel
private def coreData33 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28, 30, 32, 33] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_33 : core 33 = coreData33 := by decide +kernel
private def coreData34 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 30, 32, 33, 34] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_34 : core 34 = coreData34 := by decide +kernel
private def coreData37 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27, 28, 30, 32, 33, 34, 35, 36] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_37 : core 37 = coreData37 := by decide +kernel
private def coreData38 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 32, 33, 34, 35, 36, 38] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_38 : core 38 = coreData38 := by decide +kernel
private def coreData40 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 32, 33, 34, 35, 36, 38, 39, 40] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_40 : core 40 = coreData40 := by decide +kernel
private def coreData50 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 48, 49, 50] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_50 : core 50 = coreData50 := by decide +kernel
private def coreData51 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 48, 49, 50, 51] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_51 : core 51 = coreData51 := by decide +kernel
private def coreData66 : Finset ℕ := (⟨([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 60, 62, 63, 64, 65, 66] : List ℕ), by decide⟩ : Finset ℕ)
private theorem core_66 : core 66 = coreData66 := by decide +kernel

private theorem prefix_25_26_32 : persistentCountRec coreData25 coreData26 32 = 7 := by
  simp only [persistentCountRec]
  decide +kernel

private theorem prefix_25_26_64 : persistentCountRec coreData25 coreData26 64 = 11 := by
  change persistentCountRec coreData25 coreData26 (32 + 32) = 11
  rw [persistentCountRec_add, prefix_25_26_32]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_96 : persistentCountRec coreData25 coreData26 96 = 13 := by
  change persistentCountRec coreData25 coreData26 (64 + 32) = 13
  rw [persistentCountRec_add, prefix_25_26_64]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_128 : persistentCountRec coreData25 coreData26 128 = 18 := by
  change persistentCountRec coreData25 coreData26 (96 + 32) = 18
  rw [persistentCountRec_add, prefix_25_26_96]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_160 : persistentCountRec coreData25 coreData26 160 = 20 := by
  change persistentCountRec coreData25 coreData26 (128 + 32) = 20
  rw [persistentCountRec_add, prefix_25_26_128]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_192 : persistentCountRec coreData25 coreData26 192 = 24 := by
  change persistentCountRec coreData25 coreData26 (160 + 32) = 24
  rw [persistentCountRec_add, prefix_25_26_160]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_224 : persistentCountRec coreData25 coreData26 224 = 26 := by
  change persistentCountRec coreData25 coreData26 (192 + 32) = 26
  rw [persistentCountRec_add, prefix_25_26_192]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_256 : persistentCountRec coreData25 coreData26 256 = 30 := by
  change persistentCountRec coreData25 coreData26 (224 + 32) = 30
  rw [persistentCountRec_add, prefix_25_26_224]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_288 : persistentCountRec coreData25 coreData26 288 = 33 := by
  change persistentCountRec coreData25 coreData26 (256 + 32) = 33
  rw [persistentCountRec_add, prefix_25_26_256]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_320 : persistentCountRec coreData25 coreData26 320 = 37 := by
  change persistentCountRec coreData25 coreData26 (288 + 32) = 37
  rw [persistentCountRec_add, prefix_25_26_288]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_352 : persistentCountRec coreData25 coreData26 352 = 41 := by
  change persistentCountRec coreData25 coreData26 (320 + 32) = 41
  rw [persistentCountRec_add, prefix_25_26_320]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_384 : persistentCountRec coreData25 coreData26 384 = 44 := by
  change persistentCountRec coreData25 coreData26 (352 + 32) = 44
  rw [persistentCountRec_add, prefix_25_26_352]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_416 : persistentCountRec coreData25 coreData26 416 = 45 := by
  change persistentCountRec coreData25 coreData26 (384 + 32) = 45
  rw [persistentCountRec_add, prefix_25_26_384]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_448 : persistentCountRec coreData25 coreData26 448 = 49 := by
  change persistentCountRec coreData25 coreData26 (416 + 32) = 49
  rw [persistentCountRec_add, prefix_25_26_416]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_480 : persistentCountRec coreData25 coreData26 480 = 52 := by
  change persistentCountRec coreData25 coreData26 (448 + 32) = 52
  rw [persistentCountRec_add, prefix_25_26_448]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_512 : persistentCountRec coreData25 coreData26 512 = 55 := by
  change persistentCountRec coreData25 coreData26 (480 + 32) = 55
  rw [persistentCountRec_add, prefix_25_26_480]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_544 : persistentCountRec coreData25 coreData26 544 = 57 := by
  change persistentCountRec coreData25 coreData26 (512 + 32) = 57
  rw [persistentCountRec_add, prefix_25_26_512]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_576 : persistentCountRec coreData25 coreData26 576 = 59 := by
  change persistentCountRec coreData25 coreData26 (544 + 32) = 59
  rw [persistentCountRec_add, prefix_25_26_544]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_608 : persistentCountRec coreData25 coreData26 608 = 60 := by
  change persistentCountRec coreData25 coreData26 (576 + 32) = 60
  rw [persistentCountRec_add, prefix_25_26_576]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_25_26_625 : persistentCountRec coreData25 coreData26 625 = 61 := by
  change persistentCountRec coreData25 coreData26 (608 + 17) = 61
  rw [persistentCountRec_add, prefix_25_26_608]
  simp only [persistentSegment]
  decide +kernel

theorem ell_25_26 : ell 25 26 = 61 := by
  rw [ell_eq_persistentCount, core_25, core_26, persistentCount_eq_rec]
  exact prefix_25_26_625

private theorem prefix_27_27_32 : persistentCountRec coreData27 coreData27 32 = 7 := by
  simp only [persistentCountRec]
  decide +kernel

private theorem prefix_27_27_64 : persistentCountRec coreData27 coreData27 64 = 12 := by
  change persistentCountRec coreData27 coreData27 (32 + 32) = 12
  rw [persistentCountRec_add, prefix_27_27_32]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_96 : persistentCountRec coreData27 coreData27 96 = 15 := by
  change persistentCountRec coreData27 coreData27 (64 + 32) = 15
  rw [persistentCountRec_add, prefix_27_27_64]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_128 : persistentCountRec coreData27 coreData27 128 = 21 := by
  change persistentCountRec coreData27 coreData27 (96 + 32) = 21
  rw [persistentCountRec_add, prefix_27_27_96]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_160 : persistentCountRec coreData27 coreData27 160 = 23 := by
  change persistentCountRec coreData27 coreData27 (128 + 32) = 23
  rw [persistentCountRec_add, prefix_27_27_128]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_192 : persistentCountRec coreData27 coreData27 192 = 26 := by
  change persistentCountRec coreData27 coreData27 (160 + 32) = 26
  rw [persistentCountRec_add, prefix_27_27_160]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_224 : persistentCountRec coreData27 coreData27 224 = 29 := by
  change persistentCountRec coreData27 coreData27 (192 + 32) = 29
  rw [persistentCountRec_add, prefix_27_27_192]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_256 : persistentCountRec coreData27 coreData27 256 = 34 := by
  change persistentCountRec coreData27 coreData27 (224 + 32) = 34
  rw [persistentCountRec_add, prefix_27_27_224]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_288 : persistentCountRec coreData27 coreData27 288 = 37 := by
  change persistentCountRec coreData27 coreData27 (256 + 32) = 37
  rw [persistentCountRec_add, prefix_27_27_256]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_320 : persistentCountRec coreData27 coreData27 320 = 42 := by
  change persistentCountRec coreData27 coreData27 (288 + 32) = 42
  rw [persistentCountRec_add, prefix_27_27_288]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_352 : persistentCountRec coreData27 coreData27 352 = 48 := by
  change persistentCountRec coreData27 coreData27 (320 + 32) = 48
  rw [persistentCountRec_add, prefix_27_27_320]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_384 : persistentCountRec coreData27 coreData27 384 = 51 := by
  change persistentCountRec coreData27 coreData27 (352 + 32) = 51
  rw [persistentCountRec_add, prefix_27_27_352]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_416 : persistentCountRec coreData27 coreData27 416 = 55 := by
  change persistentCountRec coreData27 coreData27 (384 + 32) = 55
  rw [persistentCountRec_add, prefix_27_27_384]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_448 : persistentCountRec coreData27 coreData27 448 = 58 := by
  change persistentCountRec coreData27 coreData27 (416 + 32) = 58
  rw [persistentCountRec_add, prefix_27_27_416]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_480 : persistentCountRec coreData27 coreData27 480 = 62 := by
  change persistentCountRec coreData27 coreData27 (448 + 32) = 62
  rw [persistentCountRec_add, prefix_27_27_448]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_512 : persistentCountRec coreData27 coreData27 512 = 66 := by
  change persistentCountRec coreData27 coreData27 (480 + 32) = 66
  rw [persistentCountRec_add, prefix_27_27_480]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_544 : persistentCountRec coreData27 coreData27 544 = 70 := by
  change persistentCountRec coreData27 coreData27 (512 + 32) = 70
  rw [persistentCountRec_add, prefix_27_27_512]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_576 : persistentCountRec coreData27 coreData27 576 = 75 := by
  change persistentCountRec coreData27 coreData27 (544 + 32) = 75
  rw [persistentCountRec_add, prefix_27_27_544]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_608 : persistentCountRec coreData27 coreData27 608 = 77 := by
  change persistentCountRec coreData27 coreData27 (576 + 32) = 77
  rw [persistentCountRec_add, prefix_27_27_576]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_640 : persistentCountRec coreData27 coreData27 640 = 79 := by
  change persistentCountRec coreData27 coreData27 (608 + 32) = 79
  rw [persistentCountRec_add, prefix_27_27_608]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_672 : persistentCountRec coreData27 coreData27 672 = 81 := by
  change persistentCountRec coreData27 coreData27 (640 + 32) = 81
  rw [persistentCountRec_add, prefix_27_27_640]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_704 : persistentCountRec coreData27 coreData27 704 = 84 := by
  change persistentCountRec coreData27 coreData27 (672 + 32) = 84
  rw [persistentCountRec_add, prefix_27_27_672]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_27_27_729 : persistentCountRec coreData27 coreData27 729 = 85 := by
  change persistentCountRec coreData27 coreData27 (704 + 25) = 85
  rw [persistentCountRec_add, prefix_27_27_704]
  simp only [persistentSegment]
  decide +kernel

theorem ell_27_27 : ell 27 27 = 85 := by
  rw [ell_eq_persistentCount, core_27, persistentCount_eq_rec]
  exact prefix_27_27_729

private theorem prefix_28_28_32 : persistentCountRec coreData28 coreData28 32 = 7 := by
  simp only [persistentCountRec]
  decide +kernel

private theorem prefix_28_28_64 : persistentCountRec coreData28 coreData28 64 = 12 := by
  change persistentCountRec coreData28 coreData28 (32 + 32) = 12
  rw [persistentCountRec_add, prefix_28_28_32]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_96 : persistentCountRec coreData28 coreData28 96 = 15 := by
  change persistentCountRec coreData28 coreData28 (64 + 32) = 15
  rw [persistentCountRec_add, prefix_28_28_64]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_128 : persistentCountRec coreData28 coreData28 128 = 21 := by
  change persistentCountRec coreData28 coreData28 (96 + 32) = 21
  rw [persistentCountRec_add, prefix_28_28_96]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_160 : persistentCountRec coreData28 coreData28 160 = 23 := by
  change persistentCountRec coreData28 coreData28 (128 + 32) = 23
  rw [persistentCountRec_add, prefix_28_28_128]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_192 : persistentCountRec coreData28 coreData28 192 = 26 := by
  change persistentCountRec coreData28 coreData28 (160 + 32) = 26
  rw [persistentCountRec_add, prefix_28_28_160]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_224 : persistentCountRec coreData28 coreData28 224 = 27 := by
  change persistentCountRec coreData28 coreData28 (192 + 32) = 27
  rw [persistentCountRec_add, prefix_28_28_192]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_256 : persistentCountRec coreData28 coreData28 256 = 32 := by
  change persistentCountRec coreData28 coreData28 (224 + 32) = 32
  rw [persistentCountRec_add, prefix_28_28_224]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_288 : persistentCountRec coreData28 coreData28 288 = 34 := by
  change persistentCountRec coreData28 coreData28 (256 + 32) = 34
  rw [persistentCountRec_add, prefix_28_28_256]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_320 : persistentCountRec coreData28 coreData28 320 = 38 := by
  change persistentCountRec coreData28 coreData28 (288 + 32) = 38
  rw [persistentCountRec_add, prefix_28_28_288]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_352 : persistentCountRec coreData28 coreData28 352 = 44 := by
  change persistentCountRec coreData28 coreData28 (320 + 32) = 44
  rw [persistentCountRec_add, prefix_28_28_320]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_384 : persistentCountRec coreData28 coreData28 384 = 46 := by
  change persistentCountRec coreData28 coreData28 (352 + 32) = 46
  rw [persistentCountRec_add, prefix_28_28_352]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_416 : persistentCountRec coreData28 coreData28 416 = 51 := by
  change persistentCountRec coreData28 coreData28 (384 + 32) = 51
  rw [persistentCountRec_add, prefix_28_28_384]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_448 : persistentCountRec coreData28 coreData28 448 = 54 := by
  change persistentCountRec coreData28 coreData28 (416 + 32) = 54
  rw [persistentCountRec_add, prefix_28_28_416]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_480 : persistentCountRec coreData28 coreData28 480 = 58 := by
  change persistentCountRec coreData28 coreData28 (448 + 32) = 58
  rw [persistentCountRec_add, prefix_28_28_448]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_512 : persistentCountRec coreData28 coreData28 512 = 61 := by
  change persistentCountRec coreData28 coreData28 (480 + 32) = 61
  rw [persistentCountRec_add, prefix_28_28_480]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_544 : persistentCountRec coreData28 coreData28 544 = 65 := by
  change persistentCountRec coreData28 coreData28 (512 + 32) = 65
  rw [persistentCountRec_add, prefix_28_28_512]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_576 : persistentCountRec coreData28 coreData28 576 = 71 := by
  change persistentCountRec coreData28 coreData28 (544 + 32) = 71
  rw [persistentCountRec_add, prefix_28_28_544]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_608 : persistentCountRec coreData28 coreData28 608 = 74 := by
  change persistentCountRec coreData28 coreData28 (576 + 32) = 74
  rw [persistentCountRec_add, prefix_28_28_576]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_640 : persistentCountRec coreData28 coreData28 640 = 77 := by
  change persistentCountRec coreData28 coreData28 (608 + 32) = 77
  rw [persistentCountRec_add, prefix_28_28_608]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_672 : persistentCountRec coreData28 coreData28 672 = 80 := by
  change persistentCountRec coreData28 coreData28 (640 + 32) = 80
  rw [persistentCountRec_add, prefix_28_28_640]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_704 : persistentCountRec coreData28 coreData28 704 = 84 := by
  change persistentCountRec coreData28 coreData28 (672 + 32) = 84
  rw [persistentCountRec_add, prefix_28_28_672]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_736 : persistentCountRec coreData28 coreData28 736 = 86 := by
  change persistentCountRec coreData28 coreData28 (704 + 32) = 86
  rw [persistentCountRec_add, prefix_28_28_704]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_768 : persistentCountRec coreData28 coreData28 768 = 87 := by
  change persistentCountRec coreData28 coreData28 (736 + 32) = 87
  rw [persistentCountRec_add, prefix_28_28_736]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_28_28_784 : persistentCountRec coreData28 coreData28 784 = 88 := by
  change persistentCountRec coreData28 coreData28 (768 + 16) = 88
  rw [persistentCountRec_add, prefix_28_28_768]
  simp only [persistentSegment]
  decide +kernel

theorem ell_28_28 : ell 28 28 = 88 := by
  rw [ell_eq_persistentCount, core_28, persistentCount_eq_rec]
  exact prefix_28_28_784

private theorem prefix_29_33_32 : persistentCountRec coreData29 coreData33 32 = 7 := by
  simp only [persistentCountRec]
  decide +kernel

private theorem prefix_29_33_64 : persistentCountRec coreData29 coreData33 64 = 11 := by
  change persistentCountRec coreData29 coreData33 (32 + 32) = 11
  rw [persistentCountRec_add, prefix_29_33_32]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_96 : persistentCountRec coreData29 coreData33 96 = 14 := by
  change persistentCountRec coreData29 coreData33 (64 + 32) = 14
  rw [persistentCountRec_add, prefix_29_33_64]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_128 : persistentCountRec coreData29 coreData33 128 = 18 := by
  change persistentCountRec coreData29 coreData33 (96 + 32) = 18
  rw [persistentCountRec_add, prefix_29_33_96]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_160 : persistentCountRec coreData29 coreData33 160 = 20 := by
  change persistentCountRec coreData29 coreData33 (128 + 32) = 20
  rw [persistentCountRec_add, prefix_29_33_128]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_192 : persistentCountRec coreData29 coreData33 192 = 22 := by
  change persistentCountRec coreData29 coreData33 (160 + 32) = 22
  rw [persistentCountRec_add, prefix_29_33_160]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_224 : persistentCountRec coreData29 coreData33 224 = 23 := by
  change persistentCountRec coreData29 coreData33 (192 + 32) = 23
  rw [persistentCountRec_add, prefix_29_33_192]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_256 : persistentCountRec coreData29 coreData33 256 = 26 := by
  change persistentCountRec coreData29 coreData33 (224 + 32) = 26
  rw [persistentCountRec_add, prefix_29_33_224]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_288 : persistentCountRec coreData29 coreData33 288 = 28 := by
  change persistentCountRec coreData29 coreData33 (256 + 32) = 28
  rw [persistentCountRec_add, prefix_29_33_256]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_320 : persistentCountRec coreData29 coreData33 320 = 30 := by
  change persistentCountRec coreData29 coreData33 (288 + 32) = 30
  rw [persistentCountRec_add, prefix_29_33_288]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_352 : persistentCountRec coreData29 coreData33 352 = 34 := by
  change persistentCountRec coreData29 coreData33 (320 + 32) = 34
  rw [persistentCountRec_add, prefix_29_33_320]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_384 : persistentCountRec coreData29 coreData33 384 = 35 := by
  change persistentCountRec coreData29 coreData33 (352 + 32) = 35
  rw [persistentCountRec_add, prefix_29_33_352]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_416 : persistentCountRec coreData29 coreData33 416 = 37 := by
  change persistentCountRec coreData29 coreData33 (384 + 32) = 37
  rw [persistentCountRec_add, prefix_29_33_384]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_448 : persistentCountRec coreData29 coreData33 448 = 39 := by
  change persistentCountRec coreData29 coreData33 (416 + 32) = 39
  rw [persistentCountRec_add, prefix_29_33_416]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_480 : persistentCountRec coreData29 coreData33 480 = 40 := by
  change persistentCountRec coreData29 coreData33 (448 + 32) = 40
  rw [persistentCountRec_add, prefix_29_33_448]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_512 : persistentCountRec coreData29 coreData33 512 = 43 := by
  change persistentCountRec coreData29 coreData33 (480 + 32) = 43
  rw [persistentCountRec_add, prefix_29_33_480]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_544 : persistentCountRec coreData29 coreData33 544 = 45 := by
  change persistentCountRec coreData29 coreData33 (512 + 32) = 45
  rw [persistentCountRec_add, prefix_29_33_512]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_576 : persistentCountRec coreData29 coreData33 576 = 50 := by
  change persistentCountRec coreData29 coreData33 (544 + 32) = 50
  rw [persistentCountRec_add, prefix_29_33_544]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_608 : persistentCountRec coreData29 coreData33 608 = 51 := by
  change persistentCountRec coreData29 coreData33 (576 + 32) = 51
  rw [persistentCountRec_add, prefix_29_33_576]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_640 : persistentCountRec coreData29 coreData33 640 = 54 := by
  change persistentCountRec coreData29 coreData33 (608 + 32) = 54
  rw [persistentCountRec_add, prefix_29_33_608]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_672 : persistentCountRec coreData29 coreData33 672 = 56 := by
  change persistentCountRec coreData29 coreData33 (640 + 32) = 56
  rw [persistentCountRec_add, prefix_29_33_640]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_704 : persistentCountRec coreData29 coreData33 704 = 60 := by
  change persistentCountRec coreData29 coreData33 (672 + 32) = 60
  rw [persistentCountRec_add, prefix_29_33_672]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_736 : persistentCountRec coreData29 coreData33 736 = 62 := by
  change persistentCountRec coreData29 coreData33 (704 + 32) = 62
  rw [persistentCountRec_add, prefix_29_33_704]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_768 : persistentCountRec coreData29 coreData33 768 = 63 := by
  change persistentCountRec coreData29 coreData33 (736 + 32) = 63
  rw [persistentCountRec_add, prefix_29_33_736]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_800 : persistentCountRec coreData29 coreData33 800 = 64 := by
  change persistentCountRec coreData29 coreData33 (768 + 32) = 64
  rw [persistentCountRec_add, prefix_29_33_768]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_832 : persistentCountRec coreData29 coreData33 832 = 64 := by
  change persistentCountRec coreData29 coreData33 (800 + 32) = 64
  rw [persistentCountRec_add, prefix_29_33_800]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_29_33_841 : persistentCountRec coreData29 coreData33 841 = 64 := by
  change persistentCountRec coreData29 coreData33 (832 + 9) = 64
  rw [persistentCountRec_add, prefix_29_33_832]
  simp only [persistentSegment]
  decide +kernel

theorem ell_29_33 : ell 29 33 = 64 := by
  rw [ell_eq_persistentCount, core_29, core_33, persistentCount_eq_rec]
  exact prefix_29_33_841

private theorem prefix_34_37_32 : persistentCountRec coreData34 coreData37 32 = 8 := by
  simp only [persistentCountRec]
  decide +kernel

private theorem prefix_34_37_64 : persistentCountRec coreData34 coreData37 64 = 12 := by
  change persistentCountRec coreData34 coreData37 (32 + 32) = 12
  rw [persistentCountRec_add, prefix_34_37_32]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_96 : persistentCountRec coreData34 coreData37 96 = 16 := by
  change persistentCountRec coreData34 coreData37 (64 + 32) = 16
  rw [persistentCountRec_add, prefix_34_37_64]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_128 : persistentCountRec coreData34 coreData37 128 = 21 := by
  change persistentCountRec coreData34 coreData37 (96 + 32) = 21
  rw [persistentCountRec_add, prefix_34_37_96]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_160 : persistentCountRec coreData34 coreData37 160 = 24 := by
  change persistentCountRec coreData34 coreData37 (128 + 32) = 24
  rw [persistentCountRec_add, prefix_34_37_128]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_192 : persistentCountRec coreData34 coreData37 192 = 26 := by
  change persistentCountRec coreData34 coreData37 (160 + 32) = 26
  rw [persistentCountRec_add, prefix_34_37_160]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_224 : persistentCountRec coreData34 coreData37 224 = 28 := by
  change persistentCountRec coreData34 coreData37 (192 + 32) = 28
  rw [persistentCountRec_add, prefix_34_37_192]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_256 : persistentCountRec coreData34 coreData37 256 = 32 := by
  change persistentCountRec coreData34 coreData37 (224 + 32) = 32
  rw [persistentCountRec_add, prefix_34_37_224]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_288 : persistentCountRec coreData34 coreData37 288 = 34 := by
  change persistentCountRec coreData34 coreData37 (256 + 32) = 34
  rw [persistentCountRec_add, prefix_34_37_256]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_320 : persistentCountRec coreData34 coreData37 320 = 36 := by
  change persistentCountRec coreData34 coreData37 (288 + 32) = 36
  rw [persistentCountRec_add, prefix_34_37_288]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_352 : persistentCountRec coreData34 coreData37 352 = 39 := by
  change persistentCountRec coreData34 coreData37 (320 + 32) = 39
  rw [persistentCountRec_add, prefix_34_37_320]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_384 : persistentCountRec coreData34 coreData37 384 = 42 := by
  change persistentCountRec coreData34 coreData37 (352 + 32) = 42
  rw [persistentCountRec_add, prefix_34_37_352]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_416 : persistentCountRec coreData34 coreData37 416 = 44 := by
  change persistentCountRec coreData34 coreData37 (384 + 32) = 44
  rw [persistentCountRec_add, prefix_34_37_384]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_448 : persistentCountRec coreData34 coreData37 448 = 48 := by
  change persistentCountRec coreData34 coreData37 (416 + 32) = 48
  rw [persistentCountRec_add, prefix_34_37_416]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_480 : persistentCountRec coreData34 coreData37 480 = 49 := by
  change persistentCountRec coreData34 coreData37 (448 + 32) = 49
  rw [persistentCountRec_add, prefix_34_37_448]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_512 : persistentCountRec coreData34 coreData37 512 = 54 := by
  change persistentCountRec coreData34 coreData37 (480 + 32) = 54
  rw [persistentCountRec_add, prefix_34_37_480]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_544 : persistentCountRec coreData34 coreData37 544 = 55 := by
  change persistentCountRec coreData34 coreData37 (512 + 32) = 55
  rw [persistentCountRec_add, prefix_34_37_512]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_576 : persistentCountRec coreData34 coreData37 576 = 60 := by
  change persistentCountRec coreData34 coreData37 (544 + 32) = 60
  rw [persistentCountRec_add, prefix_34_37_544]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_608 : persistentCountRec coreData34 coreData37 608 = 62 := by
  change persistentCountRec coreData34 coreData37 (576 + 32) = 62
  rw [persistentCountRec_add, prefix_34_37_576]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_640 : persistentCountRec coreData34 coreData37 640 = 66 := by
  change persistentCountRec coreData34 coreData37 (608 + 32) = 66
  rw [persistentCountRec_add, prefix_34_37_608]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_672 : persistentCountRec coreData34 coreData37 672 = 67 := by
  change persistentCountRec coreData34 coreData37 (640 + 32) = 67
  rw [persistentCountRec_add, prefix_34_37_640]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_704 : persistentCountRec coreData34 coreData37 704 = 73 := by
  change persistentCountRec coreData34 coreData37 (672 + 32) = 73
  rw [persistentCountRec_add, prefix_34_37_672]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_736 : persistentCountRec coreData34 coreData37 736 = 77 := by
  change persistentCountRec coreData34 coreData37 (704 + 32) = 77
  rw [persistentCountRec_add, prefix_34_37_704]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_768 : persistentCountRec coreData34 coreData37 768 = 80 := by
  change persistentCountRec coreData34 coreData37 (736 + 32) = 80
  rw [persistentCountRec_add, prefix_34_37_736]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_800 : persistentCountRec coreData34 coreData37 800 = 83 := by
  change persistentCountRec coreData34 coreData37 (768 + 32) = 83
  rw [persistentCountRec_add, prefix_34_37_768]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_832 : persistentCountRec coreData34 coreData37 832 = 87 := by
  change persistentCountRec coreData34 coreData37 (800 + 32) = 87
  rw [persistentCountRec_add, prefix_34_37_800]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_864 : persistentCountRec coreData34 coreData37 864 = 89 := by
  change persistentCountRec coreData34 coreData37 (832 + 32) = 89
  rw [persistentCountRec_add, prefix_34_37_832]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_896 : persistentCountRec coreData34 coreData37 896 = 92 := by
  change persistentCountRec coreData34 coreData37 (864 + 32) = 92
  rw [persistentCountRec_add, prefix_34_37_864]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_928 : persistentCountRec coreData34 coreData37 928 = 94 := by
  change persistentCountRec coreData34 coreData37 (896 + 32) = 94
  rw [persistentCountRec_add, prefix_34_37_896]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_960 : persistentCountRec coreData34 coreData37 960 = 96 := by
  change persistentCountRec coreData34 coreData37 (928 + 32) = 96
  rw [persistentCountRec_add, prefix_34_37_928]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_992 : persistentCountRec coreData34 coreData37 992 = 97 := by
  change persistentCountRec coreData34 coreData37 (960 + 32) = 97
  rw [persistentCountRec_add, prefix_34_37_960]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_1024 : persistentCountRec coreData34 coreData37 1024 = 99 := by
  change persistentCountRec coreData34 coreData37 (992 + 32) = 99
  rw [persistentCountRec_add, prefix_34_37_992]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_1056 : persistentCountRec coreData34 coreData37 1056 = 100 := by
  change persistentCountRec coreData34 coreData37 (1024 + 32) = 100
  rw [persistentCountRec_add, prefix_34_37_1024]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_1088 : persistentCountRec coreData34 coreData37 1088 = 101 := by
  change persistentCountRec coreData34 coreData37 (1056 + 32) = 101
  rw [persistentCountRec_add, prefix_34_37_1056]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_1120 : persistentCountRec coreData34 coreData37 1120 = 102 := by
  change persistentCountRec coreData34 coreData37 (1088 + 32) = 102
  rw [persistentCountRec_add, prefix_34_37_1088]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_1152 : persistentCountRec coreData34 coreData37 1152 = 103 := by
  change persistentCountRec coreData34 coreData37 (1120 + 32) = 103
  rw [persistentCountRec_add, prefix_34_37_1120]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_34_37_1156 : persistentCountRec coreData34 coreData37 1156 = 104 := by
  change persistentCountRec coreData34 coreData37 (1152 + 4) = 104
  rw [persistentCountRec_add, prefix_34_37_1152]
  simp only [persistentSegment]
  decide +kernel

theorem ell_34_37 : ell 34 37 = 104 := by
  rw [ell_eq_persistentCount, core_34, core_37, persistentCount_eq_rec]
  exact prefix_34_37_1156

private theorem prefix_38_50_32 : persistentCountRec coreData38 coreData50 32 = 9 := by
  simp only [persistentCountRec]
  decide +kernel

private theorem prefix_38_50_64 : persistentCountRec coreData38 coreData50 64 = 12 := by
  change persistentCountRec coreData38 coreData50 (32 + 32) = 12
  rw [persistentCountRec_add, prefix_38_50_32]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_96 : persistentCountRec coreData38 coreData50 96 = 17 := by
  change persistentCountRec coreData38 coreData50 (64 + 32) = 17
  rw [persistentCountRec_add, prefix_38_50_64]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_128 : persistentCountRec coreData38 coreData50 128 = 20 := by
  change persistentCountRec coreData38 coreData50 (96 + 32) = 20
  rw [persistentCountRec_add, prefix_38_50_96]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_160 : persistentCountRec coreData38 coreData50 160 = 23 := by
  change persistentCountRec coreData38 coreData50 (128 + 32) = 23
  rw [persistentCountRec_add, prefix_38_50_128]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_192 : persistentCountRec coreData38 coreData50 192 = 26 := by
  change persistentCountRec coreData38 coreData50 (160 + 32) = 26
  rw [persistentCountRec_add, prefix_38_50_160]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_224 : persistentCountRec coreData38 coreData50 224 = 28 := by
  change persistentCountRec coreData38 coreData50 (192 + 32) = 28
  rw [persistentCountRec_add, prefix_38_50_192]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_256 : persistentCountRec coreData38 coreData50 256 = 32 := by
  change persistentCountRec coreData38 coreData50 (224 + 32) = 32
  rw [persistentCountRec_add, prefix_38_50_224]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_288 : persistentCountRec coreData38 coreData50 288 = 34 := by
  change persistentCountRec coreData38 coreData50 (256 + 32) = 34
  rw [persistentCountRec_add, prefix_38_50_256]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_320 : persistentCountRec coreData38 coreData50 320 = 35 := by
  change persistentCountRec coreData38 coreData50 (288 + 32) = 35
  rw [persistentCountRec_add, prefix_38_50_288]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_352 : persistentCountRec coreData38 coreData50 352 = 38 := by
  change persistentCountRec coreData38 coreData50 (320 + 32) = 38
  rw [persistentCountRec_add, prefix_38_50_320]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_384 : persistentCountRec coreData38 coreData50 384 = 42 := by
  change persistentCountRec coreData38 coreData50 (352 + 32) = 42
  rw [persistentCountRec_add, prefix_38_50_352]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_416 : persistentCountRec coreData38 coreData50 416 = 44 := by
  change persistentCountRec coreData38 coreData50 (384 + 32) = 44
  rw [persistentCountRec_add, prefix_38_50_384]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_448 : persistentCountRec coreData38 coreData50 448 = 45 := by
  change persistentCountRec coreData38 coreData50 (416 + 32) = 45
  rw [persistentCountRec_add, prefix_38_50_416]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_480 : persistentCountRec coreData38 coreData50 480 = 48 := by
  change persistentCountRec coreData38 coreData50 (448 + 32) = 48
  rw [persistentCountRec_add, prefix_38_50_448]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_512 : persistentCountRec coreData38 coreData50 512 = 50 := by
  change persistentCountRec coreData38 coreData50 (480 + 32) = 50
  rw [persistentCountRec_add, prefix_38_50_480]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_544 : persistentCountRec coreData38 coreData50 544 = 51 := by
  change persistentCountRec coreData38 coreData50 (512 + 32) = 51
  rw [persistentCountRec_add, prefix_38_50_512]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_576 : persistentCountRec coreData38 coreData50 576 = 53 := by
  change persistentCountRec coreData38 coreData50 (544 + 32) = 53
  rw [persistentCountRec_add, prefix_38_50_544]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_608 : persistentCountRec coreData38 coreData50 608 = 55 := by
  change persistentCountRec coreData38 coreData50 (576 + 32) = 55
  rw [persistentCountRec_add, prefix_38_50_576]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_640 : persistentCountRec coreData38 coreData50 640 = 57 := by
  change persistentCountRec coreData38 coreData50 (608 + 32) = 57
  rw [persistentCountRec_add, prefix_38_50_608]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_672 : persistentCountRec coreData38 coreData50 672 = 58 := by
  change persistentCountRec coreData38 coreData50 (640 + 32) = 58
  rw [persistentCountRec_add, prefix_38_50_640]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_704 : persistentCountRec coreData38 coreData50 704 = 60 := by
  change persistentCountRec coreData38 coreData50 (672 + 32) = 60
  rw [persistentCountRec_add, prefix_38_50_672]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_736 : persistentCountRec coreData38 coreData50 736 = 64 := by
  change persistentCountRec coreData38 coreData50 (704 + 32) = 64
  rw [persistentCountRec_add, prefix_38_50_704]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_768 : persistentCountRec coreData38 coreData50 768 = 64 := by
  change persistentCountRec coreData38 coreData50 (736 + 32) = 64
  rw [persistentCountRec_add, prefix_38_50_736]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_800 : persistentCountRec coreData38 coreData50 800 = 65 := by
  change persistentCountRec coreData38 coreData50 (768 + 32) = 65
  rw [persistentCountRec_add, prefix_38_50_768]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_832 : persistentCountRec coreData38 coreData50 832 = 67 := by
  change persistentCountRec coreData38 coreData50 (800 + 32) = 67
  rw [persistentCountRec_add, prefix_38_50_800]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_864 : persistentCountRec coreData38 coreData50 864 = 67 := by
  change persistentCountRec coreData38 coreData50 (832 + 32) = 67
  rw [persistentCountRec_add, prefix_38_50_832]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_896 : persistentCountRec coreData38 coreData50 896 = 71 := by
  change persistentCountRec coreData38 coreData50 (864 + 32) = 71
  rw [persistentCountRec_add, prefix_38_50_864]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_928 : persistentCountRec coreData38 coreData50 928 = 73 := by
  change persistentCountRec coreData38 coreData50 (896 + 32) = 73
  rw [persistentCountRec_add, prefix_38_50_896]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_960 : persistentCountRec coreData38 coreData50 960 = 74 := by
  change persistentCountRec coreData38 coreData50 (928 + 32) = 74
  rw [persistentCountRec_add, prefix_38_50_928]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_992 : persistentCountRec coreData38 coreData50 992 = 76 := by
  change persistentCountRec coreData38 coreData50 (960 + 32) = 76
  rw [persistentCountRec_add, prefix_38_50_960]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1024 : persistentCountRec coreData38 coreData50 1024 = 78 := by
  change persistentCountRec coreData38 coreData50 (992 + 32) = 78
  rw [persistentCountRec_add, prefix_38_50_992]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1056 : persistentCountRec coreData38 coreData50 1056 = 79 := by
  change persistentCountRec coreData38 coreData50 (1024 + 32) = 79
  rw [persistentCountRec_add, prefix_38_50_1024]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1088 : persistentCountRec coreData38 coreData50 1088 = 81 := by
  change persistentCountRec coreData38 coreData50 (1056 + 32) = 81
  rw [persistentCountRec_add, prefix_38_50_1056]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1120 : persistentCountRec coreData38 coreData50 1120 = 82 := by
  change persistentCountRec coreData38 coreData50 (1088 + 32) = 82
  rw [persistentCountRec_add, prefix_38_50_1088]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1152 : persistentCountRec coreData38 coreData50 1152 = 84 := by
  change persistentCountRec coreData38 coreData50 (1120 + 32) = 84
  rw [persistentCountRec_add, prefix_38_50_1120]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1184 : persistentCountRec coreData38 coreData50 1184 = 86 := by
  change persistentCountRec coreData38 coreData50 (1152 + 32) = 86
  rw [persistentCountRec_add, prefix_38_50_1152]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1216 : persistentCountRec coreData38 coreData50 1216 = 88 := by
  change persistentCountRec coreData38 coreData50 (1184 + 32) = 88
  rw [persistentCountRec_add, prefix_38_50_1184]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1248 : persistentCountRec coreData38 coreData50 1248 = 89 := by
  change persistentCountRec coreData38 coreData50 (1216 + 32) = 89
  rw [persistentCountRec_add, prefix_38_50_1216]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1280 : persistentCountRec coreData38 coreData50 1280 = 90 := by
  change persistentCountRec coreData38 coreData50 (1248 + 32) = 90
  rw [persistentCountRec_add, prefix_38_50_1248]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1312 : persistentCountRec coreData38 coreData50 1312 = 91 := by
  change persistentCountRec coreData38 coreData50 (1280 + 32) = 91
  rw [persistentCountRec_add, prefix_38_50_1280]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1344 : persistentCountRec coreData38 coreData50 1344 = 92 := by
  change persistentCountRec coreData38 coreData50 (1312 + 32) = 92
  rw [persistentCountRec_add, prefix_38_50_1312]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1376 : persistentCountRec coreData38 coreData50 1376 = 93 := by
  change persistentCountRec coreData38 coreData50 (1344 + 32) = 93
  rw [persistentCountRec_add, prefix_38_50_1344]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1408 : persistentCountRec coreData38 coreData50 1408 = 93 := by
  change persistentCountRec coreData38 coreData50 (1376 + 32) = 93
  rw [persistentCountRec_add, prefix_38_50_1376]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1440 : persistentCountRec coreData38 coreData50 1440 = 93 := by
  change persistentCountRec coreData38 coreData50 (1408 + 32) = 93
  rw [persistentCountRec_add, prefix_38_50_1408]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_38_50_1444 : persistentCountRec coreData38 coreData50 1444 = 94 := by
  change persistentCountRec coreData38 coreData50 (1440 + 4) = 94
  rw [persistentCountRec_add, prefix_38_50_1440]
  simp only [persistentSegment]
  decide +kernel

theorem ell_38_50 : ell 38 50 = 94 := by
  rw [ell_eq_persistentCount, core_38, core_50, persistentCount_eq_rec]
  exact prefix_38_50_1444

private theorem prefix_51_66_32 : persistentCountRec coreData51 coreData66 32 = 10 := by
  simp only [persistentCountRec]
  decide +kernel

private theorem prefix_51_66_64 : persistentCountRec coreData51 coreData66 64 = 10 := by
  change persistentCountRec coreData51 coreData66 (32 + 32) = 10
  rw [persistentCountRec_add, prefix_51_66_32]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_96 : persistentCountRec coreData51 coreData66 96 = 15 := by
  change persistentCountRec coreData51 coreData66 (64 + 32) = 15
  rw [persistentCountRec_add, prefix_51_66_64]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_128 : persistentCountRec coreData51 coreData66 128 = 19 := by
  change persistentCountRec coreData51 coreData66 (96 + 32) = 19
  rw [persistentCountRec_add, prefix_51_66_96]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_160 : persistentCountRec coreData51 coreData66 160 = 21 := by
  change persistentCountRec coreData51 coreData66 (128 + 32) = 21
  rw [persistentCountRec_add, prefix_51_66_128]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_192 : persistentCountRec coreData51 coreData66 192 = 24 := by
  change persistentCountRec coreData51 coreData66 (160 + 32) = 24
  rw [persistentCountRec_add, prefix_51_66_160]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_224 : persistentCountRec coreData51 coreData66 224 = 27 := by
  change persistentCountRec coreData51 coreData66 (192 + 32) = 27
  rw [persistentCountRec_add, prefix_51_66_192]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_256 : persistentCountRec coreData51 coreData66 256 = 31 := by
  change persistentCountRec coreData51 coreData66 (224 + 32) = 31
  rw [persistentCountRec_add, prefix_51_66_224]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_288 : persistentCountRec coreData51 coreData66 288 = 31 := by
  change persistentCountRec coreData51 coreData66 (256 + 32) = 31
  rw [persistentCountRec_add, prefix_51_66_256]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_320 : persistentCountRec coreData51 coreData66 320 = 33 := by
  change persistentCountRec coreData51 coreData66 (288 + 32) = 33
  rw [persistentCountRec_add, prefix_51_66_288]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_352 : persistentCountRec coreData51 coreData66 352 = 37 := by
  change persistentCountRec coreData51 coreData66 (320 + 32) = 37
  rw [persistentCountRec_add, prefix_51_66_320]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_384 : persistentCountRec coreData51 coreData66 384 = 40 := by
  change persistentCountRec coreData51 coreData66 (352 + 32) = 40
  rw [persistentCountRec_add, prefix_51_66_352]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_416 : persistentCountRec coreData51 coreData66 416 = 41 := by
  change persistentCountRec coreData51 coreData66 (384 + 32) = 41
  rw [persistentCountRec_add, prefix_51_66_384]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_448 : persistentCountRec coreData51 coreData66 448 = 43 := by
  change persistentCountRec coreData51 coreData66 (416 + 32) = 43
  rw [persistentCountRec_add, prefix_51_66_416]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_480 : persistentCountRec coreData51 coreData66 480 = 44 := by
  change persistentCountRec coreData51 coreData66 (448 + 32) = 44
  rw [persistentCountRec_add, prefix_51_66_448]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_512 : persistentCountRec coreData51 coreData66 512 = 46 := by
  change persistentCountRec coreData51 coreData66 (480 + 32) = 46
  rw [persistentCountRec_add, prefix_51_66_480]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_544 : persistentCountRec coreData51 coreData66 544 = 48 := by
  change persistentCountRec coreData51 coreData66 (512 + 32) = 48
  rw [persistentCountRec_add, prefix_51_66_512]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_576 : persistentCountRec coreData51 coreData66 576 = 49 := by
  change persistentCountRec coreData51 coreData66 (544 + 32) = 49
  rw [persistentCountRec_add, prefix_51_66_544]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_608 : persistentCountRec coreData51 coreData66 608 = 51 := by
  change persistentCountRec coreData51 coreData66 (576 + 32) = 51
  rw [persistentCountRec_add, prefix_51_66_576]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_640 : persistentCountRec coreData51 coreData66 640 = 54 := by
  change persistentCountRec coreData51 coreData66 (608 + 32) = 54
  rw [persistentCountRec_add, prefix_51_66_608]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_672 : persistentCountRec coreData51 coreData66 672 = 55 := by
  change persistentCountRec coreData51 coreData66 (640 + 32) = 55
  rw [persistentCountRec_add, prefix_51_66_640]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_704 : persistentCountRec coreData51 coreData66 704 = 56 := by
  change persistentCountRec coreData51 coreData66 (672 + 32) = 56
  rw [persistentCountRec_add, prefix_51_66_672]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_736 : persistentCountRec coreData51 coreData66 736 = 58 := by
  change persistentCountRec coreData51 coreData66 (704 + 32) = 58
  rw [persistentCountRec_add, prefix_51_66_704]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_768 : persistentCountRec coreData51 coreData66 768 = 59 := by
  change persistentCountRec coreData51 coreData66 (736 + 32) = 59
  rw [persistentCountRec_add, prefix_51_66_736]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_800 : persistentCountRec coreData51 coreData66 800 = 59 := by
  change persistentCountRec coreData51 coreData66 (768 + 32) = 59
  rw [persistentCountRec_add, prefix_51_66_768]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_832 : persistentCountRec coreData51 coreData66 832 = 60 := by
  change persistentCountRec coreData51 coreData66 (800 + 32) = 60
  rw [persistentCountRec_add, prefix_51_66_800]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_864 : persistentCountRec coreData51 coreData66 864 = 61 := by
  change persistentCountRec coreData51 coreData66 (832 + 32) = 61
  rw [persistentCountRec_add, prefix_51_66_832]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_896 : persistentCountRec coreData51 coreData66 896 = 64 := by
  change persistentCountRec coreData51 coreData66 (864 + 32) = 64
  rw [persistentCountRec_add, prefix_51_66_864]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_928 : persistentCountRec coreData51 coreData66 928 = 65 := by
  change persistentCountRec coreData51 coreData66 (896 + 32) = 65
  rw [persistentCountRec_add, prefix_51_66_896]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_960 : persistentCountRec coreData51 coreData66 960 = 66 := by
  change persistentCountRec coreData51 coreData66 (928 + 32) = 66
  rw [persistentCountRec_add, prefix_51_66_928]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_992 : persistentCountRec coreData51 coreData66 992 = 67 := by
  change persistentCountRec coreData51 coreData66 (960 + 32) = 67
  rw [persistentCountRec_add, prefix_51_66_960]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1024 : persistentCountRec coreData51 coreData66 1024 = 68 := by
  change persistentCountRec coreData51 coreData66 (992 + 32) = 68
  rw [persistentCountRec_add, prefix_51_66_992]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1056 : persistentCountRec coreData51 coreData66 1056 = 71 := by
  change persistentCountRec coreData51 coreData66 (1024 + 32) = 71
  rw [persistentCountRec_add, prefix_51_66_1024]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1088 : persistentCountRec coreData51 coreData66 1088 = 73 := by
  change persistentCountRec coreData51 coreData66 (1056 + 32) = 73
  rw [persistentCountRec_add, prefix_51_66_1056]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1120 : persistentCountRec coreData51 coreData66 1120 = 74 := by
  change persistentCountRec coreData51 coreData66 (1088 + 32) = 74
  rw [persistentCountRec_add, prefix_51_66_1088]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1152 : persistentCountRec coreData51 coreData66 1152 = 76 := by
  change persistentCountRec coreData51 coreData66 (1120 + 32) = 76
  rw [persistentCountRec_add, prefix_51_66_1120]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1184 : persistentCountRec coreData51 coreData66 1184 = 78 := by
  change persistentCountRec coreData51 coreData66 (1152 + 32) = 78
  rw [persistentCountRec_add, prefix_51_66_1152]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1216 : persistentCountRec coreData51 coreData66 1216 = 80 := by
  change persistentCountRec coreData51 coreData66 (1184 + 32) = 80
  rw [persistentCountRec_add, prefix_51_66_1184]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1248 : persistentCountRec coreData51 coreData66 1248 = 80 := by
  change persistentCountRec coreData51 coreData66 (1216 + 32) = 80
  rw [persistentCountRec_add, prefix_51_66_1216]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1280 : persistentCountRec coreData51 coreData66 1280 = 83 := by
  change persistentCountRec coreData51 coreData66 (1248 + 32) = 83
  rw [persistentCountRec_add, prefix_51_66_1248]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1312 : persistentCountRec coreData51 coreData66 1312 = 85 := by
  change persistentCountRec coreData51 coreData66 (1280 + 32) = 85
  rw [persistentCountRec_add, prefix_51_66_1280]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1344 : persistentCountRec coreData51 coreData66 1344 = 86 := by
  change persistentCountRec coreData51 coreData66 (1312 + 32) = 86
  rw [persistentCountRec_add, prefix_51_66_1312]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1376 : persistentCountRec coreData51 coreData66 1376 = 88 := by
  change persistentCountRec coreData51 coreData66 (1344 + 32) = 88
  rw [persistentCountRec_add, prefix_51_66_1344]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1408 : persistentCountRec coreData51 coreData66 1408 = 89 := by
  change persistentCountRec coreData51 coreData66 (1376 + 32) = 89
  rw [persistentCountRec_add, prefix_51_66_1376]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1440 : persistentCountRec coreData51 coreData66 1440 = 89 := by
  change persistentCountRec coreData51 coreData66 (1408 + 32) = 89
  rw [persistentCountRec_add, prefix_51_66_1408]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1472 : persistentCountRec coreData51 coreData66 1472 = 90 := by
  change persistentCountRec coreData51 coreData66 (1440 + 32) = 90
  rw [persistentCountRec_add, prefix_51_66_1440]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1504 : persistentCountRec coreData51 coreData66 1504 = 91 := by
  change persistentCountRec coreData51 coreData66 (1472 + 32) = 91
  rw [persistentCountRec_add, prefix_51_66_1472]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1536 : persistentCountRec coreData51 coreData66 1536 = 93 := by
  change persistentCountRec coreData51 coreData66 (1504 + 32) = 93
  rw [persistentCountRec_add, prefix_51_66_1504]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1568 : persistentCountRec coreData51 coreData66 1568 = 94 := by
  change persistentCountRec coreData51 coreData66 (1536 + 32) = 94
  rw [persistentCountRec_add, prefix_51_66_1536]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1600 : persistentCountRec coreData51 coreData66 1600 = 94 := by
  change persistentCountRec coreData51 coreData66 (1568 + 32) = 94
  rw [persistentCountRec_add, prefix_51_66_1568]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1632 : persistentCountRec coreData51 coreData66 1632 = 96 := by
  change persistentCountRec coreData51 coreData66 (1600 + 32) = 96
  rw [persistentCountRec_add, prefix_51_66_1600]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1664 : persistentCountRec coreData51 coreData66 1664 = 97 := by
  change persistentCountRec coreData51 coreData66 (1632 + 32) = 97
  rw [persistentCountRec_add, prefix_51_66_1632]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1696 : persistentCountRec coreData51 coreData66 1696 = 100 := by
  change persistentCountRec coreData51 coreData66 (1664 + 32) = 100
  rw [persistentCountRec_add, prefix_51_66_1664]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1728 : persistentCountRec coreData51 coreData66 1728 = 102 := by
  change persistentCountRec coreData51 coreData66 (1696 + 32) = 102
  rw [persistentCountRec_add, prefix_51_66_1696]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1760 : persistentCountRec coreData51 coreData66 1760 = 105 := by
  change persistentCountRec coreData51 coreData66 (1728 + 32) = 105
  rw [persistentCountRec_add, prefix_51_66_1728]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1792 : persistentCountRec coreData51 coreData66 1792 = 106 := by
  change persistentCountRec coreData51 coreData66 (1760 + 32) = 106
  rw [persistentCountRec_add, prefix_51_66_1760]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1824 : persistentCountRec coreData51 coreData66 1824 = 107 := by
  change persistentCountRec coreData51 coreData66 (1792 + 32) = 107
  rw [persistentCountRec_add, prefix_51_66_1792]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1856 : persistentCountRec coreData51 coreData66 1856 = 108 := by
  change persistentCountRec coreData51 coreData66 (1824 + 32) = 108
  rw [persistentCountRec_add, prefix_51_66_1824]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1888 : persistentCountRec coreData51 coreData66 1888 = 109 := by
  change persistentCountRec coreData51 coreData66 (1856 + 32) = 109
  rw [persistentCountRec_add, prefix_51_66_1856]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1920 : persistentCountRec coreData51 coreData66 1920 = 111 := by
  change persistentCountRec coreData51 coreData66 (1888 + 32) = 111
  rw [persistentCountRec_add, prefix_51_66_1888]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1952 : persistentCountRec coreData51 coreData66 1952 = 113 := by
  change persistentCountRec coreData51 coreData66 (1920 + 32) = 113
  rw [persistentCountRec_add, prefix_51_66_1920]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_1984 : persistentCountRec coreData51 coreData66 1984 = 113 := by
  change persistentCountRec coreData51 coreData66 (1952 + 32) = 113
  rw [persistentCountRec_add, prefix_51_66_1952]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2016 : persistentCountRec coreData51 coreData66 2016 = 115 := by
  change persistentCountRec coreData51 coreData66 (1984 + 32) = 115
  rw [persistentCountRec_add, prefix_51_66_1984]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2048 : persistentCountRec coreData51 coreData66 2048 = 117 := by
  change persistentCountRec coreData51 coreData66 (2016 + 32) = 117
  rw [persistentCountRec_add, prefix_51_66_2016]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2080 : persistentCountRec coreData51 coreData66 2080 = 119 := by
  change persistentCountRec coreData51 coreData66 (2048 + 32) = 119
  rw [persistentCountRec_add, prefix_51_66_2048]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2112 : persistentCountRec coreData51 coreData66 2112 = 119 := by
  change persistentCountRec coreData51 coreData66 (2080 + 32) = 119
  rw [persistentCountRec_add, prefix_51_66_2080]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2144 : persistentCountRec coreData51 coreData66 2144 = 120 := by
  change persistentCountRec coreData51 coreData66 (2112 + 32) = 120
  rw [persistentCountRec_add, prefix_51_66_2112]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2176 : persistentCountRec coreData51 coreData66 2176 = 121 := by
  change persistentCountRec coreData51 coreData66 (2144 + 32) = 121
  rw [persistentCountRec_add, prefix_51_66_2144]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2208 : persistentCountRec coreData51 coreData66 2208 = 122 := by
  change persistentCountRec coreData51 coreData66 (2176 + 32) = 122
  rw [persistentCountRec_add, prefix_51_66_2176]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2240 : persistentCountRec coreData51 coreData66 2240 = 122 := by
  change persistentCountRec coreData51 coreData66 (2208 + 32) = 122
  rw [persistentCountRec_add, prefix_51_66_2208]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2272 : persistentCountRec coreData51 coreData66 2272 = 124 := by
  change persistentCountRec coreData51 coreData66 (2240 + 32) = 124
  rw [persistentCountRec_add, prefix_51_66_2240]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2304 : persistentCountRec coreData51 coreData66 2304 = 126 := by
  change persistentCountRec coreData51 coreData66 (2272 + 32) = 126
  rw [persistentCountRec_add, prefix_51_66_2272]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2336 : persistentCountRec coreData51 coreData66 2336 = 126 := by
  change persistentCountRec coreData51 coreData66 (2304 + 32) = 126
  rw [persistentCountRec_add, prefix_51_66_2304]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2368 : persistentCountRec coreData51 coreData66 2368 = 127 := by
  change persistentCountRec coreData51 coreData66 (2336 + 32) = 127
  rw [persistentCountRec_add, prefix_51_66_2336]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2400 : persistentCountRec coreData51 coreData66 2400 = 127 := by
  change persistentCountRec coreData51 coreData66 (2368 + 32) = 127
  rw [persistentCountRec_add, prefix_51_66_2368]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2432 : persistentCountRec coreData51 coreData66 2432 = 128 := by
  change persistentCountRec coreData51 coreData66 (2400 + 32) = 128
  rw [persistentCountRec_add, prefix_51_66_2400]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2464 : persistentCountRec coreData51 coreData66 2464 = 130 := by
  change persistentCountRec coreData51 coreData66 (2432 + 32) = 130
  rw [persistentCountRec_add, prefix_51_66_2432]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2496 : persistentCountRec coreData51 coreData66 2496 = 130 := by
  change persistentCountRec coreData51 coreData66 (2464 + 32) = 130
  rw [persistentCountRec_add, prefix_51_66_2464]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2528 : persistentCountRec coreData51 coreData66 2528 = 132 := by
  change persistentCountRec coreData51 coreData66 (2496 + 32) = 132
  rw [persistentCountRec_add, prefix_51_66_2496]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2560 : persistentCountRec coreData51 coreData66 2560 = 133 := by
  change persistentCountRec coreData51 coreData66 (2528 + 32) = 133
  rw [persistentCountRec_add, prefix_51_66_2528]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2592 : persistentCountRec coreData51 coreData66 2592 = 133 := by
  change persistentCountRec coreData51 coreData66 (2560 + 32) = 133
  rw [persistentCountRec_add, prefix_51_66_2560]
  simp only [persistentSegment]
  decide +kernel

private theorem prefix_51_66_2601 : persistentCountRec coreData51 coreData66 2601 = 134 := by
  change persistentCountRec coreData51 coreData66 (2592 + 9) = 134
  rw [persistentCountRec_add, prefix_51_66_2592]
  simp only [persistentSegment]
  decide +kernel

theorem ell_51_66 : ell 51 66 = 134 := by
  rw [ell_eq_persistentCount, core_51, core_66, persistentCount_eq_rec]
  exact prefix_51_66_2601

/-- Exactly the seven persistent-unique-product entries of `eq:fin-block-budgets`. -/
theorem persistent_unique_product_blocks :
    ell 25 26 = 61 ∧ ell 27 27 = 85 ∧ ell 28 28 = 88 ∧ ell 29 33 = 64 ∧
    ell 34 37 = 104 ∧ ell 38 50 = 94 ∧ ell 51 66 = 134 :=
  ⟨ell_25_26, ell_27_27, ell_28_28, ell_29_33, ell_34_37, ell_38_50, ell_51_66⟩

theorem uniqueProducts_card_27 : (uniqueProducts 27).card = 85 := ell_27_27
theorem uniqueProducts_card_28 : (uniqueProducts 28).card = 88 := ell_28_28

/-- The missing cubes used in the exceptional characteristic-three residue bounds. -/
theorem cube_seven_not_mem_products_40 : 343 ∉ products 40 := by
  rw [not_mem_products_iff]
  simp only [representationDivisors, core_40]
  decide +kernel

theorem cube_eight_not_mem_products_28 : 512 ∉ products 28 := by
  rw [not_mem_products_iff]
  simp only [representationDivisors, core_28]
  decide +kernel

theorem cube_eleven_not_mem_products_40 : 1331 ∉ products 40 := by
  rw [not_mem_products_iff]
  simp only [representationDivisors, core_40]
  decide +kernel

/-- In particular these exclusions hold at each of `n=26,27,28`. -/
theorem small_cube_exclusions {n : ℕ} (hn : n ≤ 28) :
    343 ∉ products n ∧ 512 ∉ products n := by
  constructor
  · intro hm
    exact cube_seven_not_mem_products_40
      (products_mono (hn.trans (by decide : 28 ≤ 40)) hm)
  · intro hm
    exact cube_eight_not_mem_products_28 (products_mono hn hm)

/-- In particular these exclusions hold at each of `n=38,39,40`. -/
theorem middle_cube_exclusions {n : ℕ} (hn : n ≤ 40) :
    343 ∉ products n ∧ 1331 ∉ products n := by
  constructor
  · intro hm
    exact cube_seven_not_mem_products_40 (products_mono hn hm)
  · intro hm
    exact cube_eleven_not_mem_products_40 (products_mono hn hm)

end FiniteCertificates

end WeightedPilz.Arithmetic
