import WeightedPilz.IntegerResidues

/-! Refined integer-label capacities for nonzero residue classes and for
the zero class with excluded perfect powers. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]

def integerRootLabel (q : ℕ) (d : ℕ →₀ ℕ) : ℕ :=
  Nat.floorRoot q (d.prod (· ^ ·))

theorem integerRootLabel_factorization (q : ℕ) {a : ℕ} (ha : 0 < a) :
    integerRootLabel q a.factorization = Nat.floorRoot q a := by
  rw [integerRootLabel, Nat.factorization_prod_pow_eq_self ha.ne']

theorem residueExponent_eq_of_mem_part (q : ℕ) (P : Poly K) (α d : ℕ →₀ ℕ)
    (hd : d ∈ (residuePart q P α).support) : residueExponent q d = α := by
  by_contra hne
  have hc := MvPolynomial.mem_support_iff.mp hd
  rw [coeff_residuePart, if_neg hne] at hc
  exact hc rfl

theorem integerRootLabel_injOn_residue (q N : ℕ) (P : Poly K)
    (hP : IntegerSupported N P) (α : ℕ →₀ ℕ) :
    Set.InjOn (integerRootLabel q) ((residuePart q P α).support : Set (ℕ →₀ ℕ)) := by
  intro d hd e he hde
  obtain ⟨a, ha, _, had⟩ := hP d (support_residuePart_subset q P α hd)
  obtain ⟨b, hb, _, hbe⟩ := hP e (support_residuePart_subset q P α he)
  have hroots : Nat.floorRoot q a = Nat.floorRoot q b := by
    simpa only [← had, ← hbe, integerRootLabel_factorization q ha,
      integerRootLabel_factorization q hb] using hde
  have hquot := congrArg Nat.factorization hroots
  rw [Nat.factorization_floorRoot, Nat.factorization_floorRoot, had, hbe] at hquot
  have hmod := (residueExponent_eq_of_mem_part q P α d hd).trans
    (residueExponent_eq_of_mem_part q P α e he).symm
  ext i
  have hdiv : d i / q = e i / q := by
    simpa using congrArg (fun f : ℕ →₀ ℕ => f i) hquot
  have hrem : d i % q = e i % q := congrArg (fun f : ℕ →₀ ℕ => f i) hmod
  have hdv := Nat.mod_add_div (d i) q
  have hev := Nat.mod_add_div (e i) q
  rw [hrem, hdiv] at hdv
  exact hdv.symm.trans hev

theorem residueWeight_le_card_rootLabels (q N : ℕ) (P : Poly K)
    (hP : IntegerSupported N P) (α : ℕ →₀ ℕ) (s : Finset ℕ)
    (hmap : ∀ d ∈ (residuePart q P α).support, integerRootLabel q d ∈ s) :
    residueWeight q P α ≤ s.card := by
  have hi := integerRootLabel_injOn_residue q N P hP α
  have hsub : (residuePart q P α).support.image (integerRootLabel q) ⊆ s := by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
    exact hmap d hd
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hi] at hc

theorem floorRoot_pow_eq_of_residue_zero (q a : ℕ) (hq : 0 < q) (ha : 0 < a)
    (hzero : residueExponent q a.factorization = 0) : Nat.floorRoot q a ^ q = a := by
  have hr : Nat.floorRoot q a ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨hq.ne', ha.ne'⟩
  apply Nat.factorization_inj (pow_ne_zero q hr) ha.ne'
  rw [Nat.factorization_pow, Nat.factorization_floorRoot]
  ext i
  change q * (a.factorization i / q) = a.factorization i
  have hm : a.factorization i % q = 0 := congrArg (fun f : ℕ →₀ ℕ => f i) hzero
  have h := Nat.mod_add_div (a.factorization i) q
  simpa [hm] using h

theorem two_mul_floorRoot_pow_le_of_residue_ne_zero (q a : ℕ) (ha : 0 < a)
    (hne : residueExponent q a.factorization ≠ 0) : 2 * Nat.floorRoot q a ^ q ≤ a := by
  obtain ⟨k, hk⟩ := (Nat.floorRoot_pow_dvd : Nat.floorRoot q a ^ q ∣ a)
  have hk0 : k ≠ 0 := by intro hz; simp [hz] at hk; omega
  have hk1 : k ≠ 1 := by
    intro h1
    have heq : a = Nat.floorRoot q a ^ q := by simpa [h1] using hk
    apply hne
    rw [heq, Nat.factorization_pow]
    ext i
    simp [residueExponent_apply, Finsupp.smul_apply, smul_eq_mul]
  have htwo : 2 ≤ k := by omega
  have hmul := Nat.mul_le_mul_left (Nat.floorRoot q a ^ q) htwo
  nlinarith [hmul]

theorem residueWeight_nonzero_le_of_integerSupported (q N m : ℕ) (hq : 0 < q)
    (P : Poly K) (hP : IntegerSupported N P) (α : ℕ →₀ ℕ) (hα : α ≠ 0)
    (hNm : N < 2 * (m + 1) ^ q) : residueWeight q P α ≤ m := by
  have hc := residueWeight_le_card_rootLabels q N P hP α (Finset.Icc 1 m) (by
    intro d hd
    obtain ⟨a, ha, haN, had⟩ := hP d (support_residuePart_subset q P α hd)
    have hres : residueExponent q a.factorization ≠ 0 := by
      rw [had, residueExponent_eq_of_mem_part q P α d hd]
      exact hα
    rw [← had, integerRootLabel_factorization q ha]
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.pos_of_ne_zero (Nat.floorRoot_ne_zero.mpr ⟨hq.ne', ha.ne'⟩), ?_⟩
    have hbound := (two_mul_floorRoot_pow_le_of_residue_ne_zero q a ha hres).trans haN
    by_contra hnot
    have hle : m + 1 ≤ Nat.floorRoot q a := by omega
    have hpow := Nat.pow_le_pow_left hle q
    omega)
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc

theorem residueWeight_zero_le_of_excluded_powers (q N m : ℕ) (hq : 0 < q)
    (P : Poly K) (hP : IntegerSupported N P) (hNm : N < (m + 1) ^ q)
    (excluded : Finset ℕ)
    (hexcluded : ∀ b ∈ excluded, (b ^ q).factorization ∉ P.support) :
    residueWeight q P 0 ≤ ((Finset.Icc 1 m) \ excluded).card := by
  apply residueWeight_le_card_rootLabels q N P hP 0
  intro d hd
  obtain ⟨a, ha, haN, had⟩ := hP d (support_residuePart_subset q P 0 hd)
  have hres : residueExponent q a.factorization = 0 := by
    rw [had]
    exact residueExponent_eq_of_mem_part q P 0 d hd
  have heq := floorRoot_pow_eq_of_residue_zero q a hq ha hres
  rw [← had, integerRootLabel_factorization q ha]
  apply Finset.mem_sdiff.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    refine ⟨Nat.pos_of_ne_zero (Nat.floorRoot_ne_zero.mpr ⟨hq.ne', ha.ne'⟩), ?_⟩
    by_contra hnot
    have hle : m + 1 ≤ Nat.floorRoot q a := by omega
    have hpow := Nat.pow_le_pow_left hle q
    omega
  · intro hbad
    apply hexcluded _ hbad
    rw [heq, had]
    exact support_residuePart_subset q P 0 hd

end WeightedPilz
