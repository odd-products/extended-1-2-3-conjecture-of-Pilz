import Pilz.Parity
import Pilz.Residual
import Pilz.Support
import Pilz.ClassCapacity
import Pilz.Width

/-!
# Polynomial parity classes and their square roots

This formalizes the full exponent-parity decomposition used in Sections 2
and 3 of the manuscript.  The index of `parityClass` is the same function
index used by `paritySupport` and `classWeight` in `Pilz.Residual`.
-/

noncomputable section

namespace Pilz

open MvPolynomial

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The full polynomial class with the specified exponent parities. -/
def parityClass (P : Poly) (ε : ℕ → ℕ) : Poly := by
  classical
  exact Finsupp.filter (fun d => ∀ i, d i % 2 = ε i) P

@[simp] theorem coeff_parityClass (P : Poly) (ε : ℕ → ℕ) (d : ℕ →₀ ℕ) :
    coeff d (parityClass P ε) =
      if (∀ i, d i % 2 = ε i) then coeff d P else 0 := by
  classical
  rfl

@[simp] theorem support_parityClass (P : Poly) (ε : ℕ → ℕ) :
    (parityClass P ε).support = paritySupport P ε := by
  classical
  rfl

@[simp] theorem weight_parityClass (P : Poly) (ε : ℕ → ℕ) :
    weight (parityClass P ε) = classWeight P ε := by
  unfold weight classWeight
  rw [support_parityClass]

@[simp] theorem parityClass_zero (ε : ℕ → ℕ) : parityClass 0 ε = 0 := by
  classical
  exact Finsupp.filter_zero _

theorem parityClass_add (P Q : Poly) (ε : ℕ → ℕ) :
    parityClass (P + Q) ε = parityClass P ε + parityClass Q ε := by
  classical
  exact Finsupp.filter_add

theorem parityClass_monomial (d : ℕ →₀ ℕ) (c : ZMod 2) (ε : ℕ → ℕ) :
    parityClass (monomial d c) ε =
      if (∀ i, d i % 2 = ε i) then monomial d c else 0 := by
  classical
  by_cases h : ∀ i, d i % 2 = ε i
  · rw [if_pos h]
    exact Finsupp.filter_single_of_pos _ h
  · rw [if_neg h]
    exact Finsupp.filter_single_of_neg _ h

/-- The bit vector of the exponents of one monomial. -/
def parityExponent (d : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  d.mapRange (fun n => n % 2) (by decide)

/-- The exponent vector obtained by dividing each exponent by two. -/
def halfExponent (d : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  d.mapRange (fun n => n / 2) (by decide)

@[simp] theorem parityExponent_apply (d : ℕ →₀ ℕ) (i : ℕ) :
    parityExponent d i = d i % 2 := rfl

@[simp] theorem halfExponent_apply (d : ℕ →₀ ℕ) (i : ℕ) :
    halfExponent d i = d i / 2 := rfl

theorem exponent_parity_half (d ε : ℕ →₀ ℕ)
    (h : ∀ i, d i % 2 = ε i) :
    ε + doubleExponent (halfExponent d) = d := by
  ext i
  simp only [Finsupp.add_apply, doubleExponent, two_smul, halfExponent_apply]
  have hi := h i
  have hdiv := Nat.mod_add_div (d i) 2
  omega

/-- The square root after removing the parity monomial from a class. -/
def classRoot (P : Poly) (ε : ℕ → ℕ) : Poly :=
  Finsupp.mapDomain halfExponent (parityClass P ε)

theorem halfExponent_injOn_paritySupport (P : Poly) (ε : ℕ → ℕ) :
    Set.InjOn halfExponent (paritySupport P ε : Set (ℕ →₀ ℕ)) := by
  intro a ha b hb hab
  obtain ⟨_ha, hpa⟩ := Finset.mem_filter.mp ha
  obtain ⟨_hb, hpb⟩ := Finset.mem_filter.mp hb
  ext i
  have hi := congrArg (fun d : ℕ →₀ ℕ => d i) hab
  simp only [halfExponent_apply] at hi
  have hrem : a i % 2 = b i % 2 := (hpa i).trans (hpb i).symm
  have hda := Nat.mod_add_div (a i) 2
  have hdb := Nat.mod_add_div (b i) 2
  omega

theorem support_classRoot (P : Poly) (ε : ℕ → ℕ) :
    (classRoot P ε).support = (paritySupport P ε).image halfExponent := by
  classical
  unfold classRoot
  change Finsupp.support (Finsupp.mapDomain halfExponent (parityClass P ε)) = _
  have hinj : Set.InjOn halfExponent (Finsupp.support (parityClass P ε)) := by
    change Set.InjOn halfExponent (MvPolynomial.support (parityClass P ε) : Set _)
    rw [support_parityClass]
    exact halfExponent_injOn_paritySupport P ε
  rw [Finsupp.mapDomain_support_of_injOn _ hinj]
  rfl

theorem weight_classRoot (P : Poly) (ε : ℕ → ℕ) :
    weight (classRoot P ε) = classWeight P ε := by
  classical
  unfold weight classWeight
  rw [support_classRoot]
  exact Finset.card_image_iff.mpr (halfExponent_injOn_paritySupport P ε)

theorem monomial_mul_eq_mapDomain (ε : ℕ →₀ ℕ) (P : Poly) :
    monomial ε 1 * P = Finsupp.mapDomain (fun d => ε + d) P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [monomial_mul, one_mul]
      exact Finsupp.mapDomain_single.symm
  | add P Q hP hQ =>
      rw [mul_add, hP, hQ, Finsupp.mapDomain_add]

/-- Every class is its parity monomial times the square of its class root.
The statement also handles invalid parity vectors, whose classes are zero. -/
theorem parityClass_eq_monomial_mul_square (P : Poly) (ε : ℕ →₀ ℕ) :
    parityClass P ε = monomial ε 1 * (classRoot P ε) ^ 2 := by
  symm
  rw [monomial_mul_eq_mapDomain, square_eq_mapDomain, classRoot]
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  calc
    Finsupp.mapDomain
        ((fun d => ε + d) ∘ doubleExponent ∘ halfExponent) (parityClass P ε) =
        Finsupp.mapDomain id (parityClass P ε) := by
      apply Finsupp.mapDomain_congr
      intro d hd
      change d ∈ MvPolynomial.support (parityClass P ε) at hd
      rw [support_parityClass] at hd
      have hp := (Finset.mem_filter.mp hd).2
      exact exponent_parity_half d ε hp
    _ = parityClass P ε := Finsupp.mapDomain_id

/-- Distinct full parity classes have disjoint supports. -/
theorem parityClass_support_disjoint (P : Poly) (ε η : ℕ → ℕ) (hne : ε ≠ η) :
    Disjoint (parityClass P ε).support (parityClass P η).support := by
  classical
  rw [support_parityClass, support_parityClass]
  apply Finset.disjoint_left.mpr
  intro d hdε hdη
  apply hne
  funext i
  exact ((Finset.mem_filter.mp hdε).2 i).symm.trans ((Finset.mem_filter.mp hdη).2 i)

/-- The finitely many exponent-parity vectors that occur in `P`. -/
def parityIndices (P : Poly) : Finset (ℕ →₀ ℕ) :=
  P.support.image parityExponent

theorem exists_nonzero_parityClass (P : Poly) (hP : P ≠ 0) :
    ∃ ε ∈ parityIndices P, parityClass P ε ≠ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hP
  refine ⟨parityExponent d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
  intro hz
  have hdclass : d ∈ (parityClass P (parityExponent d)).support := by
    rw [support_parityClass]
    exact Finset.mem_filter.mpr ⟨hd, fun _ => rfl⟩
  rw [hz, MvPolynomial.support_zero] at hdclass
  exact Finset.notMem_empty _ hdclass

/-- Summing the nonempty full parity classes recovers the polynomial. -/
theorem sum_parityClasses (P : Poly) :
    (∑ ε ∈ parityIndices P, parityClass P ε) = P := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_sum]
  by_cases hd : d ∈ P.support
  · have hidx : parityExponent d ∈ parityIndices P :=
      Finset.mem_image.mpr ⟨d, hd, rfl⟩
    rw [Finset.sum_eq_single (parityExponent d)]
    · simp
    · intro ε _hε hne
      rw [coeff_parityClass]
      apply if_neg
      intro h
      apply hne
      ext i
      exact (h i).symm
    · exact fun hn => (hn hidx).elim
  · have hz := MvPolynomial.notMem_support_iff.mp hd
    rw [hz]
    apply Finset.sum_eq_zero
    intro ε _hε
    simp only [coeff_parityClass, hz, ite_self]

/-- The paper's full parity decomposition `P = ∑ ε, x^ε P_ε²`. -/
theorem parity_decomposition (P : Poly) :
    P = ∑ ε ∈ parityIndices P, monomial ε 1 * (classRoot P ε) ^ 2 := by
  calc
    P = ∑ ε ∈ parityIndices P, parityClass P ε := (sum_parityClasses P).symm
    _ = ∑ ε ∈ parityIndices P, monomial ε 1 * (classRoot P ε) ^ 2 := by
      apply Finset.sum_congr rfl
      intro ε _hε
      exact parityClass_eq_monomial_mul_square P ε

theorem paritySupport_biUnion (P : Poly) :
    (parityIndices P).biUnion (fun ε => paritySupport P ε) = P.support := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨ε, _hε, hd⟩ := Finset.mem_biUnion.mp hd
    exact paritySupport_subset P ε hd
  · intro hd
    apply Finset.mem_biUnion.mpr
    refine ⟨parityExponent d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨hd, fun _ => rfl⟩

/-- The weights of the disjoint parity classes sum to the total weight. -/
theorem sum_classWeights (P : Poly) :
    (∑ ε ∈ parityIndices P, classWeight P ε) = weight P := by
  classical
  have hdis : (parityIndices P : Set (ℕ →₀ ℕ)).PairwiseDisjoint
      (fun ε => paritySupport P ε) := by
    intro ε _hε η _hη hne
    apply Finset.disjoint_left.mpr
    intro d hdε hdη
    apply hne
    ext i
    exact ((Finset.mem_filter.mp hdε).2 i).symm.trans ((Finset.mem_filter.mp hdη).2 i)
  have hcard := Finset.card_biUnion hdis
  rw [paritySupport_biUnion] at hcard
  exact hcard.symm

theorem exists_parityIndex_of_classWeight_pos {P : Poly} {ε : ℕ → ℕ}
    (h : 0 < classWeight P ε) :
    ∃ η ∈ parityIndices P, (η : ℕ → ℕ) = ε := by
  unfold classWeight at h
  obtain ⟨d, hd⟩ := Finset.card_pos.mp h
  obtain ⟨hd, hpar⟩ := Finset.mem_filter.mp hd
  refine ⟨parityExponent d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
  funext i
  exact hpar i

/-- The largest number of terms in any full parity class: the paper's `σ(P)`. -/
def sigma (P : Poly) : ℕ :=
  (parityIndices P).sup (fun ε => classWeight P ε)

theorem classWeight_le_sigma (P : Poly) (ε : ℕ → ℕ) :
    classWeight P ε ≤ sigma P := by
  by_cases hzero : classWeight P ε = 0
  · rw [hzero]
    exact Nat.zero_le _
  obtain ⟨η, hη, heq⟩ := exists_parityIndex_of_classWeight_pos (Nat.pos_of_ne_zero hzero)
  have hle := Finset.le_sup (f := fun η : ℕ →₀ ℕ => classWeight P η) hη
  change classWeight P η ≤ sigma P at hle
  rw [heq] at hle
  exact hle

theorem sigma_le_weight (P : Poly) : sigma P ≤ weight P := by
  unfold sigma
  exact Finset.sup_le (fun ε _hε => classWeight_le_weight P ε)

/-- The class-capacity estimate used in fresh-variable elimination. -/
theorem classWeight_mul_le_sigma (C D : Poly) (ε : ℕ → ℕ) :
    classWeight (C * D) ε ≤ sigma C * weight D :=
  classWeight_mul_le C D (sigma C) (classWeight_le_sigma C) ε

/-- Multiplying by an even monomial preserves the parity class of each term. -/
theorem parityClass_monomial_mul_of_even (s : ℕ →₀ ℕ) (c : ZMod 2)
    (P : Poly) (ε : ℕ → ℕ) (hs : ∀ i, s i % 2 = 0) :
    parityClass (monomial s c * P) ε = monomial s c * parityClass P ε := by
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
      have hpar : (∀ i, (s + d) i % 2 = ε i) ↔ (∀ i, d i % 2 = ε i) := by
        simp only [Finsupp.add_apply, Nat.add_mod, hs, zero_add, Nat.mod_mod]
      rw [monomial_mul, parityClass_monomial, parityClass_monomial]
      by_cases h : ∀ i, d i % 2 = ε i
      · rw [if_pos h, if_pos (hpar.mpr h), monomial_mul]
      · rw [if_neg h, if_neg (fun hsd => h (hpar.mp hsd)), mul_zero]
  | add P Q hP hQ =>
      simp only [mul_add, parityClass_add, hP, hQ]

/-- A square factor commutes with projection onto every full parity class. -/
theorem parityClass_square_mul (F J : Poly) (ε : ℕ → ℕ) :
    parityClass (F ^ 2 * J) ε = F ^ 2 * parityClass J ε := by
  induction F using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [monomial_pow]
      apply parityClass_monomial_mul_of_even
      intro i
      simp only [two_smul, Finsupp.add_apply]
      omega
  | add F G hF hG =>
      simp only [CharTwo.add_sq, add_mul, parityClass_add, hF, hG]

/-- The square-class identity used for the residual `R = F² J`. -/
theorem parityClass_square_mul_eq (F J : Poly) (ε : ℕ →₀ ℕ) :
    parityClass (F ^ 2 * J) ε = monomial ε 1 * (F * classRoot J ε) ^ 2 := by
  rw [parityClass_square_mul, parityClass_eq_monomial_mul_square]
  simp only [mul_pow, mul_comm, mul_assoc]

/-- A residual parity class has exactly the weight of the corresponding
square-root multiple of `F`, the equality needed in Proposition `prop:residual`. -/
theorem classWeight_square_mul (F J : Poly) (ε : ℕ →₀ ℕ) :
    classWeight (F ^ 2 * J) ε = weight (F * classRoot J ε) := by
  rw [← weight_parityClass, parityClass_square_mul_eq, weight_monomial_mul,
    weight_square]

/-- The residual weight equality for arbitrary function-valued parity indices.
Any nonempty class automatically has a finitely supported parity index. -/
theorem classWeight_square_mul_all (F J : Poly) (ε : ℕ → ℕ) :
    classWeight (F ^ 2 * J) ε = weight (F * classRoot J ε) := by
  by_cases hz : parityClass J ε = 0
  · rw [← weight_parityClass, parityClass_square_mul, hz, mul_zero, weight_zero]
    unfold classRoot
    rw [hz, Finsupp.mapDomain_zero, mul_zero, weight_zero]
  · have hpos : 0 < classWeight J ε := by
      rw [← weight_parityClass]
      exact weight_pos hz
    obtain ⟨η, _hη, heq⟩ := exists_parityIndex_of_classWeight_pos hpos
    rw [← heq]
    exact classWeight_square_mul F J η

theorem classRoot_ne_zero_of_parityClass_ne_zero (P : Poly) (ε : ℕ → ℕ)
    (h : parityClass P ε ≠ 0) : classRoot P ε ≠ 0 := by
  intro hz
  have hpos := weight_pos h
  rw [weight_parityClass] at hpos
  have hw := weight_classRoot P ε
  rw [hz, weight_zero] at hw
  omega

theorem widthOf_parityClass_le (p : ℕ) (P : Poly) (ε : ℕ → ℕ)
    (h : parityClass P ε ≠ 0) : widthOf p (parityClass P ε) ≤ widthOf p P := by
  apply widthOf_mono_support p h
  rw [support_parityClass]
  exact paritySupport_subset P ε

/-- Taking a class root at least halves every coordinate width. -/
theorem twice_widthOf_classRoot_le (p : ℕ) (P : Poly) (ε : ℕ →₀ ℕ)
    (h : parityClass P ε ≠ 0) :
    2 * widthOf p (classRoot P ε) ≤ widthOf p P := by
  have hroot := classRoot_ne_zero_of_parityClass_ne_zero P ε h
  have hwidth := widthOf_parityClass_le p P ε h
  rw [parityClass_eq_monomial_mul_square,
    widthOf_monomial_mul p ε (pow_ne_zero 2 hroot), widthOf_square p hroot] at hwidth
  exact hwidth

theorem twice_totalWidth_classRoot_le (B : Finset ℕ) (P : Poly) (ε : ℕ →₀ ℕ)
    (h : parityClass P ε ≠ 0) :
    2 * totalWidth B (classRoot P ε) ≤ totalWidth B P := by
  unfold totalWidth
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun p _hp => twice_widthOf_classRoot_le p P ε h)

theorem squareClass_multiple_ne_zero (F J : Poly) (ε : ℕ →₀ ℕ)
    (h : parityClass (F ^ 2 * J) ε ≠ 0) : F * classRoot J ε ≠ 0 := by
  intro hz
  apply h
  rw [parityClass_square_mul_eq, hz]
  simp

/-- Every nonzero residual class is a square of a multiple whose coordinate
width is bounded by half the residual width. -/
theorem twice_widthOf_squareClass_multiple_le (p : ℕ) (F J : Poly) (ε : ℕ →₀ ℕ)
    (h : parityClass (F ^ 2 * J) ε ≠ 0) :
    2 * widthOf p (F * classRoot J ε) ≤ widthOf p (F ^ 2 * J) := by
  have hroot := squareClass_multiple_ne_zero F J ε h
  have hwidth := widthOf_parityClass_le p (F ^ 2 * J) ε h
  rw [parityClass_square_mul_eq,
    widthOf_monomial_mul p ε (pow_ne_zero 2 hroot), widthOf_square p hroot] at hwidth
  exact hwidth

theorem twice_totalWidth_squareClass_multiple_le (B : Finset ℕ)
    (F J : Poly) (ε : ℕ →₀ ℕ) (h : parityClass (F ^ 2 * J) ε ≠ 0) :
    2 * totalWidth B (F * classRoot J ε) ≤ totalWidth B (F ^ 2 * J) := by
  unfold totalWidth
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun p _hp => twice_widthOf_squareClass_multiple_le p F J ε h)

end Pilz
