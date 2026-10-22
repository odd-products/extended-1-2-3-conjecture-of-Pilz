import Pilz.Width
import Pilz.Support

/-! The lexicographic minimality argument in the fresh-variable descent. -/

namespace Pilz

def ShortMultiple (F : Poly) (N : ℕ) (G : Poly) : Prop :=
  G ≠ 0 ∧ F ∣ G ∧ weight G < N

/-- Minimize base width first and weight second, exactly as in the paper. -/
def Extremal (F : Poly) (B : Finset ℕ) (N : ℕ) (G : Poly) : Prop :=
  ShortMultiple F N G ∧ ∀ Q : Poly, ShortMultiple F N Q →
    totalWidth B G ≤ totalWidth B Q ∧
      (totalWidth B G = totalWidth B Q → weight G ≤ weight Q)

theorem exists_extremal (F : Poly) (B : Finset ℕ) (N : ℕ)
    (hex : ∃ G : Poly, ShortMultiple F N G) :
    ∃ G : Poly, Extremal F B N G := by
  classical
  let widthPossible : ℕ → Prop := fun w =>
    ∃ G : Poly, ShortMultiple F N G ∧ totalWidth B G = w
  have hwidth : ∃ w, widthPossible w := by
    obtain ⟨G, hG⟩ := hex
    exact ⟨totalWidth B G, G, hG, rfl⟩
  obtain ⟨E, hE, hEwidth⟩ := Nat.find_spec hwidth
  let weightPossible : ℕ → Prop := fun m =>
    ∃ G : Poly, ShortMultiple F N G ∧ totalWidth B G = Nat.find hwidth ∧ weight G = m
  have hweight : ∃ m, weightPossible m := ⟨weight E, E, hE, hEwidth, rfl⟩
  obtain ⟨G, hG, hGwidth, hGweight⟩ := Nat.find_spec hweight
  refine ⟨G, hG, ?_⟩
  intro Q hQ
  have hw : Nat.find hwidth ≤ totalWidth B Q :=
    Nat.find_min' hwidth ⟨Q, hQ, rfl⟩
  refine ⟨by omega, ?_⟩
  intro heq
  have hqwidth : totalWidth B Q = Nat.find hwidth := heq.symm.trans hGwidth
  have hm : Nat.find hweight ≤ weight Q :=
    Nat.find_min' hweight ⟨Q, hQ, hqwidth, rfl⟩
  omega

/-- Stability under a replacement with no more terms and no greater widths. -/
theorem extremal_stability (F : Poly) (B : Finset ℕ) (N : ℕ) (G Q : Poly)
    (hG : Extremal F B N G) (hQ : Q ≠ 0) (hdiv : F ∣ Q)
    (hweight : weight Q ≤ weight G)
    (hwidth : ∀ p ∈ B, widthOf p Q ≤ widthOf p G) :
    Extremal F B N Q ∧ weight Q = weight G ∧ totalWidth B Q = totalWidth B G := by
  have hshort : ShortMultiple F N Q := ⟨hQ, hdiv, hweight.trans_lt hG.1.2.2⟩
  have hwle : totalWidth B Q ≤ totalWidth B G := Finset.sum_le_sum hwidth
  have hwge := (hG.2 Q hshort).1
  have hweq : totalWidth B Q = totalWidth B G := Nat.le_antisymm hwle hwge
  have hmge := (hG.2 Q hshort).2 hweq.symm
  have hmeq : weight Q = weight G := Nat.le_antisymm hweight hmge
  refine ⟨⟨hshort, ?_⟩, hmeq, hweq⟩
  intro P hP
  obtain ⟨hw, hm⟩ := hG.2 P hP
  constructor
  · simpa [hweq] using hw
  · intro heq
    rw [hmeq]
    exact hm (hweq.symm.trans heq)

/-- Any smaller-weight multiple with no larger widths must be zero. -/
theorem extremal_eq_zero_of_weight_lt (F : Poly) (B : Finset ℕ) (N : ℕ) (G Q : Poly)
    (hG : Extremal F B N G) (hdiv : F ∣ Q)
    (hweight : weight Q < weight G)
    (hwidth : Q ≠ 0 → ∀ p ∈ B, widthOf p Q ≤ widthOf p G) : Q = 0 := by
  by_contra hQ
  have heq := (extremal_stability F B N G Q hG hQ hdiv hweight.le (hwidth hQ)).2.1
  omega

/-- Multiplication by a monomial preserves extremality. In particular this
applies to the fresh-variable parity normalization in Step 1. -/
theorem extremal_monomial_mul (F : Poly) (B : Finset ℕ) (N : ℕ) (G : Poly)
    (hG : Extremal F B N G) (d : ℕ →₀ ℕ) :
    Extremal F B N (MvPolynomial.monomial d 1 * G) := by
  have hm : (MvPolynomial.monomial d 1 : Poly) ≠ 0 := by simp
  have hdiv : F ∣ MvPolynomial.monomial d 1 * G := dvd_mul_of_dvd_right hG.1.2.1 _
  exact (extremal_stability F B N G _ hG (mul_ne_zero hm hG.1.1) hdiv
    (by rw [weight_monomial_mul])
    (fun p _ => by rw [widthOf_monomial_mul p d hG.1.1])).1

end Pilz
