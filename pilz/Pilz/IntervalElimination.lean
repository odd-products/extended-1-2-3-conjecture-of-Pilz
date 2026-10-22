import Pilz.Elimination
import Pilz.IntervalSigma
import Pilz.Fresh
import Pilz.Statements

/-!
# Fresh-prime elimination for intervals

The interval core and its isolated fresh prime terms instantiate the general
fresh-linear setting. Every parity class of the core has at most `sqrt n`
terms, and all core variables are primes at most `n/2`. Thus the general
elimination theorem gives exactly the paper's interval reduction.
-/

noncomputable section

namespace Pilz

theorem support_core_subset_interval (n : ℕ) : (core n).support ⊆ (interval n).support := by
  classical
  have hI : ∀ a ∈ Finset.Icc 1 n, 0 < a := fun _ ha => (Finset.mem_Icc.mp ha).1
  have hC : ∀ a ∈ Finset.Icc 1 n \ freshPrimes n, 0 < a :=
    fun _ ha => hI _ (Finset.mem_sdiff.mp ha).1
  rw [core, support_polynomialOf _ hC, interval_eq_polynomialOf,
    support_polynomialOf _ hI]
  exact Finset.image_subset_image Finset.sdiff_subset

theorem classWeight_mono_support (P Q : Poly) (hPQ : P.support ⊆ Q.support)
    (ε : ℕ → ℕ) : classWeight P ε ≤ classWeight Q ε := by
  classical
  apply Finset.card_le_card
  intro d hd
  obtain ⟨hd, hpar⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hPQ hd, hpar⟩

theorem sigma_core_le_sqrt (n : ℕ) : sigma (core n) ≤ Nat.sqrt n := by
  unfold sigma
  apply Finset.sup_le
  intro ε _
  exact (classWeight_mono_support (core n) (interval n)
    (support_core_subset_interval n) ε).trans (classWeight_interval_le_sqrt n ε)

/-- The paper's core/fresh decomposition as an instance of the general setting. -/
def intervalFreshData (n : ℕ) (hn : 0 < n) (hfresh : (freshPrimes n).Nonempty) : FreshData where
  vars := freshPrimes n
  nonempty := hfresh
  C := core n
  C_ne_zero := core_ne_zero hn
  independent := fun _ hp _ hd => core_fresh_exponent_zero hp hd

@[simp] theorem intervalFreshData_F (n : ℕ) (hn : 0 < n)
    (hfresh : (freshPrimes n).Nonempty) :
    (intervalFreshData n hn hfresh).F = interval n :=
  (interval_eq_core_add_fresh n).symm

/-- The core can involve only primes at most half the interval length. -/
theorem core_vars_prime_bounded (n : ℕ) {p : ℕ} (hp : p ∈ (core n).vars) :
    Nat.Prime p ∧ p ≤ n / 2 := by
  classical
  have hC : ∀ a ∈ Finset.Icc 1 n \ freshPrimes n, 0 < a :=
    fun _ ha => (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).1
  obtain ⟨d, hd, hpd⟩ := (MvPolynomial.mem_vars p).mp hp
  rw [core, support_polynomialOf _ hC] at hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  have hprime : Nat.Prime p := (Nat.mem_primeFactors.mp hpd).1
  have hdiv : p ∣ a := Nat.dvd_of_factorization_pos (Finsupp.mem_support_iff.mp hpd)
  have hap := Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1
  have hpa : p ≤ a := Nat.le_of_dvd hap.1 hdiv
  refine ⟨hprime, ?_⟩
  by_contra hhalf
  have hpfresh : p ∈ freshPrimes n :=
    (mem_freshPrimes_iff n p).mpr ⟨hprime, hpa.trans hap.2, by omega⟩
  have hae : a = p := eq_freshPrime_of_dvd hpfresh (Finset.mem_sdiff.mp ha).1 hdiv
  exact (Finset.mem_sdiff.mp ha).2 (by simpa [hae] using hpfresh)

/-- The exact interval elimination statement used by the final assembly. -/
theorem intervalFreshElimination (n : ℕ) : IntervalFreshElimination n := by
  classical
  intro hn hcount H hH hshort
  have hnpos : 0 < n := by omega
  have hsqrt : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hnpos
  have hfresh : (freshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_freshPrimes]
    omega
  let S := intervalFreshData n hnpos hfresh
  have hSF : S.F = interval n := intervalFreshData_F n hnpos hfresh
  have hN : n ≤ weight S.C + S.vars.card := by
    rw [← S.weight_F, hSF, weight_interval]
  have hσ : sigma S.C ≤ S.vars.card := by
    change sigma (core n) ≤ (freshPrimes n).card
    rw [card_freshPrimes]
    exact (sigma_core_le_sqrt n).trans hcount
  have hG : ShortMultiple S.F n (S.F * H) :=
    ⟨mul_ne_zero S.prime_F.ne_zero hH, dvd_mul_right S.F H, by simpa only [hSF] using hshort⟩
  obtain ⟨E, hE, hEvars, hEshort⟩ := S.eliminate_short n hN hσ ⟨S.F * H, hG⟩
  refine ⟨E, hE, ?_, ?_⟩
  · simpa only [hSF] using hEshort
  · intro p hp
    obtain ⟨d, hd, hdp⟩ := hp
    have hpE : p ∈ E.vars :=
      (MvPolynomial.mem_vars p).mpr ⟨d, hd, Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hdp)⟩
    exact core_vars_prime_bounded n (hEvars hpE)

end Pilz
