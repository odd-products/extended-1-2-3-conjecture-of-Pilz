import WeightedPilz.ResidueCapacity
import WeightedPilz.Frobenius
import Mathlib.Tactic.Ring

/-! Overlap of translated unequal dilates is bounded by one residue class. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ R K : Type*} [DecidableEq σ] [CommSemiring R] [Field K]

theorem translated_dilate_inter_card_le (P : MvPolynomial σ R)
    (T : Finset (σ →₀ ℕ)) (q s : ℕ) (hq : 0 < q) (a b : σ →₀ ℕ) :
    ((P.support.image (fun d => a + scaleExponent q d)) ∩
      (T.image (fun d => b + scaleExponent (q * s) d))).card ≤ residueSigma s P := by
  classical
  let I := (P.support.image (fun d => a + scaleExponent q d)) ∩
    (T.image (fun d => b + scaleExponent (q * s) d))
  by_cases hI : I.Nonempty
  · obtain ⟨z, hz⟩ := hI
    obtain ⟨e₀, he₀, hez⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).1
    obtain ⟨f₀, hf₀, hfz⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).2
    have hbase : a + scaleExponent q e₀ = b + scaleExponent (q * s) f₀ := hez.trans hfz.symm
    have hres {e f : σ →₀ ℕ}
        (hef : a + scaleExponent q e = b + scaleExponent (q * s) f) :
        residueExponent s e = residueExponent s e₀ := by
      ext i
      have he := congrArg (fun d : σ →₀ ℕ => d i) hef
      have hbasei := congrArg (fun d : σ →₀ ℕ => d i) hbase
      simp only [Finsupp.add_apply, scaleExponent_apply] at he hbasei
      have hcross : q * e i + (q * s) * f₀ i = q * e₀ i + (q * s) * f i := by omega
      have hmul : q * (e i + s * f₀ i) = q * (e₀ i + s * f i) := by
        calc
          _ = q * e i + (q * s) * f₀ i := by ring
          _ = q * e₀ i + (q * s) * f i := hcross
          _ = _ := by ring
      have hcancel := Nat.eq_of_mul_eq_mul_left hq hmul
      have hm := congrArg (fun n : ℕ => n % s) hcancel
      simpa [residueExponent_apply, Nat.add_mod, Nat.mul_mod] using hm
    have hsub : I ⊆ (P.support.filter (fun e => residueExponent s e = residueExponent s e₀)).image
        (fun e => a + scaleExponent q e) := by
      intro x hx
      obtain ⟨e, he, hex⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).1
      obtain ⟨f, hf, hfx⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).2
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hres (hex.trans hfx.symm)⟩, hex⟩
    apply (Finset.card_le_card hsub).trans
    apply Finset.card_image_le.trans
    have hcard : (P.support.filter (fun e => residueExponent s e = residueExponent s e₀)).card =
        residueWeight s P (residueExponent s e₀) := by
      unfold residueWeight weight
      rw [support_residuePart]
      congr 1
      ext d
      simp
    rw [hcard]
    exact residueWeight_le_sigma s P (residueExponent s e₀)
  · have hz : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    change I.card ≤ _
    simp [hz]

theorem support_scalar_monomial_frobenius (p e : ℕ) [ExpChar K p]
    (P : MvPolynomial σ K) (a : σ →₀ ℕ) (u : K) (hu : u ≠ 0) :
    (monomial a u * P ^ p ^ e).support =
      P.support.image (fun d => a + scaleExponent (p ^ e) d) := by
  classical
  have h := AddMonoidAlgebra.support_single_mul (P ^ p ^ e) u (by simp [hu]) a
  change (monomial a u * P ^ p ^ e).support = _ at h
  apply h.trans
  have hs := congrArg (fun S : Finset (σ →₀ ℕ) => S.map (addLeftEmbedding a))
    (support_pow_expChar p e P)
  simpa only [Finset.map_eq_image, Finset.image_image, addLeftEmbedding_apply,
    Function.comp_def] using hs

/-- Cancellation between two translated characteristic powers costs at most
twice the largest residue class at their dilation ratio. -/
theorem distinguished_monomial_sum_overlap (p e f : ℕ) [ExpChar K p]
    (hef : e ≤ f) (P : MvPolynomial σ K) (a b : σ →₀ ℕ) (u v : K)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    2 * weight P ≤ weight (monomial a u * P ^ p ^ e + monomial b v * P ^ p ^ f) +
      2 * residueSigma (p ^ (f - e)) P := by
  classical
  have hfactor : p ^ f = p ^ e * p ^ (f - e) := by
    rw [← pow_add, Nat.add_sub_of_le hef]
  have hinter : ((monomial a u * P ^ p ^ e).support ∩
      (monomial b v * P ^ p ^ f).support).card ≤ residueSigma (p ^ (f - e)) P := by
    rw [support_scalar_monomial_frobenius p e P a u hu,
      support_scalar_monomial_frobenius p f P b v hv, hfactor]
    exact translated_dilate_inter_card_le P P.support (p ^ e) (p ^ (f - e))
      (pow_pos (expChar_pos K p) e) a b
  have h := weight_add_cancellation (monomial a u * P ^ p ^ e) (monomial b v * P ^ p ^ f)
  rw [weight_scalar_monomial_mul a hu, weight_scalar_monomial_mul b hv,
    weight_pow_expChar, weight_pow_expChar] at h
  omega

theorem exists_monomial_of_weight_one (M : MvPolynomial σ K) (hM : weight M = 1) :
    ∃ (a : σ →₀ ℕ) (u : K), u ≠ 0 ∧ M = monomial a u := by
  classical
  obtain ⟨a, hs⟩ := Finset.card_eq_one.mp hM
  refine ⟨a, coeff a M, mem_support_iff.mp (by rw [hs]; simp), ?_⟩
  conv_lhs => rw [M.as_sum]
  rw [hs]
  simp

end WeightedPilz
