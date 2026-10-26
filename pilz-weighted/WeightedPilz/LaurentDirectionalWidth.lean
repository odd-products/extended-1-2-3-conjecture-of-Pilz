import WeightedPilz.DirectionalWidth
import WeightedPilz.Laurent

/-! Directional widths of finite Laurent supports, including negative exponents. -/
noncomputable section
namespace WeightedPilz
variable {σ K Γ : Type*} [DecidableEq σ] [Field K]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

def laurentDirectionalMax (v : (σ →₀ ℤ) →+ Γ) (H : LaurentPoly σ K) : Γ := by
  classical
  exact if h : H = 0 then 0 else H.support.sup' (Finsupp.support_nonempty_iff.mpr h) v

theorem laurentDirectionalMax_eq (v : (σ →₀ ℤ) →+ Γ) (H : LaurentPoly σ K) (hH : H ≠ 0) :
    laurentDirectionalMax v H = H.support.sup' (Finsupp.support_nonempty_iff.mpr hH) v := by
  simp only [laurentDirectionalMax, dif_neg hH]

theorem le_laurentDirectionalMax (v : (σ →₀ ℤ) →+ Γ) (H : LaurentPoly σ K)
    {d : σ →₀ ℤ} (hd : d ∈ H.support) : v d ≤ laurentDirectionalMax v H := by
  have hH : H ≠ 0 := by intro hz; simpa [hz] using hd
  rw [laurentDirectionalMax_eq v H hH]
  exact Finset.le_sup' v hd

theorem exists_laurentDirectionalMax (v : (σ →₀ ℤ) →+ Γ) (H : LaurentPoly σ K)
    (hH : H ≠ 0) : ∃ d ∈ H.support, v d = laurentDirectionalMax v H := by
  rw [laurentDirectionalMax_eq v H hH]
  obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_sup' (Finsupp.support_nonempty_iff.mpr hH) v
  exact ⟨d, hd, heq.symm⟩

theorem laurentDirectionalMax_translate (v : (σ →₀ ℤ) →+ Γ) (e : σ →₀ ℤ)
    (H : LaurentPoly σ K) (hH : H ≠ 0) :
    laurentDirectionalMax v (AddMonoidAlgebra.single e (1 : K) * H) =
      v e + laurentDirectionalMax v H := by
  classical
  have htrans : AddMonoidAlgebra.single e (1 : K) * H ≠ 0 := by
    apply Finsupp.support_nonempty_iff.mp
    rw [AddMonoidAlgebra.support_single_mul H 1 (by simp) e]
    exact Finset.map_nonempty.mpr (Finsupp.support_nonempty_iff.mpr hH)
  apply le_antisymm
  · rw [laurentDirectionalMax_eq v _ htrans]
    apply Finset.sup'_le
    intro d hd
    rw [AddMonoidAlgebra.support_single_mul H 1 (by simp) e] at hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hd
    change v (e + a) ≤ _
    rw [map_add]
    exact add_le_add_left (le_laurentDirectionalMax v H ha) _
  · obtain ⟨d, hd, heq⟩ := exists_laurentDirectionalMax v H hH
    have hmem : e + d ∈ (AddMonoidAlgebra.single e (1 : K) * H).support := by
      rw [AddMonoidAlgebra.support_single_mul H 1 (by simp) e]
      exact Finset.mem_map.mpr ⟨d, hd, rfl⟩
    have h := le_laurentDirectionalMax v _ hmem
    simpa only [map_add, heq] using h

theorem laurentDirectionalMax_toLaurent (v : (σ →₀ ℤ) →+ Γ) (P : MvPolynomial σ K) :
    laurentDirectionalMax v (toLaurent P) = directionalMax (v.comp integerExponent) P := by
  classical
  by_cases hP : P = 0
  · simp [hP, laurentDirectionalMax, directionalMax]
  · rw [laurentDirectionalMax_eq v _ (fun hz => hP ((toLaurent_eq_zero P).mp hz)),
      directionalMax_eq _ P hP]
    simp only [support_toLaurent, Finset.sup'_image] <;> rfl

def laurentDirectionalWidth (v : (σ →₀ ℤ) →+ Γ) (H : LaurentPoly σ K) : Γ :=
  laurentDirectionalMax v H + laurentDirectionalMax (-v) H

theorem laurentDirectionalWidth_eq_sup_sub_inf (v : (σ →₀ ℤ) →+ Γ)
    (H : LaurentPoly σ K) (hH : H ≠ 0) :
    laurentDirectionalWidth v H =
      H.support.sup' (Finsupp.support_nonempty_iff.mpr hH) v -
        H.support.inf' (Finsupp.support_nonempty_iff.mpr hH) v := by
  have hmin : laurentDirectionalMax (-v) H =
      -H.support.inf' (Finsupp.support_nonempty_iff.mpr hH) v := by
    apply le_antisymm
    · rw [laurentDirectionalMax_eq (-v) H hH]
      apply Finset.sup'_le
      intro d hd
      exact neg_le_neg (Finset.inf'_le v hd)
    · obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_inf' (Finsupp.support_nonempty_iff.mpr hH) v
      rw [heq]
      exact le_laurentDirectionalMax (-v) H hd
  rw [laurentDirectionalWidth, laurentDirectionalMax_eq v H hH, hmin, sub_eq_add_neg]

theorem laurentDirectionalWidth_translate (v : (σ →₀ ℤ) →+ Γ) (e : σ →₀ ℤ)
    (H : LaurentPoly σ K) :
    laurentDirectionalWidth v (AddMonoidAlgebra.single e (1 : K) * H) =
      laurentDirectionalWidth v H := by
  by_cases hH : H = 0
  · simp [hH]
  · simp only [laurentDirectionalWidth, laurentDirectionalMax_translate v e H hH,
      laurentDirectionalMax_translate (-v) e H hH, AddMonoidHom.neg_apply]
    abel

theorem laurentDirectionalWidth_toLaurent (v : (σ →₀ ℤ) →+ Γ) (P : MvPolynomial σ K) :
    laurentDirectionalWidth v (toLaurent P) = directionalWidth (v.comp integerExponent) P := by
  simp only [laurentDirectionalWidth, directionalWidth, laurentDirectionalMax_toLaurent] <;> rfl

theorem laurentDirectionalWidth_mul (v : (σ →₀ ℤ) →+ Γ) (H J : LaurentPoly σ K)
    (hH : H ≠ 0) (hJ : J ≠ 0) :
    laurentDirectionalWidth v (H * J) =
      laurentDirectionalWidth v H + laurentDirectionalWidth v J := by
  obtain ⟨a, P, hP, hclearP⟩ := exists_laurent_clearing H hH
  obtain ⟨b, Q, hQ, hclearQ⟩ := exists_laurent_clearing J hJ
  have hclear : toLaurent (P * Q) = AddMonoidAlgebra.single (a + b) (1 : K) * (H * J) := by
    calc
      toLaurent (P * Q) =
          (AddMonoidAlgebra.single a (1 : K) * AddMonoidAlgebra.single b (1 : K)) * (H * J) := by
        rw [map_mul, hclearP, hclearQ]
        ac_rfl
      _ = _ := by rw [AddMonoidAlgebra.single_mul_single, one_mul]
  calc
    laurentDirectionalWidth v (H * J) = laurentDirectionalWidth v (toLaurent (P * Q)) := by
      rw [hclear, laurentDirectionalWidth_translate]
    _ = directionalWidth (v.comp integerExponent) (P * Q) := laurentDirectionalWidth_toLaurent v _
    _ = directionalWidth (v.comp integerExponent) P + directionalWidth (v.comp integerExponent) Q :=
      directionalWidth_mul _ P Q hP hQ
    _ = laurentDirectionalWidth v H + laurentDirectionalWidth v J := by
      rw [← laurentDirectionalWidth_toLaurent v P, ← laurentDirectionalWidth_toLaurent v Q,
        hclearP, hclearQ, laurentDirectionalWidth_translate, laurentDirectionalWidth_translate]

def laurentIntegerDirection (v : σ → ℤ) : (σ →₀ ℤ) →+ ℤ where
  toFun d := d.sum (fun i z => z * v i)
  map_zero' := by simp
  map_add' a b := by
    apply Finsupp.sum_add_index'
    · intro i
      simp
    · intro i a b
      simp [add_mul]

def laurentIntegerWidth (v : σ → ℤ) (H : LaurentPoly σ K) : ℤ :=
  laurentDirectionalWidth (laurentIntegerDirection v) H

theorem laurentIntegerWidth_mul (v : σ → ℤ) (H J : LaurentPoly σ K)
    (hH : H ≠ 0) (hJ : J ≠ 0) :
    laurentIntegerWidth v (H * J) = laurentIntegerWidth v H + laurentIntegerWidth v J :=
  laurentDirectionalWidth_mul (laurentIntegerDirection v) H J hH hJ

end WeightedPilz
