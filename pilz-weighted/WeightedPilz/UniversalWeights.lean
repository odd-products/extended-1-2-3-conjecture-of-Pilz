import WeightedPilz.FinalConsequences
import WeightedPilz.UniversalWeightRing

/-! A universal erasure inverse and preservation of that inverse under specialization. -/

noncomputable section
namespace WeightedPilz

/-- The exact universal Laurent-polynomial-ring inverse of
`prop:universal-inverse`, for the same interval matrix used in the actions. -/
theorem universal_erasure_inverse (n : ℕ) (S : Finset ℕ+)
    (E : Finset (intervalOutputSet n S)) (hE : E.card < n) :
    ∃ L : Matrix S {i : intervalOutputSet n S // i ∉ E} (UniversalWeightRing n),
      L * (intervalMatrix n (universalWeights n) S (intervalOutputSet n S)).submatrix
        (fun (i : {i : intervalOutputSet n S // i ∉ E}) => i.val) id = 1 :=
  intervalMatrix_units_erasure_inverse n (universalWeights n)
    (fun a _ _ => universalWeights_isUnit n a) S E hE

/-- The same chosen inverse, rather than a newly selected inverse, works
under every coefficient-ring specialization. -/
theorem universal_erasure_inverse_specializes {R : Type*} [CommRing R]
    (n : ℕ) (S : Finset ℕ+) (E : Finset (intervalOutputSet n S))
    (L : Matrix S {i : intervalOutputSet n S // i ∉ E} (UniversalWeightRing n))
    (hL : L * (intervalMatrix n (universalWeights n) S (intervalOutputSet n S)).submatrix
      (fun (i : {i : intervalOutputSet n S // i ∉ E}) => i.val) id = 1)
    (f : UniversalWeightRing n →+* R) :
    L.map f * (intervalMatrix n (fun a => f (universalWeights n a)) S (intervalOutputSet n S)).submatrix
      (fun (i : {i : intervalOutputSet n S // i ∉ E}) => i.val) id = 1 := by
  have hh := matrix_left_inverse_map f _ L hL
  change L.map f * ((intervalMatrix n (universalWeights n) S (intervalOutputSet n S)).map f).submatrix
    (fun (i : {i : intervalOutputSet n S // i ∉ E}) => i.val) id = 1 at hh
  rwa [intervalMatrix_map] at hh

end WeightedPilz

