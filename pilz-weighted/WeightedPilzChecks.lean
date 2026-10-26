import WeightedPilz
import Lean.Util.CollectAxioms

/-!
Compact regression checks for the weighted library. The more comprehensive
exact-type acceptance checks are in `WeightedPilzFinalChecks.lean`.
Every theorem in the WeightedPilz namespace loaded by the root import is audited.
-/

example {K : Type*} [Field K] (n : ℕ) (c : ℕ → K)
    (hc : WeightedPilz.NonzeroWeights n c) :
    (WeightedPilz.interval n c).support.card = n :=
  WeightedPilz.weight_interval n c hc

example {K : Type*} [Field K] {σ : Type*} (P : MvPolynomial σ K) :
    ∃ H : MvPolynomial σ K, H ≠ 0 ∧
      (P * H).support.card = WeightedPilz.distance P :=
  WeightedPilz.exists_weight_eq_distance P

example {K L : Type*} [Field K] [Field L] {σ : Type*}
    (f : K →+* L) (P : MvPolynomial σ K) :
    WeightedPilz.distance (MvPolynomial.map f P) = WeightedPilz.distance P :=
  WeightedPilz.distance_map f P

example {K : Type*} [Field K] {σ : Type*}
    (C : MvPolynomial σ K) (hC : C ≠ 0) (r : ℕ) :
    min (WeightedPilz.weight C + r) (WeightedPilz.distance C + 2 * r) ≤
      WeightedPilz.distance (WeightedPilz.iteratedCompletion C r) :=
  WeightedPilz.sharp_completion C hC r

example {K : Type*} [Field K] {σ : Type*} (p e : ℕ) [ExpChar K p]
    (P E : MvPolynomial σ K) (α : σ →₀ ℕ)
    (hU : P ^ p ^ e * E ≠ 0)
    (hres : ∀ d ∈ (P ^ p ^ e * E).support, WeightedPilz.residueExponent (p ^ e) d = α) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      (∀ d ∈ J.support, α + WeightedPilz.scaleExponent (p ^ e) d ∈ E.support) ∧
      (∀ d ∈ (P * J).support, α + WeightedPilz.scaleExponent (p ^ e) d ∈
        (P ^ p ^ e * E).support) :=
  WeightedPilz.frobenius_extraction p e P E α hU hres

example {K : Type*} [Field K] (n : ℕ) (c : ℕ → K) (H : WeightedPilz.Poly K)
    (hc : WeightedPilz.NonzeroWeights n c) (hn : 67 ≤ n) (hH : H ≠ 0)
    (hbase : WeightedPilz.FreshPrimeBounded n H) :
    n ≤ (WeightedPilz.interval n c * H).support.card :=
  WeightedPilz.interval_mul_base_lower n c H hc hn hH hbase

example {K : Type*} [Field K] (n : ℕ) (c : ℕ → K) (H : WeightedPilz.Poly K)
    (hc : WeightedPilz.NonzeroWeights n c) (hn : 229 ≤ n) (hH : H ≠ 0) :
    n ≤ (WeightedPilz.interval n c * H).support.card :=
  WeightedPilz.intervalBound_ge229 n c hc hn H hH

example {K : Type*} [Field K] (n : ℕ) (c : ℕ → K)
    (hc : WeightedPilz.NonzeroWeights n c) : WeightedPilz.IntervalBound n c :=
  WeightedPilz.intervalBound_all n c hc

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut audit : Lean.CollectAxioms.State := {}
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "WeightedPilz." then
      match info with
      | .thmInfo _ =>
        count := count + 1
        let (_, next) := ((Lean.CollectAxioms.collect name).run env).run audit
        audit := next
        for axiomName in audit.axioms do
          unless allowed.contains axiomName do
            throwError "{name} depends on an unexpected axiom: {axiomName}"
      | _ => pure ()
  if count == 0 then
    throwError "No WeightedPilz theorems were loaded."
  Lean.logInfo m!"Audited {count} WeightedPilz theorems; only standard foundational axioms."
