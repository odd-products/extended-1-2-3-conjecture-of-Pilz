import Pilz.PrimeCounts
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
# Finite prime-count statements in the journal proof

The definitions count actual primes in natural-number intervals. The inequalities
use `n / k`, the integer part of the corresponding real argument in the paper.
All certificates in this file are kernel checked; no `native_decide` is used.
-/

set_option Elab.async false

namespace Pilz

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- The journal's endpoint observation: n=66 does not satisfy r(n)>=sqrt(n). -/
theorem freshCount_66 : freshCount 66 = 7 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sqrt_66 : Nat.sqrt 66 = 8 := by
  exact (Nat.eq_sqrt.mpr (by decide : 8 * 8 ≤ 66 ∧ 66 < (8 + 1) * (8 + 1))).symm

theorem freshCount_66_lt_sqrt : freshCount 66 < Nat.sqrt 66 := by
  rw [freshCount_66, sqrt_66]
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- The first endpoint of the paper's fresh-prime theorem. -/
theorem freshCount_67 : freshCount 67 = 8 := by decide


/-- The finite part of Proposition 5.1 in the journal manuscript. -/
def FinitePrimeBounds (n : ℕ) : Prop :=
  Nat.sqrt n ≤ freshCount n ∧ 8 ≤ freshCount n ∧ PrimeBudget n

private def primeData : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021]

set_option maxRecDepth 16384 in
private theorem primeData_chain : primeData.IsChain (· < ·) := by decide

private def primeCertificate : Finset ℕ :=
  ⟨primeData, primeData_chain.pairwise.imp (fun h => Nat.ne_of_lt h)⟩

/-- Trial division through the square root, bounded by 31 below 1024. -/
private def SmallPrime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ m : Fin 32, 2 ≤ m.val → m.val * m.val ≤ p → ¬m.val ∣ p

private instance (p : ℕ) : Decidable (SmallPrime p) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem prime_iff_smallPrime {p : ℕ} (hp : p ≤ 1023) :
    Nat.Prime p ↔ SmallPrime p := by
  rw [Nat.prime_def_le_sqrt]
  unfold SmallPrime
  constructor
  · rintro ⟨hp2, hdiv⟩
    exact ⟨hp2, fun m hm2 hms => hdiv m.val hm2 (Nat.le_sqrt.mpr hms)⟩
  · rintro ⟨hp2, hdiv⟩
    refine ⟨hp2, fun m hm2 hms => ?_⟩
    have hs : Nat.sqrt p < 32 := Nat.sqrt_lt.mpr (by omega)
    exact hdiv ⟨m, by omega⟩ hm2 (Nat.le_sqrt.mp hms)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_0 :
    ∀ p : Fin 32, SmallPrime (p.val + 0) ↔
      p.val + 0 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_32 :
    ∀ p : Fin 32, SmallPrime (p.val + 32) ↔
      p.val + 32 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_64 :
    ∀ p : Fin 32, SmallPrime (p.val + 64) ↔
      p.val + 64 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_96 :
    ∀ p : Fin 32, SmallPrime (p.val + 96) ↔
      p.val + 96 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_128 :
    ∀ p : Fin 32, SmallPrime (p.val + 128) ↔
      p.val + 128 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_160 :
    ∀ p : Fin 32, SmallPrime (p.val + 160) ↔
      p.val + 160 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_192 :
    ∀ p : Fin 32, SmallPrime (p.val + 192) ↔
      p.val + 192 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_224 :
    ∀ p : Fin 32, SmallPrime (p.val + 224) ↔
      p.val + 224 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_256 :
    ∀ p : Fin 32, SmallPrime (p.val + 256) ↔
      p.val + 256 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_288 :
    ∀ p : Fin 32, SmallPrime (p.val + 288) ↔
      p.val + 288 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_320 :
    ∀ p : Fin 32, SmallPrime (p.val + 320) ↔
      p.val + 320 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_352 :
    ∀ p : Fin 32, SmallPrime (p.val + 352) ↔
      p.val + 352 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_384 :
    ∀ p : Fin 32, SmallPrime (p.val + 384) ↔
      p.val + 384 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_416 :
    ∀ p : Fin 32, SmallPrime (p.val + 416) ↔
      p.val + 416 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_448 :
    ∀ p : Fin 32, SmallPrime (p.val + 448) ↔
      p.val + 448 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_480 :
    ∀ p : Fin 32, SmallPrime (p.val + 480) ↔
      p.val + 480 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_512 :
    ∀ p : Fin 32, SmallPrime (p.val + 512) ↔
      p.val + 512 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_544 :
    ∀ p : Fin 32, SmallPrime (p.val + 544) ↔
      p.val + 544 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_576 :
    ∀ p : Fin 32, SmallPrime (p.val + 576) ↔
      p.val + 576 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_608 :
    ∀ p : Fin 32, SmallPrime (p.val + 608) ↔
      p.val + 608 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_640 :
    ∀ p : Fin 32, SmallPrime (p.val + 640) ↔
      p.val + 640 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_672 :
    ∀ p : Fin 32, SmallPrime (p.val + 672) ↔
      p.val + 672 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_704 :
    ∀ p : Fin 32, SmallPrime (p.val + 704) ↔
      p.val + 704 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_736 :
    ∀ p : Fin 32, SmallPrime (p.val + 736) ↔
      p.val + 736 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_768 :
    ∀ p : Fin 32, SmallPrime (p.val + 768) ↔
      p.val + 768 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_800 :
    ∀ p : Fin 32, SmallPrime (p.val + 800) ↔
      p.val + 800 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_832 :
    ∀ p : Fin 32, SmallPrime (p.val + 832) ↔
      p.val + 832 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_864 :
    ∀ p : Fin 32, SmallPrime (p.val + 864) ↔
      p.val + 864 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_896 :
    ∀ p : Fin 32, SmallPrime (p.val + 896) ↔
      p.val + 896 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_928 :
    ∀ p : Fin 32, SmallPrime (p.val + 928) ↔
      p.val + 928 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_960 :
    ∀ p : Fin 32, SmallPrime (p.val + 960) ↔
      p.val + 960 ∈ primeCertificate := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem primeCertificate_992 :
    ∀ p : Fin 32, SmallPrime (p.val + 992) ↔
      p.val + 992 ∈ primeCertificate := by decide

private theorem primeCertificate_correct {p : ℕ} (hp : p ≤ 1023) :
    Nat.Prime p ↔ p ∈ primeCertificate := by
  apply (prime_iff_smallPrime hp).trans
  by_cases h31 : p ≤ 31
  · have heq : p - 0 + 0 = p := by omega
    simpa only [heq] using primeCertificate_0 ⟨p - 0, by omega⟩
  by_cases h63 : p ≤ 63
  · have heq : p - 32 + 32 = p := by omega
    simpa only [heq] using primeCertificate_32 ⟨p - 32, by omega⟩
  by_cases h95 : p ≤ 95
  · have heq : p - 64 + 64 = p := by omega
    simpa only [heq] using primeCertificate_64 ⟨p - 64, by omega⟩
  by_cases h127 : p ≤ 127
  · have heq : p - 96 + 96 = p := by omega
    simpa only [heq] using primeCertificate_96 ⟨p - 96, by omega⟩
  by_cases h159 : p ≤ 159
  · have heq : p - 128 + 128 = p := by omega
    simpa only [heq] using primeCertificate_128 ⟨p - 128, by omega⟩
  by_cases h191 : p ≤ 191
  · have heq : p - 160 + 160 = p := by omega
    simpa only [heq] using primeCertificate_160 ⟨p - 160, by omega⟩
  by_cases h223 : p ≤ 223
  · have heq : p - 192 + 192 = p := by omega
    simpa only [heq] using primeCertificate_192 ⟨p - 192, by omega⟩
  by_cases h255 : p ≤ 255
  · have heq : p - 224 + 224 = p := by omega
    simpa only [heq] using primeCertificate_224 ⟨p - 224, by omega⟩
  by_cases h287 : p ≤ 287
  · have heq : p - 256 + 256 = p := by omega
    simpa only [heq] using primeCertificate_256 ⟨p - 256, by omega⟩
  by_cases h319 : p ≤ 319
  · have heq : p - 288 + 288 = p := by omega
    simpa only [heq] using primeCertificate_288 ⟨p - 288, by omega⟩
  by_cases h351 : p ≤ 351
  · have heq : p - 320 + 320 = p := by omega
    simpa only [heq] using primeCertificate_320 ⟨p - 320, by omega⟩
  by_cases h383 : p ≤ 383
  · have heq : p - 352 + 352 = p := by omega
    simpa only [heq] using primeCertificate_352 ⟨p - 352, by omega⟩
  by_cases h415 : p ≤ 415
  · have heq : p - 384 + 384 = p := by omega
    simpa only [heq] using primeCertificate_384 ⟨p - 384, by omega⟩
  by_cases h447 : p ≤ 447
  · have heq : p - 416 + 416 = p := by omega
    simpa only [heq] using primeCertificate_416 ⟨p - 416, by omega⟩
  by_cases h479 : p ≤ 479
  · have heq : p - 448 + 448 = p := by omega
    simpa only [heq] using primeCertificate_448 ⟨p - 448, by omega⟩
  by_cases h511 : p ≤ 511
  · have heq : p - 480 + 480 = p := by omega
    simpa only [heq] using primeCertificate_480 ⟨p - 480, by omega⟩
  by_cases h543 : p ≤ 543
  · have heq : p - 512 + 512 = p := by omega
    simpa only [heq] using primeCertificate_512 ⟨p - 512, by omega⟩
  by_cases h575 : p ≤ 575
  · have heq : p - 544 + 544 = p := by omega
    simpa only [heq] using primeCertificate_544 ⟨p - 544, by omega⟩
  by_cases h607 : p ≤ 607
  · have heq : p - 576 + 576 = p := by omega
    simpa only [heq] using primeCertificate_576 ⟨p - 576, by omega⟩
  by_cases h639 : p ≤ 639
  · have heq : p - 608 + 608 = p := by omega
    simpa only [heq] using primeCertificate_608 ⟨p - 608, by omega⟩
  by_cases h671 : p ≤ 671
  · have heq : p - 640 + 640 = p := by omega
    simpa only [heq] using primeCertificate_640 ⟨p - 640, by omega⟩
  by_cases h703 : p ≤ 703
  · have heq : p - 672 + 672 = p := by omega
    simpa only [heq] using primeCertificate_672 ⟨p - 672, by omega⟩
  by_cases h735 : p ≤ 735
  · have heq : p - 704 + 704 = p := by omega
    simpa only [heq] using primeCertificate_704 ⟨p - 704, by omega⟩
  by_cases h767 : p ≤ 767
  · have heq : p - 736 + 736 = p := by omega
    simpa only [heq] using primeCertificate_736 ⟨p - 736, by omega⟩
  by_cases h799 : p ≤ 799
  · have heq : p - 768 + 768 = p := by omega
    simpa only [heq] using primeCertificate_768 ⟨p - 768, by omega⟩
  by_cases h831 : p ≤ 831
  · have heq : p - 800 + 800 = p := by omega
    simpa only [heq] using primeCertificate_800 ⟨p - 800, by omega⟩
  by_cases h863 : p ≤ 863
  · have heq : p - 832 + 832 = p := by omega
    simpa only [heq] using primeCertificate_832 ⟨p - 832, by omega⟩
  by_cases h895 : p ≤ 895
  · have heq : p - 864 + 864 = p := by omega
    simpa only [heq] using primeCertificate_864 ⟨p - 864, by omega⟩
  by_cases h927 : p ≤ 927
  · have heq : p - 896 + 896 = p := by omega
    simpa only [heq] using primeCertificate_896 ⟨p - 896, by omega⟩
  by_cases h959 : p ≤ 959
  · have heq : p - 928 + 928 = p := by omega
    simpa only [heq] using primeCertificate_928 ⟨p - 928, by omega⟩
  by_cases h991 : p ≤ 991
  · have heq : p - 960 + 960 = p := by omega
    simpa only [heq] using primeCertificate_960 ⟨p - 960, by omega⟩
  have heq : p - 992 + 992 = p := by omega
  simpa only [heq] using primeCertificate_992 ⟨p - 992, by omega⟩

private def certifiedCount (n : ℕ) : ℕ :=
  (primeCertificate.filter (fun p => p ≤ n)).card

private theorem primeCount_eq_certified {n : ℕ} (hn : n ≤ 1023) :
    primeCount n = certifiedCount n := by
  unfold primeCount certifiedCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hprime⟩
    have hpn : p ≤ n := Nat.le_of_lt_succ hp
    exact ⟨(primeCertificate_correct (hpn.trans hn)).mp hprime, hpn⟩
  · rintro ⟨hmem, hp⟩
    exact ⟨Nat.lt_succ_of_le hp, (primeCertificate_correct (hp.trans hn)).mpr hmem⟩

private theorem sqrt_le_iff_square_lt (n r : ℕ) :
    Nat.sqrt n ≤ r ↔ n < (r + 1) * (r + 1) := by
  exact (show Nat.sqrt n ≤ r ↔ Nat.sqrt n < r + 1 by omega).trans Nat.sqrt_lt

private def CertifiedBounds (n : ℕ) : Prop :=
  let r := certifiedCount n - certifiedCount (n / 2)
  n < (r + 1) * (r + 1) ∧ 8 ≤ r ∧
    n + 48 ≤ 10 * r + 4 * certifiedCount (n / 2) +
      2 * certifiedCount (n / 3) + 2 * certifiedCount (n / 5)

private instance (n : ℕ) : Decidable (CertifiedBounds n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private theorem finitePrimeBounds_iff_certified {n : ℕ} (hn : n ≤ 1023) :
    FinitePrimeBounds n ↔ CertifiedBounds n := by
  unfold FinitePrimeBounds CertifiedBounds PrimeBudget freshCount
  rw [primeCount_eq_certified hn,
    primeCount_eq_certified (show n / 2 ≤ 1023 by omega),
    primeCount_eq_certified (show n / 3 ≤ 1023 by omega),
    primeCount_eq_certified (show n / 5 ≤ 1023 by omega)]
  rw [sqrt_le_iff_square_lt]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_67 : CertifiedBounds 67 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_68 : CertifiedBounds 68 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_69 : CertifiedBounds 69 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_70 : CertifiedBounds 70 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_71 : CertifiedBounds 71 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_72 : CertifiedBounds 72 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_73 : CertifiedBounds 73 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_74 : CertifiedBounds 74 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_75 : CertifiedBounds 75 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_76 : CertifiedBounds 76 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_77 : CertifiedBounds 77 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_78 : CertifiedBounds 78 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_79 : CertifiedBounds 79 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_80 : CertifiedBounds 80 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_81 : CertifiedBounds 81 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_82 : CertifiedBounds 82 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_83 : CertifiedBounds 83 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_84 : CertifiedBounds 84 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_85 : CertifiedBounds 85 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_86 : CertifiedBounds 86 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_87 : CertifiedBounds 87 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_88 : CertifiedBounds 88 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_89 : CertifiedBounds 89 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_90 : CertifiedBounds 90 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_91 : CertifiedBounds 91 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_92 : CertifiedBounds 92 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_93 : CertifiedBounds 93 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_94 : CertifiedBounds 94 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_95 : CertifiedBounds 95 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_96 : CertifiedBounds 96 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_97 : CertifiedBounds 97 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_98 : CertifiedBounds 98 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_99 : CertifiedBounds 99 := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem certified_100 : CertifiedBounds 100 := by decide

/-- The initial finite range, Lemma 6.1 of the journal proof. -/
theorem finitePrimeBounds_67_100 {n : ℕ} (hn : 67 ≤ n) (hn' : n ≤ 100) :
    FinitePrimeBounds n := by
  apply (finitePrimeBounds_iff_certified (by omega)).mpr
  by_cases h67 : n ≤ 67
  · have heq : n = 67 := by omega
    subst n
    exact certified_67
  by_cases h68 : n ≤ 68
  · have heq : n = 68 := by omega
    subst n
    exact certified_68
  by_cases h69 : n ≤ 69
  · have heq : n = 69 := by omega
    subst n
    exact certified_69
  by_cases h70 : n ≤ 70
  · have heq : n = 70 := by omega
    subst n
    exact certified_70
  by_cases h71 : n ≤ 71
  · have heq : n = 71 := by omega
    subst n
    exact certified_71
  by_cases h72 : n ≤ 72
  · have heq : n = 72 := by omega
    subst n
    exact certified_72
  by_cases h73 : n ≤ 73
  · have heq : n = 73 := by omega
    subst n
    exact certified_73
  by_cases h74 : n ≤ 74
  · have heq : n = 74 := by omega
    subst n
    exact certified_74
  by_cases h75 : n ≤ 75
  · have heq : n = 75 := by omega
    subst n
    exact certified_75
  by_cases h76 : n ≤ 76
  · have heq : n = 76 := by omega
    subst n
    exact certified_76
  by_cases h77 : n ≤ 77
  · have heq : n = 77 := by omega
    subst n
    exact certified_77
  by_cases h78 : n ≤ 78
  · have heq : n = 78 := by omega
    subst n
    exact certified_78
  by_cases h79 : n ≤ 79
  · have heq : n = 79 := by omega
    subst n
    exact certified_79
  by_cases h80 : n ≤ 80
  · have heq : n = 80 := by omega
    subst n
    exact certified_80
  by_cases h81 : n ≤ 81
  · have heq : n = 81 := by omega
    subst n
    exact certified_81
  by_cases h82 : n ≤ 82
  · have heq : n = 82 := by omega
    subst n
    exact certified_82
  by_cases h83 : n ≤ 83
  · have heq : n = 83 := by omega
    subst n
    exact certified_83
  by_cases h84 : n ≤ 84
  · have heq : n = 84 := by omega
    subst n
    exact certified_84
  by_cases h85 : n ≤ 85
  · have heq : n = 85 := by omega
    subst n
    exact certified_85
  by_cases h86 : n ≤ 86
  · have heq : n = 86 := by omega
    subst n
    exact certified_86
  by_cases h87 : n ≤ 87
  · have heq : n = 87 := by omega
    subst n
    exact certified_87
  by_cases h88 : n ≤ 88
  · have heq : n = 88 := by omega
    subst n
    exact certified_88
  by_cases h89 : n ≤ 89
  · have heq : n = 89 := by omega
    subst n
    exact certified_89
  by_cases h90 : n ≤ 90
  · have heq : n = 90 := by omega
    subst n
    exact certified_90
  by_cases h91 : n ≤ 91
  · have heq : n = 91 := by omega
    subst n
    exact certified_91
  by_cases h92 : n ≤ 92
  · have heq : n = 92 := by omega
    subst n
    exact certified_92
  by_cases h93 : n ≤ 93
  · have heq : n = 93 := by omega
    subst n
    exact certified_93
  by_cases h94 : n ≤ 94
  · have heq : n = 94 := by omega
    subst n
    exact certified_94
  by_cases h95 : n ≤ 95
  · have heq : n = 95 := by omega
    subst n
    exact certified_95
  by_cases h96 : n ≤ 96
  · have heq : n = 96 := by omega
    subst n
    exact certified_96
  by_cases h97 : n ≤ 97
  · have heq : n = 97 := by omega
    subst n
    exact certified_97
  by_cases h98 : n ≤ 98
  · have heq : n = 98 := by omega
    subst n
    exact certified_98
  by_cases h99 : n ≤ 99
  · have heq : n = 99 := by omega
    subst n
    exact certified_99
  have heq : n = 100 := by omega
  subst n
  exact certified_100

/-- A table row uses its left endpoint for positive counts and its right
endpoint for the subtracted count, exactly as in the journal proof. -/
private def IntervalCertificate (a b : ℕ) : Prop :=
  let r := primeCount a - primeCount (b / 2)
  b < (r + 1) * (r + 1) ∧ 8 ≤ r ∧
    b + 48 ≤ 10 * r + 4 * primeCount (a / 2) +
      2 * primeCount (a / 3) + 2 * primeCount (a / 5)

private def CertifiedInterval (a b : ℕ) : Prop :=
  let r := certifiedCount a - certifiedCount (b / 2)
  b < (r + 1) * (r + 1) ∧ 8 ≤ r ∧
    b + 48 ≤ 10 * r + 4 * certifiedCount (a / 2) +
      2 * certifiedCount (a / 3) + 2 * certifiedCount (a / 5)

private instance (a b : ℕ) : Decidable (CertifiedInterval a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private theorem intervalCertificate_iff_certified {a b : ℕ}
    (ha : a ≤ 1023) (hb : b ≤ 1023) :
    IntervalCertificate a b ↔ CertifiedInterval a b := by
  unfold IntervalCertificate CertifiedInterval
  rw [primeCount_eq_certified ha,
    primeCount_eq_certified ((Nat.div_le_self b 2).trans hb),
    primeCount_eq_certified ((Nat.div_le_self a 2).trans ha),
    primeCount_eq_certified ((Nat.div_le_self a 3).trans ha),
    primeCount_eq_certified ((Nat.div_le_self a 5).trans ha)]

private theorem bounds_of_interval {a b n : ℕ} (ha : a ≤ n) (hb : n ≤ b)
    (hc : IntervalCertificate a b) : FinitePrimeBounds n := by
  have hpa := primeCount_mono ha
  have hpb := primeCount_mono (show n / 2 ≤ b / 2 from Nat.div_le_div_right hb)
  have hp2 := primeCount_mono (show a / 2 ≤ n / 2 from Nat.div_le_div_right ha)
  have hp3 := primeCount_mono (show a / 3 ≤ n / 3 from Nat.div_le_div_right ha)
  have hp5 := primeCount_mono (show a / 5 ≤ n / 5 from Nat.div_le_div_right ha)
  have hr : primeCount a - primeCount (b / 2) ≤ freshCount n :=
    (Nat.sub_le_sub_right hpa _).trans (Nat.sub_le_sub_left hpb _)
  have hs := Nat.sqrt_le_sqrt hb
  dsimp only [IntervalCertificate] at hc
  have hsr := (sqrt_le_iff_square_lt b (primeCount a - primeCount (b / 2))).mpr hc.1
  refine ⟨hs.trans (hsr.trans hr), hc.2.1.trans hr, ?_⟩
  have hsum := Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left 10 hr) (Nat.mul_le_mul_left 4 hp2))
      (Nat.mul_le_mul_left 2 hp3))
    (Nat.mul_le_mul_left 2 hp5)
  exact (Nat.add_le_add_right hb 48).trans (hc.2.2.trans hsum)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_101_117 : IntervalCertificate 101 117 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_118_141 : IntervalCertificate 118 141 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_142_165 : IntervalCertificate 142 165 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_166_195 : IntervalCertificate 166 195 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_196_225 : IntervalCertificate 196 225 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_226_273 : IntervalCertificate 226 273 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_274_345 : IntervalCertificate 274 345 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_346_421 : IntervalCertificate 346 421 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_422_524 : IntervalCertificate 422 524 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_525_636 : IntervalCertificate 525 636 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_637_765 : IntervalCertificate 637 765 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_766_913 : IntervalCertificate 766 913 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem interval_914_1023 : IntervalCertificate 914 1023 := by
  apply (intervalCertificate_iff_certified (by decide) (by decide)).mpr
  decide

/-- The thirteen rows of the journal's finite prime-count table imply the
full finite claim, rather than checking just the table's endpoints. -/
theorem finitePrimeBounds_67_1023 {n : ℕ} (hn : 67 ≤ n) (hn' : n ≤ 1023) :
    FinitePrimeBounds n := by
  by_cases h100 : n ≤ 100
  · exact finitePrimeBounds_67_100 hn h100
  by_cases h117 : n ≤ 117
  · exact bounds_of_interval (by omega : 101 ≤ n) h117 interval_101_117
  by_cases h141 : n ≤ 141
  · exact bounds_of_interval (by omega : 118 ≤ n) h141 interval_118_141
  by_cases h165 : n ≤ 165
  · exact bounds_of_interval (by omega : 142 ≤ n) h165 interval_142_165
  by_cases h195 : n ≤ 195
  · exact bounds_of_interval (by omega : 166 ≤ n) h195 interval_166_195
  by_cases h225 : n ≤ 225
  · exact bounds_of_interval (by omega : 196 ≤ n) h225 interval_196_225
  by_cases h273 : n ≤ 273
  · exact bounds_of_interval (by omega : 226 ≤ n) h273 interval_226_273
  by_cases h345 : n ≤ 345
  · exact bounds_of_interval (by omega : 274 ≤ n) h345 interval_274_345
  by_cases h421 : n ≤ 421
  · exact bounds_of_interval (by omega : 346 ≤ n) h421 interval_346_421
  by_cases h524 : n ≤ 524
  · exact bounds_of_interval (by omega : 422 ≤ n) h524 interval_422_524
  by_cases h636 : n ≤ 636
  · exact bounds_of_interval (by omega : 525 ≤ n) h636 interval_525_636
  by_cases h765 : n ≤ 765
  · exact bounds_of_interval (by omega : 637 ≤ n) h765 interval_637_765
  by_cases h913 : n ≤ 913
  · exact bounds_of_interval (by omega : 766 ≤ n) h913 interval_766_913
  exact bounds_of_interval (by omega : 914 ≤ n) hn' interval_914_1023

end Pilz
