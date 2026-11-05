import Research.Backfill.Paper7.ChallengeV3
import Research.Backfill.Paper7.ModuliPrimeCertificates

/-! The complete frozen modular-parameter and integer-window contract. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper7Moduli

open BackfillPaper7.Challenge.Legacy.Algebra

theorem legacy_modulus_prime_and_large (ℓ : ℕ)
    (hℓ : ℓ ∈ bPrimes ∪ cPrimes ∪ {dPrime}) : ℓ.Prime ∧ 216 < ℓ := by
  simp only [bPrimes, cPrimes, dPrime, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hℓ
  rcases hℓ with ((rfl | rfl | rfl) | (rfl | rfl)) | rfl
  · exact ⟨prime_1000000007, by norm_num⟩
  · exact ⟨prime_998244353, by norm_num⟩
  · exact ⟨prime_2305843009213693951, by norm_num⟩
  · exact ⟨prime_2305843009213693951, by norm_num⟩
  · exact ⟨prime_1000000000000000003, by norm_num⟩
  · exact ⟨prime_2147483647, by norm_num⟩

#print axioms Paper7Moduli.legacy_modulus_prime_and_large

/-- Translation by R puts both inputs in [0, ℓ), where remainders are unique.
Primality is not needed by this helper; the final check retains the frozen premise. -/
theorem integerWindow_injOn (ℓ R : ℕ) (hR : 2 * R < ℓ) :
    Set.InjOn (fun z : ℤ => (z : ZMod ℓ)) (integerWindow R : Set ℤ) := by
  intro x hx y hy hxy
  have hx' : -(R : ℤ) ≤ x ∧ x ≤ (R : ℤ) := by
    simpa only [integerWindow, Finset.mem_coe, Finset.mem_Icc] using hx
  have hy' : -(R : ℤ) ≤ y ∧ y ≤ (R : ℤ) := by
    simpa only [integerWindow, Finset.mem_coe, Finset.mem_Icc] using hy
  have hlength : (2 : ℤ) * (R : ℤ) < (ℓ : ℤ) := by exact_mod_cast hR
  have hxn : 0 ≤ x + (R : ℤ) := by omega
  have hyn : 0 ≤ y + (R : ℤ) := by omega
  have hxl : x + (R : ℤ) < (ℓ : ℤ) := by omega
  have hyl : y + (R : ℤ) < (ℓ : ℤ) := by omega
  have hm : x ≡ y [ZMOD (ℓ : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff x y ℓ).mp hxy
  have hs : (x + (R : ℤ)) % (ℓ : ℤ) = (y + (R : ℤ)) % (ℓ : ℤ) :=
    (Int.ModEq.add_right (R : ℤ) hm).eq
  rw [Int.emod_eq_of_lt hxn hxl, Int.emod_eq_of_lt hyn hyl] at hs
  omega

#print axioms Paper7Moduli.integerWindow_injOn

theorem check_LegacyModuliAndWindows :
    BackfillPaper7.Challenge.Legacy.Algebra.LegacyModuliAndWindows := by
  unfold LegacyModuliAndWindows
  constructor
  · exact legacy_modulus_prime_and_large
  · intro ℓ R _hprime hR
    exact integerWindow_injOn ℓ R hR

#print axioms Paper7Moduli.check_LegacyModuliAndWindows

end Paper7Moduli
