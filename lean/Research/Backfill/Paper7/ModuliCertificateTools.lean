import Mathlib

/-! A generic Lucas certificate bridge. No finite modulus is assumed prime. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper7Moduli

theorem prime_of_lucas_list (p a : ℕ) (factors : List ℕ)
    (hprod : factors.prod = p - 1)
    (hprimes : ∀ q ∈ factors, q.Prime)
    (hfull : (a : ZMod p) ^ (p - 1) = 1)
    (hproper : ∀ q ∈ factors, (a : ZMod p) ^ ((p - 1) / q) ≠ 1) :
    p.Prime := by
  apply lucas_primality p (a : ZMod p) hfull
  intro q hq hdiv
  have hd : q ∣ factors.prod := by rwa [hprod]
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_prod_iff (Nat.prime_iff.mp hq)).mp hd
  have heq : q = r := (Nat.prime_dvd_prime_iff_eq hq (hprimes r hr)).mp hqr
  subst q
  exact hproper r hr

#print axioms Paper7Moduli.prime_of_lucas_list

end Paper7Moduli
