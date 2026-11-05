import Research.Backfill.Paper7.IntegralMultiplicitySum
import Research.Backfill.Paper7.ModularNullityUpperBounds
import Research.Backfill.Paper7.LegacyModuliAndWindows

set_option autoImplicit false

namespace Paper7NullitySieve

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

/-- The fixed D-sieve modulus is prime by the accepted original modulus contract. -/
theorem dPrime_prime : dPrime.Prime :=
  (Paper7Moduli.check_LegacyModuliAndWindows.1 dPrime
    (Finset.mem_union_right _ (Finset.mem_singleton_self dPrime))).1

#print axioms Paper7NullitySieve.dPrime_prime

/-- Summing the actual modular multiplicity bounds preserves the exceptional
free-arm offsets at zero and both signs. -/
theorem integral_modular_sum_bound (ℓ : ℕ) (hℓ : ℓ.Prime)
    (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) (hn : nOf b p q ≤ 49)
    (hG : IsIntegralGraph (SG b p q)) :
    nOf b p q ≤ ∑ m ∈ integerWindow 9, modularMultiplicityBound ℓ b p q m := by
  calc
    nOf b p q = ∑ m ∈ integerWindow 9, mult (SG b p q) (m : ℝ) :=
      (check_IntegralMultiplicitySum b p q hb hn hG).symm
    _ ≤ ∑ m ∈ integerWindow 9, modularMultiplicityBound ℓ b p q m := by
      apply Finset.sum_le_sum
      intro m _hm
      exact Paper7ModularNullity.check_ModularNullityUpperBounds ℓ hℓ b p q hb m

#print axioms Paper7NullitySieve.integral_modular_sum_bound

/-- Both conclusions of the frozen D/D2/D3 nullity sieve, with no condition
that the Schur scalar remain nonzero modulo the prime. -/
theorem check_LegacyNullitySieveSoundness :
    BackfillPaper7.Challenge.Legacy.Algebra.LegacyNullitySieveSoundness := by
  intro b p q hb hn
  have hforward := integral_modular_sum_bound dPrime dPrime_prime b p q hb hn
  refine ⟨hforward, ?_⟩
  intro hlt hG
  exact (not_lt_of_ge (hforward hG)) hlt

#print axioms Paper7NullitySieve.check_LegacyNullitySieveSoundness

#check (check_LegacyNullitySieveSoundness :
  BackfillPaper7.Challenge.Legacy.Algebra.LegacyNullitySieveSoundness)

end Paper7NullitySieve
