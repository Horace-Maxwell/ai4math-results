import Research.Backfill.Paper7.CRTPrime7847
import Research.Backfill.Paper7.CRTPrime7817
import Research.Backfill.Paper7.CRTPrime7787
import Research.Backfill.Paper7.CRTPrime7761
import Research.Backfill.Paper7.LegacyTransfer

set_option autoImplicit false
namespace Paper7CRTPrimes
open BackfillPaper7.Challenge.Legacy

theorem actual_aPrimes_prime : ∀ a ∈ aPrimes, a.Prime := by
  intro a ha
  simp only [aPrimes, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact prime_4611686018427387847
  · exact prime_4611686018427387817
  · exact prime_4611686018427387787
  · exact prime_4611686018427387761
#print axioms Paper7CRTPrimes.actual_aPrimes_prime

end Paper7CRTPrimes
