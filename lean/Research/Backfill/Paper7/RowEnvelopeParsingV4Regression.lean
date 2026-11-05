import Research.Backfill.Paper7.LegacyTransfer
set_option autoImplicit false
open scoped BigOperators Matrix
namespace Paper7RowEnvelopeV4Regression
open BackfillPaper7.Challenge.Legacy

/-- Same b=3, p=4, q=0 fixture as the preserved v3 counterexample. -/
def fixturePQ3 : PQ 3 := (fun _ => 4, fun _ => 0)
#print axioms Paper7RowEnvelopeV4Regression.fixturePQ3

theorem rowEnvelope_parsed_shape (b : ℕ) (x : PQ b) (m : ℤ) :
    rowEnvelope x m = ∏ k, ((transferS x m k).natAbs + (transferH m).natAbs) := by
  rfl
#print axioms Paper7RowEnvelopeV4Regression.rowEnvelope_parsed_shape

theorem fixture_transferH : transferH 2 = 6 := by
  decide +kernel
#print axioms Paper7RowEnvelopeV4Regression.fixture_transferH

theorem fixture_transferS : ∀ k : Fin 3, transferS fixturePQ3 2 k = 0 := by
  decide +kernel
#print axioms Paper7RowEnvelopeV4Regression.fixture_transferS

theorem fixture_rowEnvelope : rowEnvelope fixturePQ3 2 = 216 := by
  decide +kernel
#print axioms Paper7RowEnvelopeV4Regression.fixture_rowEnvelope

theorem fixture_integerMono_entry : (integerMono fixturePQ3 2 0 1).natAbs = 216 := by
  decide +kernel
#print axioms Paper7RowEnvelopeV4Regression.fixture_integerMono_entry

/-- A parsing regression for this one fixture; no universal CRT contract proof. -/
theorem fixture_entry_bound :
    (integerMono fixturePQ3 2 0 1).natAbs ≤ rowEnvelope fixturePQ3 2 := by
  rw [fixture_integerMono_entry, fixture_rowEnvelope]
#print axioms Paper7RowEnvelopeV4Regression.fixture_entry_bound

end Paper7RowEnvelopeV4Regression
