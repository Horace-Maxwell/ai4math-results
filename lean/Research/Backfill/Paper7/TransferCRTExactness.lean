import Research.Backfill.Paper7.CRTPrimeCertificates
import Research.Backfill.Paper7.CRTTransferMultiplicity

/-! Complete post-freeze v4 CRT source candidate. All original quantified
conjuncts are assembled with actual prime certificates and proof bodies.
The separate 4/36 control is additional and does not alter ReportedARun. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CRTAlgebra
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem check_LegacyTransferCRTExactness :
    BackfillPaper7.Challenge.Legacy.LegacyTransferCRTExactness := by
  refine ⟨?_, actual_aPrimes_pairwise_coprime, actual_aPrimes_product_bound,
    actual_bounded_integer_crt, integerMono_scaling, ?_, reported_a_crt_conclusions⟩
  · intro a ha
    exact ⟨Paper7CRTPrimes.actual_aPrimes_prime a ha, actual_aPrimes_upper_bound a ha⟩
  · intro b x m _hm
    exact integerMono_envelope_bounds b x m
#print axioms Paper7CRTAlgebra.check_LegacyTransferCRTExactness

/-- All six CRT conclusions on the separate 4/36 budget, without a run-family,
integrality, residue-table correctness or floating-guard premise. -/
theorem control_four_thirtysix_crt_conclusions (x : PQ 4) (hB : Budget 4 36 x)
    (m : ℤ) (hm : 2 ≤ m.natAbs) (hM : m.natAbs ≤ 9) :
    2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ 4 < 2 ^ 240 ∧
    (traceDifference x m).natAbs < 2 ^ 240 ∧
    (∀ i j : Fin 2, (scalarDifference x m i j).natAbs < 2 ^ 240) ∧
    (CRTTraceZero x m ↔ (integerMono x m).trace = 2 * (transferH m) ^ 4) ∧
    (CRTScalarZero x m ↔ integerMono x m =
      (transferH m) ^ 4 • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ∧
    CRTMultiplicity x m = mult (SG 4 x.1 x.2) (m : ℝ) := by
  have he := Paper7CRTEnvelope.control_four_thirtysix_envelope x hB m hm hM
  have hd := differences_lt_of_envelope 4 x m he
  exact ⟨he, hd.1, hd.2, crt_trace_iff_of_envelope 4 x m he,
    crt_scalar_iff_of_envelope 4 x m he,
    crt_multiplicity_of_envelope 4 x (by norm_num) m hm he⟩
#print axioms Paper7CRTAlgebra.control_four_thirtysix_crt_conclusions

end Paper7CRTAlgebra
