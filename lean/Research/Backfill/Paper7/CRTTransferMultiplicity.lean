import Research.Backfill.Paper7.BoundedIntegerCRT
import Research.Backfill.Paper7.IntegerTransferScaling
import Research.Backfill.Paper7.IntegerMatrixEnvelope
import Research.Backfill.Paper7.BudgetTransferEnvelope
import Research.Backfill.Paper7.ReportedALeafBound
import Research.Backfill.Paper7.Lemma22

/-! Actual residue and multiplicity conclusions, with the only remaining
primality obligation displayed explicitly in the final conditional assembly. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CRTAlgebra
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem differences_lt_of_envelope (b : ℕ) (x : PQ b) (m : ℤ)
    (he : 2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b < 2 ^ 240) :
    (traceDifference x m).natAbs < 2 ^ 240 ∧
    ∀ i j : Fin 2, (scalarDifference x m i j).natAbs < 2 ^ 240 := by
  have h := integerMono_envelope_bounds b x m
  refine ⟨h.2.1.trans_lt he, ?_⟩
  intro i j
  have hs := h.2.2 i j
  have hc : rowEnvelope x m + (transferH m).natAbs ^ b ≤
      2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b := by omega
  exact (hs.trans hc).trans_lt he
#print axioms Paper7CRTAlgebra.differences_lt_of_envelope

theorem crt_trace_iff_of_envelope (b : ℕ) (x : PQ b) (m : ℤ)
    (he : 2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b < 2 ^ 240) :
    CRTTraceZero x m ↔ (integerMono x m).trace = 2 * (transferH m) ^ b := by
  have ht := (differences_lt_of_envelope b x m he).1
  have hp : (traceDifference x m).natAbs < aPrimes.prod :=
    ht.trans actual_aPrimes_product_bound
  change (∀ a ∈ aPrimes, (traceDifference x m : ZMod a) = 0) ↔ _
  rw [actual_bounded_integer_crt _ hp]
  exact sub_eq_zero
#print axioms Paper7CRTAlgebra.crt_trace_iff_of_envelope

theorem crt_scalar_iff_of_envelope (b : ℕ) (x : PQ b) (m : ℤ)
    (he : 2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b < 2 ^ 240) :
    CRTScalarZero x m ↔ integerMono x m =
      (transferH m) ^ b • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hs := (differences_lt_of_envelope b x m he).2
  constructor
  · intro hres
    have hz : scalarDifference x m = 0 := by
      apply Matrix.ext
      intro i j
      change scalarDifference x m i j = 0
      exact (actual_bounded_integer_crt _ ((hs i j).trans actual_aPrimes_product_bound)).mp
        (fun a ha => hres a ha i j)
    exact sub_eq_zero.mp hz
  · intro h
    have hz : scalarDifference x m = 0 := sub_eq_zero.mpr h
    intro a _ i j
    simp only [hz, Matrix.zero_apply, Int.cast_zero]
#print axioms Paper7CRTAlgebra.crt_scalar_iff_of_envelope

theorem crt_multiplicity_of_envelope (b : ℕ) (x : PQ b) (hb : 3 ≤ b)
    (m : ℤ) (hm : 2 ≤ m.natAbs)
    (he : 2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b < 2 ^ 240) :
    CRTMultiplicity x m = mult (SG b x.1 x.2) (m : ℝ) := by
  have hn := ordinary_cast_ne m hm
  have hL := (Paper7Lemma22.check_Lemma22 b x.1 x.2 hb).1
    (m : ℝ) hn.1 hn.2.1 hn.2.2.1
  have hS : CRTScalarZero x m ↔ Mono b x.1 x.2 (m : ℝ) = 1 :=
    (crt_scalar_iff_of_envelope b x m he).trans (integerMono_scalar_eq_iff b x m hm)
  have hT : CRTTraceZero x m ↔ (Mono b x.1 x.2 (m : ℝ)).trace = 2 :=
    (crt_trace_iff_of_envelope b x m he).trans (integerMono_trace_eq_iff b x m hm)
  unfold CRTMultiplicity
  by_cases hscalar : CRTScalarZero x m
  · rw [ite_eq_left hscalar]
    exact (hL.2.2.1.mpr (hS.mp hscalar)).symm
  · rw [ite_eq_right hscalar]
    by_cases htrace : CRTTraceZero x m
    · rw [ite_eq_left htrace]
      exact (hL.2.2.2.mpr ⟨fun h => hscalar (hS.mpr h), hT.mp htrace⟩).symm
    · rw [ite_eq_right htrace]
      have hnot2 : mult (SG b x.1 x.2) (m : ℝ) ≠ 2 :=
        fun h => hscalar (hS.mpr (hL.2.2.1.mp h))
      have hnot1 : mult (SG b x.1 x.2) (m : ℝ) ≠ 1 :=
        fun h => htrace (hT.mpr (hL.2.2.2.mp h).2)
      have hle := hL.2.1
      omega
#print axioms Paper7CRTAlgebra.crt_multiplicity_of_envelope

theorem reported_a_run_three_le_b (v : SearchVersion) (b N : ℕ)
    (hRun : ReportedARun v b N) : 3 ≤ b := by
  rcases hRun with ⟨_, hcases⟩ | ⟨_, hcases⟩ | ⟨_, hcases⟩ | ⟨_, hb, _⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcases
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcases
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcases
    omega
  · omega
#print axioms Paper7CRTAlgebra.reported_a_run_three_le_b

/-- All six original reported-leaf conclusions; no integrality or prime premise. -/
theorem reported_a_crt_conclusions (v : SearchVersion) (b N : ℕ)
    (hRun : ReportedARun v b N) (x : PQ b) (hx : x ∈ LeafSet v b N)
    (m : ℤ) (hm : 2 ≤ m.natAbs) (hM : m.natAbs ≤ 9) :
    2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b < 2 ^ 240 ∧
    (traceDifference x m).natAbs < 2 ^ 240 ∧
    (∀ i j : Fin 2, (scalarDifference x m i j).natAbs < 2 ^ 240) ∧
    (CRTTraceZero x m ↔ (integerMono x m).trace = 2 * (transferH m) ^ b) ∧
    (CRTScalarZero x m ↔ integerMono x m =
      (transferH m) ^ b • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ∧
    CRTMultiplicity x m = mult (SG b x.1 x.2) (m : ℝ) := by
  have hb := Paper7CRTEnvelope.reported_a_leaf_b_le_eighteen v b N hRun x hx
  have hB := Paper7CRTEnvelope.reported_a_leaf_budget v b N hRun x hx
  have hN := Paper7CRTEnvelope.reported_a_run_N_le_fortynine v b N hRun
  have he := (Paper7CRTEnvelope.budget_envelope_bound b N x hb hB hN m hm hM).2.2.2
  have hd := differences_lt_of_envelope b x m he
  exact ⟨he, hd.1, hd.2, crt_trace_iff_of_envelope b x m he,
    crt_scalar_iff_of_envelope b x m he,
    crt_multiplicity_of_envelope b x (reported_a_run_three_le_b v b N hRun) m hm he⟩
#print axioms Paper7CRTAlgebra.reported_a_crt_conclusions

/-- Conditional assembly ONLY: four concrete prime certificates are still missing.
This is deliberately not named check_LegacyTransferCRTExactness and adds no credit. -/
theorem legacy_transfer_crt_of_prime_certificates
    (hprime : ∀ a ∈ aPrimes, a.Prime) : LegacyTransferCRTExactness := by
  refine ⟨?_, actual_aPrimes_pairwise_coprime, actual_aPrimes_product_bound,
    actual_bounded_integer_crt, integerMono_scaling, ?_, reported_a_crt_conclusions⟩
  · intro a ha
    exact ⟨hprime a ha, actual_aPrimes_upper_bound a ha⟩
  · intro b x m _hm
    exact integerMono_envelope_bounds b x m
#print axioms Paper7CRTAlgebra.legacy_transfer_crt_of_prime_certificates

end Paper7CRTAlgebra
