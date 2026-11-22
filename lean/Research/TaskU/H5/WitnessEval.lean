import Research.TaskU.H5.WitnessBase

namespace TaskU.H5.WitnessCertificate

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Check each zero below the diagonal by the five-term product formula. -/
theorem transformed_upper : transformed.IsUpperTriangular := by
  have checks : ∀ i j : Fin 125, (decide (i ≤ j) || decide (transformed i j = 0)) = true := by
    decide +kernel
  intro i j hij
  have hij' : ¬ i ≤ j := not_le.mpr hij
  simpa only [hij', decide_false, Bool.false_or, decide_eq_true_eq] using checks i j

theorem left_diagonal : (∏ i : Fin 125, left i i) = 176045096572546062966544272254876263965635740262784938036910791996960375553533805075368167245146010315544762400826586765775792054071352993987153732521238200320000 := by
  decide +kernel

theorem transformed_diagonal : (∏ i : Fin 125, transformed i i) = 72140099938884626799523345932500023529752833503880885184035402237123404856356675022432574618481327350102081388573812485617910049661430825809340590899200000000000000000000000000000000 := by
  decide +kernel

end TaskU.H5.WitnessCertificate
