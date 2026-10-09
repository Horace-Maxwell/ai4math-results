import Research.Backfill.Paper6.LiteralCounts

/-! Bounded suffix checks; source only, not compiled. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

-- Residual total budget 7; residual column budgets [3, 1, 1].
set_option maxHeartbeats 200000 in
theorem certificate3_3_2 : suffix3 3 2 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [3, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate3_3_3 : suffix3 3 3 = true := by
  decide +kernel

-- Residual total budget 8; residual column budgets [2, 2, 2].
set_option maxHeartbeats 200000 in
theorem certificate3_4_0 : suffix3 4 0 = true := by
  decide +kernel

-- Residual total budget 7; residual column budgets [2, 1, 1].
set_option maxHeartbeats 200000 in
theorem certificate3_4_1 : suffix3 4 1 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [2, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate3_4_2 : suffix3 4 2 = true := by
  decide +kernel

-- Residual total budget 7; residual column budgets [1, 1, 1].
set_option maxHeartbeats 200000 in
theorem certificate3_5_0 : suffix3 5 0 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [1, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate3_5_1 : suffix3 5 1 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [0, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate3_6_0 : suffix3 6 0 = true := by
  decide +kernel

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.certificate3_3_2
#print axioms Paper6LiteralLouWang.certificate3_3_3
#print axioms Paper6LiteralLouWang.certificate3_4_0
#print axioms Paper6LiteralLouWang.certificate3_4_1
#print axioms Paper6LiteralLouWang.certificate3_4_2
#print axioms Paper6LiteralLouWang.certificate3_5_0
#print axioms Paper6LiteralLouWang.certificate3_5_1
#print axioms Paper6LiteralLouWang.certificate3_6_0
