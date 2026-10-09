import Research.Backfill.Paper6.LiteralCounts

/-! Source-only small suffixes; no external weight computation. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

-- At most 6435 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_3_1_0_1_0_0_0 : suffix4Depth7 3 1 0 1 0 0 0 = true := by
  decide +kernel

-- At most 3003 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_3_1_0_1_0_0_1 : suffix4Depth7 3 1 0 1 0 0 1 = true := by
  decide +kernel

-- At most 5005 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_3_1_0_1_0_1 : suffix4Depth6 3 1 0 1 0 1 = true := by
  decide +kernel

-- At most 6435 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_3_1_1_0_0_0_0 : suffix4Depth7 3 1 1 0 0 0 0 = true := by
  decide +kernel

-- At most 3003 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_3_1_1_0_0_0_1 : suffix4Depth7 3 1 1 0 0 0 1 = true := by
  decide +kernel

-- At most 5005 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_3_1_1_0_0_1 : suffix4Depth6 3 1 1 0 0 1 = true := by
  decide +kernel

-- At most 6435 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_3_2_0_0_0_0_0 : suffix4Depth7 3 2 0 0 0 0 0 = true := by
  decide +kernel

-- At most 3003 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_3_2_0_0_0_0_1 : suffix4Depth7 3 2 0 0 0 0 1 = true := by
  decide +kernel

-- At most 5005 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_3_2_0_0_0_1 : suffix4Depth6 3 2 0 0 0 1 = true := by
  decide +kernel

-- At most 6435 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_0_0_0_0_0 : suffix4Depth8 4 0 0 0 0 0 0 0 = true := by
  decide +kernel

-- At most 3432 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_0_0_0_0_1 : suffix4Depth8 4 0 0 0 0 0 0 1 = true := by
  decide +kernel

-- At most 1716 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_0_0_0_0_2 : suffix4Depth8 4 0 0 0 0 0 0 2 = true := by
  decide +kernel

-- At most 6435 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_0_0_0_1 : suffix4Depth7 4 0 0 0 0 0 1 = true := by
  decide +kernel

-- At most 3003 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_0_0_0_2 : suffix4Depth7 4 0 0 0 0 0 2 = true := by
  decide +kernel

-- At most 6435 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_0_0_1_0 : suffix4Depth7 4 0 0 0 0 1 0 = true := by
  decide +kernel

-- At most 3003 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_0_0_1_1 : suffix4Depth7 4 0 0 0 0 1 1 = true := by
  decide +kernel

-- At most 5005 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_0_0_2 : suffix4Depth6 4 0 0 0 0 2 = true := by
  decide +kernel

-- At most 6435 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_0_1_0_0 : suffix4Depth7 4 0 0 0 1 0 0 = true := by
  decide +kernel

-- At most 3003 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_0_1_0_1 : suffix4Depth7 4 0 0 0 1 0 1 = true := by
  decide +kernel

-- At most 5005 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_0_1_1 : suffix4Depth6 4 0 0 0 1 1 = true := by
  decide +kernel

-- At most 6435 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_1_0_0_0 : suffix4Depth7 4 0 0 1 0 0 0 = true := by
  decide +kernel

-- At most 3003 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_1_0_0_1 : suffix4Depth7 4 0 0 1 0 0 1 = true := by
  decide +kernel

-- At most 5005 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_0_1_0_1 : suffix4Depth6 4 0 0 1 0 1 = true := by
  decide +kernel

-- At most 6435 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_1_0_0_0_0 : suffix4Depth7 4 0 1 0 0 0 0 = true := by
  decide +kernel

-- At most 3003 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_1_0_0_0_1 : suffix4Depth7 4 0 1 0 0 0 1 = true := by
  decide +kernel

-- At most 5005 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_0_1_0_0_1 : suffix4Depth6 4 0 1 0 0 1 = true := by
  decide +kernel

-- At most 6435 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_1_0_0_0_0_0 : suffix4Depth7 4 1 0 0 0 0 0 = true := by
  decide +kernel

-- At most 3003 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_1_0_0_0_0_1 : suffix4Depth7 4 1 0 0 0 0 1 = true := by
  decide +kernel

-- At most 5005 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_4_1_0_0_0_1 : suffix4Depth6 4 1 0 0 0 1 = true := by
  decide +kernel

-- At most 6435 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_5_0_0_0_0_0_0 : suffix4Depth7 5 0 0 0 0 0 0 = true := by
  decide +kernel

-- At most 3003 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_5_0_0_0_0_0_1 : suffix4Depth7 5 0 0 0 0 0 1 = true := by
  decide +kernel

-- At most 5005 assignments by the residual-total composition bound.
set_option maxHeartbeats 200000 in
theorem leaf4_5_0_0_0_0_1 : suffix4Depth6 5 0 0 0 0 1 = true := by
  decide +kernel

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.leaf4_3_1_0_1_0_0_0
#print axioms Paper6LiteralLouWang.leaf4_3_1_0_1_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_3_1_0_1_0_1
#print axioms Paper6LiteralLouWang.leaf4_3_1_1_0_0_0_0
#print axioms Paper6LiteralLouWang.leaf4_3_1_1_0_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_3_1_1_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_3_2_0_0_0_0_0
#print axioms Paper6LiteralLouWang.leaf4_3_2_0_0_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_3_2_0_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_0_0_0_0_0
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_0_0_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_0_0_0_0_2
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_0_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_0_0_0_2
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_0_0_1_0
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_0_0_1_1
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_0_0_2
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_0_1_0_0
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_0_1_0_1
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_0_1_1
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_1_0_0_0
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_1_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_4_0_0_1_0_1
#print axioms Paper6LiteralLouWang.leaf4_4_0_1_0_0_0_0
#print axioms Paper6LiteralLouWang.leaf4_4_0_1_0_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_4_0_1_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_4_1_0_0_0_0_0
#print axioms Paper6LiteralLouWang.leaf4_4_1_0_0_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_4_1_0_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_5_0_0_0_0_0_0
#print axioms Paper6LiteralLouWang.leaf4_5_0_0_0_0_0_1
#print axioms Paper6LiteralLouWang.leaf4_5_0_0_0_0_1
