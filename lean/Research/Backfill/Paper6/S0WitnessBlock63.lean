import Research.Backfill.Paper6.S0WitnessBasic

/-! Historical data transcribed without changing its masks or their order.
Source SHA-256: 784bca3ba1e3012078d29156811132a726641d51f75e3d04c125f2efa085939b.
Candidate shard 63: weights 16128 through 16383; 8 rows.
Each row is checked independently. No runtime or acceptance is claimed. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6S0Witnesses

def row_16128 : ℕ × List ℕ := (16128, [0, 3850])

set_option maxHeartbeats 200000 in
theorem row_16128_valid : RowData row_16128 := by
  decide +kernel

def row_16130 : ℕ × List ℕ := (16130, [0, 127, 16256])

set_option maxHeartbeats 200000 in
theorem row_16130_valid : RowData row_16130 := by
  decide +kernel

def row_16132 : ℕ × List ℕ := (16132, [0, 1777, 15622])

set_option maxHeartbeats 200000 in
theorem row_16132_valid : RowData row_16132 := by
  decide +kernel

def row_16136 : ℕ × List ℕ := (16136, [0, 5030, 10355])

set_option maxHeartbeats 200000 in
theorem row_16136_valid : RowData row_16136 := by
  decide +kernel

def row_16144 : ℕ × List ℕ := (16144, [0, 3498, 5707])

set_option maxHeartbeats 200000 in
theorem row_16144_valid : RowData row_16144 := by
  decide +kernel

def row_16160 : ℕ × List ℕ := (16160, [0, 3481, 12044])

set_option maxHeartbeats 200000 in
theorem row_16160_valid : RowData row_16160 := by
  decide +kernel

def row_16192 : ℕ × List ℕ := (16192, [0, 2546, 7618])

set_option maxHeartbeats 200000 in
theorem row_16192_valid : RowData row_16192 := by
  decide +kernel

def row_16256 : ℕ × List ℕ := (16256, [0, 5788])

set_option maxHeartbeats 200000 in
theorem row_16256_valid : RowData row_16256 := by
  decide +kernel

def rows_63 : List (ℕ × List ℕ) := [
  row_16128,
  row_16130,
  row_16132,
  row_16136,
  row_16144,
  row_16160,
  row_16192,
  row_16256]

theorem rows_63_valid : ∀ t ∈ rows_63, RowData t := by
  simp only [rows_63, List.forall_mem_cons]
  exact ⟨row_16128_valid, row_16130_valid, row_16132_valid, row_16136_valid, row_16144_valid, row_16160_valid, row_16192_valid, row_16256_valid, (by simp)⟩

set_option maxHeartbeats 200000 in
theorem coverage_63 : ∀ i : Fin 256,
    normalizedS0 (256 * 63 + i.val) →
      256 * 63 + i.val ∈ rows_63.map Prod.fst := by
  decide +kernel

theorem block_63 : BlockResult 63 :=
  block_sound 63 rows_63 rows_63_valid coverage_63

end Paper6S0Witnesses

#print axioms Paper6S0Witnesses.row_16128
#print axioms Paper6S0Witnesses.row_16128_valid
#print axioms Paper6S0Witnesses.row_16130
#print axioms Paper6S0Witnesses.row_16130_valid
#print axioms Paper6S0Witnesses.row_16132
#print axioms Paper6S0Witnesses.row_16132_valid
#print axioms Paper6S0Witnesses.row_16136
#print axioms Paper6S0Witnesses.row_16136_valid
#print axioms Paper6S0Witnesses.row_16144
#print axioms Paper6S0Witnesses.row_16144_valid
#print axioms Paper6S0Witnesses.row_16160
#print axioms Paper6S0Witnesses.row_16160_valid
#print axioms Paper6S0Witnesses.row_16192
#print axioms Paper6S0Witnesses.row_16192_valid
#print axioms Paper6S0Witnesses.row_16256
#print axioms Paper6S0Witnesses.row_16256_valid
#print axioms Paper6S0Witnesses.rows_63
#print axioms Paper6S0Witnesses.rows_63_valid
#print axioms Paper6S0Witnesses.coverage_63
#print axioms Paper6S0Witnesses.block_63
