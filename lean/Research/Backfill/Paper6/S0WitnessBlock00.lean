import Research.Backfill.Paper6.S0WitnessBasic

/-! Historical data transcribed without changing its masks or their order.
Source SHA-256: 784bca3ba1e3012078d29156811132a726641d51f75e3d04c125f2efa085939b.
Candidate shard 0: weights 0 through 255; 8 rows.
Each row is checked independently. No runtime or acceptance is claimed. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6S0Witnesses

def row_00000 : ℕ × List ℕ := (0, [])

set_option maxHeartbeats 200000 in
theorem row_00000_valid : RowData row_00000 := by
  decide +kernel

def row_00128 : ℕ × List ℕ := (128, [5788])

set_option maxHeartbeats 200000 in
theorem row_00128_valid : RowData row_00128 := by
  decide +kernel

def row_00192 : ℕ × List ℕ := (192, [2546, 7618])

set_option maxHeartbeats 200000 in
theorem row_00192_valid : RowData row_00192 := by
  decide +kernel

def row_00224 : ℕ × List ℕ := (224, [3481, 12044])

set_option maxHeartbeats 200000 in
theorem row_00224_valid : RowData row_00224 := by
  decide +kernel

def row_00240 : ℕ × List ℕ := (240, [3498, 5707])

set_option maxHeartbeats 200000 in
theorem row_00240_valid : RowData row_00240 := by
  decide +kernel

def row_00248 : ℕ × List ℕ := (248, [5030, 10355])

set_option maxHeartbeats 200000 in
theorem row_00248_valid : RowData row_00248 := by
  decide +kernel

def row_00252 : ℕ × List ℕ := (252, [1777, 15622])

set_option maxHeartbeats 200000 in
theorem row_00252_valid : RowData row_00252 := by
  decide +kernel

def row_00254 : ℕ × List ℕ := (254, [127, 16256])

set_option maxHeartbeats 200000 in
theorem row_00254_valid : RowData row_00254 := by
  decide +kernel

def rows_00 : List (ℕ × List ℕ) := [
  row_00000,
  row_00128,
  row_00192,
  row_00224,
  row_00240,
  row_00248,
  row_00252,
  row_00254]

theorem rows_00_valid : ∀ t ∈ rows_00, RowData t := by
  simp only [rows_00, List.forall_mem_cons]
  exact ⟨row_00000_valid, row_00128_valid, row_00192_valid, row_00224_valid, row_00240_valid, row_00248_valid, row_00252_valid, row_00254_valid, (by simp)⟩

set_option maxHeartbeats 200000 in
theorem coverage_00 : ∀ i : Fin 256,
    normalizedS0 (256 * 0 + i.val) →
      256 * 0 + i.val ∈ rows_00.map Prod.fst := by
  decide +kernel

theorem block_00 : BlockResult 0 :=
  block_sound 0 rows_00 rows_00_valid coverage_00

end Paper6S0Witnesses

#print axioms Paper6S0Witnesses.row_00000
#print axioms Paper6S0Witnesses.row_00000_valid
#print axioms Paper6S0Witnesses.row_00128
#print axioms Paper6S0Witnesses.row_00128_valid
#print axioms Paper6S0Witnesses.row_00192
#print axioms Paper6S0Witnesses.row_00192_valid
#print axioms Paper6S0Witnesses.row_00224
#print axioms Paper6S0Witnesses.row_00224_valid
#print axioms Paper6S0Witnesses.row_00240
#print axioms Paper6S0Witnesses.row_00240_valid
#print axioms Paper6S0Witnesses.row_00248
#print axioms Paper6S0Witnesses.row_00248_valid
#print axioms Paper6S0Witnesses.row_00252
#print axioms Paper6S0Witnesses.row_00252_valid
#print axioms Paper6S0Witnesses.row_00254
#print axioms Paper6S0Witnesses.row_00254_valid
#print axioms Paper6S0Witnesses.rows_00
#print axioms Paper6S0Witnesses.rows_00_valid
#print axioms Paper6S0Witnesses.coverage_00
#print axioms Paper6S0Witnesses.block_00
