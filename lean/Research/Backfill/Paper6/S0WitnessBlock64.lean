import Research.Backfill.Paper6.S0WitnessBasic

/-! Historical data transcribed without changing its masks or their order.
Source SHA-256: 784bca3ba1e3012078d29156811132a726641d51f75e3d04c125f2efa085939b.
Candidate shard 64: weights 16384 through 16639; 1 rows.
Each row is checked independently. No runtime or acceptance is claimed. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6S0Witnesses

def row_16384 : ℕ × List ℕ := (16384, [0])

set_option maxHeartbeats 200000 in
theorem row_16384_valid : RowData row_16384 := by
  decide +kernel

def rows_64 : List (ℕ × List ℕ) := [
  row_16384]

theorem rows_64_valid : ∀ t ∈ rows_64, RowData t := by
  simp only [rows_64, List.forall_mem_cons]
  exact ⟨row_16384_valid, (by simp)⟩

set_option maxHeartbeats 200000 in
theorem coverage_64 : ∀ i : Fin 256,
    normalizedS0 (256 * 64 + i.val) →
      256 * 64 + i.val ∈ rows_64.map Prod.fst := by
  decide +kernel

theorem block_64 : BlockResult 64 :=
  block_sound 64 rows_64 rows_64_valid coverage_64

end Paper6S0Witnesses

#print axioms Paper6S0Witnesses.row_16384
#print axioms Paper6S0Witnesses.row_16384_valid
#print axioms Paper6S0Witnesses.rows_64
#print axioms Paper6S0Witnesses.rows_64_valid
#print axioms Paper6S0Witnesses.coverage_64
#print axioms Paper6S0Witnesses.block_64
