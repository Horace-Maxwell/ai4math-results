import Research.Backfill.Paper7.EnumeratedRows

/-! Source-only candidate. List/PQ coverage includes b=0 and every empty row.
The imported list-enumeration proof remains an uncompiled Root candidate. -/
set_option autoImplicit false
noncomputable section

namespace Paper7Pruning
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

def pqRow {b : ℕ} (x : PQ b) : List (ℕ × ℕ) :=
  List.ofFn (fun i => (x.1 i, x.2 i))
#print axioms Paper7Pruning.pqRow

theorem pqRow_length {b : ℕ} (x : PQ b) : (pqRow x).length = b := by
  simp only [pqRow, List.length_ofFn]
#print axioms Paper7Pruning.pqRow_length

theorem rowPQ_pqRow {b : ℕ} (x : PQ b) : rowPQ b (pqRow x) = x := by
  have hget (i : Fin b) : (pqRow x).getD i.val (0, 0) = (x.1 i, x.2 i) := by
    rw [← List.getElem_eq_getD (h := by simpa only [pqRow_length] using i.isLt) (0, 0)]
    simp only [pqRow, List.getElem_ofFn]
  apply Prod.ext
  · funext i
    exact congrArg Prod.fst (hget i)
  · funext i
    exact congrArg Prod.snd (hget i)
#print axioms Paper7Pruning.rowPQ_pqRow

theorem pqRow_rowPQ (b : ℕ) (row : List (ℕ × ℕ)) (hlen : row.length = b) :
    pqRow (rowPQ b row) = row := by
  subst b
  have hget (i : Fin row.length) : row.getD i.val (0, 0) = row[i.val] :=
    (List.getElem_eq_getD (h := i.isLt) (0, 0)).symm
  change List.ofFn (fun i : Fin row.length =>
    ((row.getD i.val (0, 0)).1, (row.getD i.val (0, 0)).2)) = row
  simp only [Prod.mk.eta, hget, List.ofFn_getElem]
#print axioms Paper7Pruning.pqRow_rowPQ

theorem rowWeight_pqRow {b : ℕ} (x : PQ b) : rowWeight (pqRow x) = weight x := by
  rw [rowWeight, pqRow, List.map_ofFn, Fin.sum_ofFn]
  simp only [Function.comp_def, weight, pSum, qSum, Finset.sum_add_distrib,
    Finset.mul_sum]
#print axioms Paper7Pruning.rowWeight_pqRow

theorem weight_rowPQ (b : ℕ) (row : List (ℕ × ℕ)) (hlen : row.length = b) :
    weight (rowPQ b row) = rowWeight row := by
  have h := rowWeight_pqRow (rowPQ b row)
  rw [pqRow_rowPQ b row hlen] at h
  exact h.symm
#print axioms Paper7Pruning.weight_rowPQ

theorem enumerated_eq_budget (b N : ℕ) (hbN : b ≤ N) :
    Enumerated b N = {x | Budget b N x} := by
  ext x
  constructor
  · rintro ⟨row, hrow, hlen, hrowx, hpositive⟩
    obtain ⟨_, hw⟩ := (mem_enumerateRows_iff b (N-b) row).mp hrow
    have hweight : weight x = rowWeight row := by
      rw [← hrowx]
      exact weight_rowPQ b row hlen
    exact ⟨hpositive, by omega⟩
  · rintro ⟨hpositive, hbudget⟩
    refine ⟨pqRow x, ?_, pqRow_length x, rowPQ_pqRow x, hpositive⟩
    apply (mem_enumerateRows_iff b (N-b) (pqRow x)).mpr
    rw [rowWeight_pqRow]
    exact ⟨pqRow_length x, by omega⟩
#print axioms Paper7Pruning.enumerated_eq_budget

end Paper7Pruning
