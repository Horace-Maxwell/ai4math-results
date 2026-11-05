import Research.Backfill.Paper7.InertiaBlockElimination

set_option autoImplicit false

noncomputable section

namespace Paper7Pivots

open Matrix Polynomial BackfillPaper7.Challenge
open scoped Matrix

/-- Exactly the list appearing in the frozen Lemma52; the first coefficient is zero. -/
def pivotEntries (N : ℕ) (t a : ℕ → ℝ) : List (ℝ × ℝ) :=
  (List.range N).map (fun k => (t k, if k = 0 then 0 else a (k-1)^2))
#print axioms Paper7Pivots.pivotEntries

def tailEntries (N : ℕ) (t a : ℕ → ℝ) : List (ℝ × ℝ) :=
  (List.range N).map (fun k => (t (k+1), a k ^ 2))
#print axioms Paper7Pivots.tailEntries

def pivotSign (pos : Bool) (d : ℝ) : ℕ :=
  if (pos = true ∧ 0 < d) ∨ (pos = false ∧ d < 0) then 1 else 0
#print axioms Paper7Pivots.pivotSign

def schurDiagonal (t a : ℕ → ℝ) (d : ℝ) : ℕ → ℝ :=
  fun k => if k = 0 then t 1 - a 0 ^ 2 / d else t (k+1)
#print axioms Paper7Pivots.schurDiagonal

theorem pivotEntries_succ (N : ℕ) (t a : ℕ → ℝ) :
    pivotEntries (N+1) t a = (t 0, 0) :: tailEntries N t a := by
  simp [pivotEntries, tailEntries, List.range_succ_eq_map, List.map_map,
    Function.comp_def]
#print axioms Paper7Pivots.pivotEntries_succ

theorem tailEntries_succ (N : ℕ) (t a : ℕ → ℝ) :
    tailEntries (N+1) t a = (t 1, a 0 ^ 2) ::
      tailEntries N (fun k => t (k+1)) (fun k => a (k+1)) := by
  simp [tailEntries, List.range_succ_eq_map, List.map_map, Function.comp_def]
#print axioms Paper7Pivots.tailEntries_succ

theorem pivCount_head_coefficient (pos : Bool) (d c c' : ℝ) (rest : List (ℝ × ℝ)) :
    pivCount pos ((d,c) :: rest) none = pivCount pos ((d,c') :: rest) none := by
  conv_lhs => rw [pivCount.eq_def]
  conv_rhs => rw [pivCount.eq_def]
#print axioms Paper7Pivots.pivCount_head_coefficient

theorem pivCount_some_head (pos : Bool) (t c d : ℝ) (rest : List (ℝ × ℝ)) :
    pivCount pos ((t,c) :: rest) (some d) =
      pivCount pos ((t-c/d,0) :: rest) none := by
  conv_lhs => rw [pivCount.eq_def]
  conv_rhs => rw [pivCount.eq_def]
#print axioms Paper7Pivots.pivCount_some_head

theorem tailEntries_restart (pos : Bool) (N : ℕ) (t a : ℕ → ℝ) :
    pivCount pos (tailEntries N t a) none =
      pivCount pos (pivotEntries N (fun k => t (k+1)) (fun k => a (k+1))) none := by
  cases N with
  | zero => rfl
  | succ N =>
    rw [tailEntries_succ, pivotEntries_succ]
    exact pivCount_head_coefficient pos (t 1) (a 0 ^ 2) 0 _
#print axioms Paper7Pivots.tailEntries_restart

theorem tailEntries_schur (pos : Bool) (N : ℕ) (t a : ℕ → ℝ) (d : ℝ) :
    pivCount pos (tailEntries N t a) (some d) =
      pivCount pos (pivotEntries N (schurDiagonal t a d) (fun k => a (k+1))) none := by
  cases N with
  | zero => rfl
  | succ N =>
    rw [tailEntries_succ, pivotEntries_succ, pivCount_some_head]
    simp only [schurDiagonal, ite_true]
    congr 2
#print axioms Paper7Pivots.tailEntries_schur

/-- Exact ordinary pivot step, with no sign restriction on the nonzero pivot. -/
theorem pivCount_nonzero_step (pos : Bool) (N : ℕ) (t a : ℕ → ℝ) (h : t 0 ≠ 0) :
    pivCount pos (pivotEntries (N+1) t a) none =
      pivotSign pos (t 0) +
        pivCount pos (pivotEntries N (schurDiagonal t a (t 0)) (fun k => a (k+1))) none := by
  rw [pivotEntries_succ]
  rw [pivCount.eq_def]
  simp only [h, ite_false]
  change pivotSign pos (t 0) + _ = _
  rw [tailEntries_schur]
#print axioms Paper7Pivots.pivCount_nonzero_step

/-- Exact frozen zero-pivot rule: one count for either sign, discard two indices,
and restart with no previous pivot. This is an identity of the original recursion. -/
theorem pivCount_zero_step (pos : Bool) (N : ℕ) (t a : ℕ → ℝ) (h : t 0 = 0) :
    pivCount pos (pivotEntries (N+2) t a) none =
      1 + pivCount pos (pivotEntries N (fun k => t (k+2)) (fun k => a (k+2))) none := by
  rw [show N+2 = (N+1)+1 by omega, pivotEntries_succ, tailEntries_succ]
  simp only [pivCount, h, ite_true]
  rw [tailEntries_restart]
#print axioms Paper7Pivots.pivCount_zero_step

theorem pivotSign_true (d : ℝ) : pivotSign true d = if 0 < d then 1 else 0 := by
  simp [pivotSign]
#print axioms Paper7Pivots.pivotSign_true

theorem pivotSign_false (d : ℝ) : pivotSign false d = if d < 0 then 1 else 0 := by
  simp [pivotSign]
#print axioms Paper7Pivots.pivotSign_false

theorem tridiagGen_isHermitian (N : ℕ) (t a : ℕ → ℝ) :
    (tridiagGen N t a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases he : i = j
  · subst j
    simp [tridiagGen]
  · change (if j = i then t j.val else if j.val + 1 = i.val then a j.val
        else if i.val + 1 = j.val then a i.val else 0) =
      (if i = j then t i.val else if i.val + 1 = j.val then a i.val
        else if j.val + 1 = i.val then a j.val else 0)
    rw [ite_eq_right (Ne.symm he), ite_eq_right he]
    by_cases hf : i.val + 1 = j.val
    · have hb : j.val + 1 ≠ i.val := by omega
      rw [ite_eq_right hb, ite_eq_left hf, ite_eq_left hf]
    · by_cases hb : j.val + 1 = i.val
      · rw [ite_eq_left hb, ite_eq_right hf, ite_eq_left hb]
      · rw [ite_eq_right hb, ite_eq_right hf, ite_eq_right hf, ite_eq_right hb]

#print axioms Paper7Pivots.tridiagGen_isHermitian

/-- The actual empty matrix, with no nonempty-index assumption. -/
theorem lemma52_zero (t a : ℕ → ℝ) :
    pivCount true (pivotEntries 0 t a) none = nPos (tridiagGen 0 t a) ∧
      pivCount false (pivotEntries 0 t a) none = nNeg (tridiagGen 0 t a) := by
  simp [pivotEntries, pivCount, nPos, nNeg, eigs, Matrix.charpoly_isEmpty]
#print axioms Paper7Pivots.lemma52_zero

/-- The terminal one-point case includes a zero diagonal pivot. -/
theorem lemma52_one (t a : ℕ → ℝ) :
    pivCount true (pivotEntries 1 t a) none = nPos (tridiagGen 1 t a) ∧
      pivCount false (pivotEntries 1 t a) none = nNeg (tridiagGen 1 t a) := by
  have hc : (tridiagGen 1 t a).charpoly = X - C (t 0) := by
    rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
    simp [tridiagGen]
  by_cases h : t 0 = 0 <;>
    simp [pivotEntries, pivCount, nPos, nNeg, eigs, hc, h, Multiset.filter_singleton]
  all_goals split_ifs <;> simp_all
#print axioms Paper7Pivots.lemma52_one

/-- A genuine zero-pivot two-point tridiagonal matrix has both counts equal to one. -/
theorem lemma52_two_zero (t a : ℕ → ℝ) (ht : t 0 = 0) (ha : a 0 ≠ 0) :
    pivCount true (pivotEntries 2 t a) none = nPos (tridiagGen 2 t a) ∧
      pivCount false (pivotEntries 2 t a) none = nNeg (tridiagGen 2 t a) := by
  have hm : tridiagGen 2 t a = Paper7Inertia.zeroPivotBlock (a 0) (t 1) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [tridiagGen, Paper7Inertia.zeroPivotBlock, ht]
  have hi := Paper7Inertia.zeroPivotBlock_inertia (a 0) (t 1) ha
  rw [hm]
  rw [hi.1, hi.2]
  constructor <;> simp [pivotEntries, List.range_succ, pivCount, ht]
#print axioms Paper7Pivots.lemma52_two_zero

end Paper7Pivots
