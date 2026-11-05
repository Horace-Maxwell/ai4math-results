import Research.Backfill.Paper7.LegacyTransfer

/-! Source-only author candidate by Codex subagent p6_binding_spotcheck.
The bounds use the actual reversed matrix product in integerMono. Only the
commutative natural-number product of row bounds is reordered. The conclusions
hold for every integer m, including the exceptional values. This file asserts
neither CRT correctness nor compilation/kernel acceptance of this candidate. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix

namespace Paper7CRTAlgebra
open BackfillPaper7.Challenge.Legacy

/-- The absolute row sum of an integer two-by-two matrix. -/
def matrixRowNorm (A : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) : ℕ :=
  (A i 0).natAbs + (A i 1).natAbs
#print axioms Paper7CRTAlgebra.matrixRowNorm

theorem entry_natAbs_le_matrixRowNorm (A : Matrix (Fin 2) (Fin 2) ℤ)
    (i j : Fin 2) : (A i j).natAbs ≤ matrixRowNorm A i := by
  fin_cases j
  · exact Nat.le_add_right _ _
  · exact Nat.le_add_left _ _
#print axioms Paper7CRTAlgebra.entry_natAbs_le_matrixRowNorm

/-- Row-sum submultiplicativity, proved entry by entry over the integers. -/
theorem matrixRowNorm_mul_le (A B : Matrix (Fin 2) (Fin 2) ℤ) (a b : ℕ)
    (hA : ∀ i, matrixRowNorm A i ≤ a) (hB : ∀ i, matrixRowNorm B i ≤ b)
    (i : Fin 2) : matrixRowNorm (A * B) i ≤ a * b := by
  calc
    matrixRowNorm (A * B) i =
        (A i 0 * B 0 0 + A i 1 * B 1 0).natAbs +
          (A i 0 * B 0 1 + A i 1 * B 1 1).natAbs := by
      simp only [matrixRowNorm, Matrix.mul_apply, Fin.sum_univ_two]
    _ ≤ ((A i 0 * B 0 0).natAbs + (A i 1 * B 1 0).natAbs) +
        ((A i 0 * B 0 1).natAbs + (A i 1 * B 1 1).natAbs) :=
      Nat.add_le_add (Int.natAbs_add_le _ _) (Int.natAbs_add_le _ _)
    _ = (A i 0).natAbs * matrixRowNorm B 0 +
        (A i 1).natAbs * matrixRowNorm B 1 := by
      simp only [Int.natAbs_mul, matrixRowNorm]
      ring
    _ ≤ (A i 0).natAbs * b + (A i 1).natAbs * b :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (hB 0)) (Nat.mul_le_mul_left _ (hB 1))
    _ = matrixRowNorm A i * b := by unfold matrixRowNorm; ring
    _ ≤ a * b := Nat.mul_le_mul_right b (hA i)
#print axioms Paper7CRTAlgebra.matrixRowNorm_mul_le

/-- List order is preserved in the matrix product. -/
theorem matrixRowNorm_list_prod_le {α : Type*} (l : List α)
    (F : α → Matrix (Fin 2) (Fin 2) ℤ) (c : α → ℕ)
    (hc : ∀ a ∈ l, ∀ i, matrixRowNorm (F a) i ≤ c a) :
    ∀ i, matrixRowNorm (l.map F).prod i ≤ (l.map c).prod := by
  revert hc
  induction l with
  | nil =>
      intro _ i
      fin_cases i <;> simp [matrixRowNorm]
  | cons a l ih =>
      intro hc i
      simp only [List.map_cons, List.prod_cons]
      exact matrixRowNorm_mul_le (F a) (l.map F).prod (c a) (l.map c).prod
        (hc a (by simp)) (ih (fun z hz => hc z (by simp [hz]))) i
#print axioms Paper7CRTAlgebra.matrixRowNorm_list_prod_le

theorem integerTk_matrixRowNorm_le (b : ℕ) (x : PQ b) (m : ℤ)
    (k : Fin b) (i : Fin 2) :
    matrixRowNorm (integerTk x m k) i ≤
      (transferS x m k).natAbs + (transferH m).natAbs := by
  fin_cases i
  · simp [matrixRowNorm, integerTk]
  · simp [matrixRowNorm, integerTk]
#print axioms Paper7CRTAlgebra.integerTk_matrixRowNorm_le

/-- The reversed transfer product has the frozen product of row bounds. -/
theorem integerMono_matrixRowNorm_le (b : ℕ) (x : PQ b) (m : ℤ)
    (i : Fin 2) : matrixRowNorm (integerMono x m) i ≤ rowEnvelope x m := by
  let c : Fin b → ℕ := fun k => (transferS x m k).natAbs + (transferH m).natAbs
  have hprod : (((List.finRange b).reverse).map c).prod = rowEnvelope x m := by
    calc
      (((List.finRange b).reverse).map c).prod = ((List.finRange b).map c).prod := by
        rw [List.map_reverse, List.prod_reverse]
      _ = ∏ k : Fin b, c k := (Fin.prod_univ_def c).symm
      _ = rowEnvelope x m := rfl
  have hlist := matrixRowNorm_list_prod_le (List.finRange b).reverse
    (integerTk x m) c (fun k _ => integerTk_matrixRowNorm_le b x m k) i
  change matrixRowNorm (integerMono x m) i ≤ (((List.finRange b).reverse).map c).prod at hlist
  rw [hprod] at hlist
  exact hlist
#print axioms Paper7CRTAlgebra.integerMono_matrixRowNorm_le

theorem integerMono_entry_natAbs_le (b : ℕ) (x : PQ b) (m : ℤ)
    (i j : Fin 2) : (integerMono x m i j).natAbs ≤ rowEnvelope x m :=
  (entry_natAbs_le_matrixRowNorm (integerMono x m) i j).trans
    (integerMono_matrixRowNorm_le b x m i)
#print axioms Paper7CRTAlgebra.integerMono_entry_natAbs_le

theorem traceDifference_natAbs_le (b : ℕ) (x : PQ b) (m : ℤ) :
    (traceDifference x m).natAbs ≤
      2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b := by
  have h00 := integerMono_entry_natAbs_le b x m 0 0
  have h11 := integerMono_entry_natAbs_le b x m 1 1
  have htrace : (integerMono x m).trace.natAbs ≤ 2 * rowEnvelope x m := by
    rw [Matrix.trace_fin_two]
    have h := Int.natAbs_add_le (integerMono x m 0 0) (integerMono x m 1 1)
    omega
  calc
    (traceDifference x m).natAbs ≤
        (integerMono x m).trace.natAbs + (2 * (transferH m) ^ b).natAbs :=
      Int.natAbs_sub_le _ _
    _ = (integerMono x m).trace.natAbs + 2 * (transferH m).natAbs ^ b := by
      simp [Int.natAbs_mul]
    _ ≤ 2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b :=
      Nat.add_le_add_right htrace _
#print axioms Paper7CRTAlgebra.traceDifference_natAbs_le

theorem scalarDifference_natAbs_le (b : ℕ) (x : PQ b) (m : ℤ)
    (i j : Fin 2) : (scalarDifference x m i j).natAbs ≤
      rowEnvelope x m + (transferH m).natAbs ^ b := by
  by_cases hij : i = j
  · subst j
    simp only [scalarDifference, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one]
    calc
      (integerMono x m i i - (transferH m) ^ b).natAbs ≤
          (integerMono x m i i).natAbs + ((transferH m) ^ b).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ rowEnvelope x m + (transferH m).natAbs ^ b := by
        rw [Int.natAbs_pow]
        exact Nat.add_le_add_right (integerMono_entry_natAbs_le b x m i i) _
  · simp only [scalarDifference, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_ne hij, smul_eq_mul, mul_zero, sub_zero]
    exact (integerMono_entry_natAbs_le b x m i j).trans (Nat.le_add_right _ _)
#print axioms Paper7CRTAlgebra.scalarDifference_natAbs_le

/-- The full generic envelope conjunct of the frozen CRT contract, strengthened
to all integer m. No magnitude bound is supplied as a hypothesis. -/
theorem integerMono_envelope_bounds (b : ℕ) (x : PQ b) (m : ℤ) :
    (∀ i j : Fin 2, (integerMono x m i j).natAbs ≤ rowEnvelope x m) ∧
    (traceDifference x m).natAbs ≤
      2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b ∧
    (∀ i j : Fin 2, (scalarDifference x m i j).natAbs ≤
      rowEnvelope x m + (transferH m).natAbs ^ b) :=
  ⟨integerMono_entry_natAbs_le b x m, traceDifference_natAbs_le b x m,
    scalarDifference_natAbs_le b x m⟩
#print axioms Paper7CRTAlgebra.integerMono_envelope_bounds

end Paper7CRTAlgebra
