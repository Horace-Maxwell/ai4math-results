import Research.Backfill.Paper7.SpectralThresholdCounts

set_option autoImplicit false

noncomputable section

namespace Paper7Comparison

open Matrix BackfillPaper7.Challenge Paper7Inertia
open scoped Matrix

theorem tridiag_isHermitian {b : ℕ} (Y : Finset (Fin b)) (t : Fin b → ℝ) :
    (tridiag Y t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases he : i = j
  · subst j
    simp [tridiag]
  · simp [tridiag, he, Ne.symm he, or_comm]
#print axioms Paper7Comparison.tridiag_isHermitian

theorem tridiag_add_diagonal {b : ℕ} (Y : Finset (Fin b)) (t u : Fin b → ℝ) :
    tridiag Y u = tridiag Y t + Matrix.diagonal (fun i : Y => u i.val - t i.val) := by
  apply Matrix.ext
  intro i j
  by_cases he : i = j
  · subst j
    simp [tridiag, Matrix.add_apply]
  · simp [tridiag, Matrix.add_apply, he]
#print axioms Paper7Comparison.tridiag_add_diagonal

theorem tridiag_quadratic_mono {b : ℕ} (Y : Finset (Fin b)) (t u : Fin b → ℝ)
    (htu : ∀ k ∈ Y, t k ≤ u k) (x : Y → ℝ) :
    (tridiag Y t).toQuadraticForm' x ≤ (tridiag Y u).toQuadraticForm' x := by
  rw [tridiag_add_diagonal Y t u, quadratic_add_apply, quadratic_diagonal]
  have hnonneg : 0 ≤ (QuadraticMap.weightedSumSquares ℝ
      (fun i : Y => u i.val - t i.val)) x := by
    rw [QuadraticMap.weightedSumSquares_apply]
    apply Finset.sum_nonneg
    intro i hi
    change 0 ≤ (u i.val - t i.val) * (x i * x i)
    exact mul_nonneg (sub_nonneg.mpr (htu i.val i.property)) (mul_self_nonneg (x i))
  linarith
#print axioms Paper7Comparison.tridiag_quadratic_mono

/-- Monotonicity on the actual frozen arbitrary subset-indexed tridiagonal matrix,
with strict and non-strict counts kept separate. -/
theorem tridiag_inertia_mono {b : ℕ} (Y : Finset (Fin b)) (t u : Fin b → ℝ)
    (htu : ∀ k ∈ Y, t k ≤ u k) :
    nPos (tridiag Y t) ≤ nPos (tridiag Y u) ∧
      nNeg (tridiag Y u) ≤ nNeg (tridiag Y t) ∧
      nPos (tridiag Y t) + nZero (tridiag Y t) ≤
        nPos (tridiag Y u) + nZero (tridiag Y u) := by
  have hq := tridiag_quadratic_mono Y t u htu
  have h := inertia_mono _ _ (tridiag_isHermitian Y t) (tridiag_isHermitian Y u) hq
  exact ⟨h.1, h.2, nonneg_inertia_mono _ _
    (tridiag_isHermitian Y t) (tridiag_isHermitian Y u) hq⟩
#print axioms Paper7Comparison.tridiag_inertia_mono

/-- Removing the final cycle vertex removes the wrap-around edge. -/
theorem cycle_adj_on_Xset (b : ℕ) (hb : 3 ≤ b) (i j : Fin b)
    (hi : i ∈ Xset b) (hj : j ∈ Xset b) :
    (SimpleGraph.cycleGraph b).Adj i j ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n+2 := ⟨b-2, by omega⟩
  have hsuc (u v : Fin (n+2)) :
      v.val = (u.val+1) % (n+2) ↔ v = u+1 := by
    rw [Fin.ext_iff, Fin.val_add, Fin.val_one]
  have hc : (SimpleGraph.cycleGraph (n+2)).Adj i j ↔
      j.val = (i.val+1) % (n+2) ∨ i.val = (j.val+1) % (n+2) := by
    rw [SimpleGraph.cycleGraph_adj, sub_eq_iff_eq_add', sub_eq_iff_eq_add', hsuc, hsuc]
    exact or_comm
  simp only [Xset, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have hi' : i.val+1 < n+2 := by omega
  have hj' : j.val+1 < n+2 := by omega
  rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hc
  exact hc.trans (or_congr eq_comm eq_comm)
#print axioms Paper7Comparison.cycle_adj_on_Xset

theorem cycle_diagonal_compression (b : ℕ) (hb : 3 ≤ b) (Y : Finset (Fin b))
    (hY : Y ⊆ Xset b) (d : Fin b → ℝ) :
    (Cyc b + Matrix.diagonal d).submatrix
      (fun i : Y => i.val) (fun j : Y => j.val) = tridiag Y d := by
  apply Matrix.ext
  intro i j
  by_cases he : i = j
  · subst j
    simp [Matrix.submatrix_apply, Matrix.add_apply,
      Cyc, SimpleGraph.adjMatrix_apply, tridiag]
  · have hv : i.val ≠ j.val := fun h => he (Subtype.ext h)
    have ha := cycle_adj_on_Xset b hb i.val j.val (hY i.property) (hY j.property)
    simp [Matrix.submatrix_apply, Matrix.add_apply,
      Cyc, SimpleGraph.adjMatrix_apply, tridiag, he, hv, ha]
#print axioms Paper7Comparison.cycle_diagonal_compression

theorem smat_as_cycle_diagonal (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) :
    Smat b p q m = Cyc b + Matrix.diagonal (fun k => fk b p q m k - m) := by
  unfold Smat
  rw [Matrix.smul_one_eq_diagonal]
  change Cyc b - Matrix.diagonal (fun _ => m) + Matrix.diagonal (fk b p q m) =
    Cyc b + Matrix.diagonal (fun k => fk b p q m k - m)
  rw [← Matrix.diagonal_sub (fk b p q m) (fun _ => m)]
  abel
#print axioms Paper7Comparison.smat_as_cycle_diagonal

theorem smat_Xset_compression (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) (m : ℝ) :
    (Smat b p q m).submatrix (fun i : Xset b => i.val) (fun j : Xset b => j.val) =
      tridiag (Xset b) (fun k => fk b p q m k - m) := by
  rw [smat_as_cycle_diagonal]
  exact cycle_diagonal_compression b hb (Xset b) (fun _ h => h) _
#print axioms Paper7Comparison.smat_Xset_compression

/-- The diagonal-comparison stage of the ordinary branch only.
The missing original-graph Schur/compression stage is not assumed in this theorem. -/
theorem ordinary_compressed_comparison (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (m : ℝ) (t : Fin b → ℝ) (ht : ∀ k ∈ Xset b, t k ≤ fk b p q m k - m) :
    nPos (tridiag (Xset b) t) ≤
        nPos ((Smat b p q m).submatrix (fun i : Xset b => i.val) (fun j : Xset b => j.val)) ∧
      nPos (tridiag (Xset b) t) + nZero (tridiag (Xset b) t) ≤
        nPos ((Smat b p q m).submatrix (fun i : Xset b => i.val) (fun j : Xset b => j.val)) +
        nZero ((Smat b p q m).submatrix (fun i : Xset b => i.val) (fun j : Xset b => j.val)) := by
  rw [smat_Xset_compression b p q hb m]
  have h := tridiag_inertia_mono (Xset b) t (fun k => fk b p q m k - m) ht
  exact ⟨h.1, h.2.2⟩
#print axioms Paper7Comparison.ordinary_compressed_comparison

/-- The monotone residual-core comparison at threshold 1, retaining the exact
Y.card addition. The actual q-arm contribution remains a separate proof obligation. -/
theorem unit_compressed_comparison (b : ℕ) (p : Fin b → ℕ) (hb : 3 ≤ b)
    (Y : Finset (Fin b)) (t : Fin b → ℝ)
    (ht : ∀ k ∈ Xset b \ Y, t k ≤ (p k : ℝ) - 1) :
    Y.card + nPos (tridiag (Xset b \ Y) t) ≤
      Y.card + nPos ((Cyc b + Matrix.diagonal (fun k => (p k : ℝ) - 1)).submatrix
        (fun i : ↥(Xset b \ Y) => i.val) (fun j : ↥(Xset b \ Y) => j.val)) := by
  have hY : Xset b \ Y ⊆ Xset b := by
    intro k hk
    exact (Finset.mem_sdiff.mp hk).1
  rw [cycle_diagonal_compression b hb (Xset b \ Y) hY]
  exact Nat.add_le_add_left
    (tridiag_inertia_mono (Xset b \ Y) t (fun k => (p k : ℝ) - 1) ht).1 Y.card
#print axioms Paper7Comparison.unit_compressed_comparison

end Paper7Comparison
