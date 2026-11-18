import Research.TaskH.General.OriginalSplitLockedRows
import Research.TaskH.General.OriginalTwoLockedRows

/-! Original-domain endpoint. Actual split representatives, Kempe components,
simple paths, whole-class capacities and both C_(2k) contradictions are all
derived internally. No new degree, coverage, path, recoloring or split premise
is added to the original full-critical equality graph. UNCOMPILED candidate. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open scoped Classical
open SimpleGraph _root_.TaskH.Challenge
variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_split_boundary_impossible [DecidableRel G.Adj]
    (hk : 6 ≤ k) (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1)) {v : V} (hv : G.degree v = 2 * k - 2)
    {c : (G.induce {z | z ≠ v}).Coloring (Fin k)} (D : OriginalBoundarySplitData v c) : False := by
  classical
  obtain ⟨i, _, _, hi, _⟩ := D.two_locked_rows hk hcrit hcount hnot hv
  obtain ⟨j, j', hjj', hj, hj'⟩ := D.reversed.two_locked_rows hk hcrit hcount hnot hv
  have hchoose : ∃ l : D.S, l ≠ i ∧
      D.P l ∈ _root_.TaskH.Seven.twoColorComponent c (c D.b) (c (D.Q l)) D.b := by
    by_cases hji : j = i
    · exact ⟨j', fun he => hjj' (hji.trans he.symm), hj'⟩
    · exact ⟨j, hji, hj⟩
  obtain ⟨l, hli, hl⟩ := hchoose
  have hreachA : D.Q i ∈ _root_.TaskH.Seven.twoColorComponent c (c D.a) (c (D.Q i)) D.a := by
    simpa only [D.colorP i, D.colorQ i] using hi
  have hreachB : D.P l ∈ _root_.TaskH.Seven.twoColorComponent c (c D.b) (c (D.P l)) D.b := by
    simpa only [D.colorP l, D.colorQ l] using hl
  have hcolors : c (D.Q i) ≠ c (D.P l) := by
    rw [D.colorQ i, D.colorP l]
    intro he
    exact hli (Subtype.ext he.symm)
  exact equality_original_two_distinct_locked_rows_impossible hk hcrit hcount c
    D.a D.b (D.Q i) (D.P l) D.hva D.hvb (D.rootQ i) (D.rootP l)
    (D.hookQ i) (D.hookP l) D.unique_a D.unique_b D.color_ne
    (by rw [D.colorQ i]; exact (D.side_color_ne i).1)
    (by rw [D.colorQ i]; exact (D.side_color_ne i).2)
    (by rw [D.colorP l]; exact (D.side_color_ne l).1)
    (by rw [D.colorP l]; exact (D.side_color_ne l).2) hcolors
    (fun he => D.notQ i he.symm) (fun he => D.notP l he.symm) hreachA hreachB

theorem equality_original_boundary_degree_impossible [DecidableRel G.Adj]
    (hk : 6 ≤ k) (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1)) (v : V) (hv : G.degree v = 2 * k - 2) : False := by
  obtain ⟨c⟩ := _root_.TaskH.critical_colorable_deletedVertex hcrit v
  obtain ⟨D⟩ := equality_original_boundary_split_data hk hcrit hcount hnot v hv c
  exact equality_original_split_boundary_impossible hk hcrit hcount hnot hv D

/-- The complete original parameter-uniform stronger minimum-degree target.
The present source has not been elaborated, checked, reviewed or accepted. -/
theorem equality_original_minimum_degree_two_mul_sub_one [DecidableRel G.Adj]
    (hk : 6 ≤ k) (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1)) (v : V) : 2 * k - 1 ≤ G.degree v := by
  have hlo := equality_original_minimum_degree_two_mul_sub_two (by omega) hcrit hcount hnot v
  by_contra hn
  have hv : G.degree v = 2 * k - 2 := by omega
  exact equality_original_boundary_degree_impossible hk hcrit hcount hnot v hv

end TaskH.General
#print axioms TaskH.General.equality_original_split_boundary_impossible
#print axioms TaskH.General.equality_original_boundary_degree_impossible
#print axioms TaskH.General.equality_original_minimum_degree_two_mul_sub_one
