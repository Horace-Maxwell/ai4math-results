import Research.Backfill.Paper7.OddFifteenEmpty
import Research.Backfill.Paper7.ReportedALeafBound

/-! Source-only complete odd feature cells and the cycle-filtered even cells.
The unfiltered DReachable assertions are deliberately a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace Paper7FeatureEmpty
open BackfillPaper7.Challenge.Legacy

theorem odd_cells_empty (cyc : Bool) (N : ℕ) (hN : N ≤ 42) (b : ℕ)
    (hb : b ∈ ({5,7,9,11,13,15} : Finset ℕ)) : {s | Admissible cyc b N s} = ∅ := by
  by_cases h15 : b = 15
  · subst b
    exact fifteen_odd_cell_empty cyc N hN
  · apply five_odd_cells_empty cyc N b
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
    tauto
#print axioms Paper7FeatureEmpty.odd_cells_empty

theorem even_cycle_filtered_cells_empty (b : ℕ) (hb : b = 22 ∨ b = 26) :
    {s | Admissible true b 42 s} = ∅ := by
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hs
  have he : Even b := by rcases hb with rfl | rfl <;> norm_num
  have hcount := Paper7CRTEnvelope.admissible_even_42_posCard_le_five b s he hs
  have hcycle := (hs.2 rfl).1
  rcases hb with rfl | rfl
  · rw [Paper7CRTEnvelope.cyclic_positive_twenty_two] at hcycle
    omega
  · rw [Paper7CRTEnvelope.cyclic_positive_twenty_six] at hcycle
    omega
#print axioms Paper7FeatureEmpty.even_cycle_filtered_cells_empty

end Paper7FeatureEmpty
