import Research.Backfill.Paper4.Proof.TriangleFreeClassification
import Research.Backfill.Paper4.Proof.TriangleFreeIndependentCount

/-! The complete frozen count of 1,857 nonempty independent-set extensions.
The witness family is the same 59 actual graphs used by the full ClassCount proof.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4 TriangleFreeEnumerationCore TriangleFreeEnumerationFamily
namespace TriangleFreeCandidates
open TriangleFreeIndependentCount

def counts : Fin 59 → ℕ := ![64, 49, 43, 39, 42, 37, 40, 35, 36, 34, 33, 41, 35, 38, 33, 33, 34, 31, 31, 32, 32, 32, 30, 30, 29, 28, 37, 36, 31, 31, 29, 29, 30, 30, 28, 27, 28, 28, 28, 26, 27, 26, 35, 29, 27, 26, 28, 26, 26, 24, 24, 25, 25, 34, 25, 24, 22, 23, 22]

theorem count_00 : (independentFinsets (reps 7 0)).card = counts 0 := by
  decide +kernel
theorem count_01 : (independentFinsets (reps 7 1)).card = counts 1 := by
  decide +kernel
theorem count_02 : (independentFinsets (reps 7 2)).card = counts 2 := by
  decide +kernel
theorem count_03 : (independentFinsets (reps 7 3)).card = counts 3 := by
  decide +kernel
theorem count_04 : (independentFinsets (reps 7 4)).card = counts 4 := by
  decide +kernel
theorem count_05 : (independentFinsets (reps 7 5)).card = counts 5 := by
  decide +kernel
theorem count_06 : (independentFinsets (reps 7 6)).card = counts 6 := by
  decide +kernel
theorem count_07 : (independentFinsets (reps 7 7)).card = counts 7 := by
  decide +kernel
theorem count_08 : (independentFinsets (reps 7 8)).card = counts 8 := by
  decide +kernel
theorem count_09 : (independentFinsets (reps 7 9)).card = counts 9 := by
  decide +kernel
theorem count_10 : (independentFinsets (reps 7 10)).card = counts 10 := by
  decide +kernel
theorem count_11 : (independentFinsets (reps 7 11)).card = counts 11 := by
  decide +kernel
theorem count_12 : (independentFinsets (reps 7 12)).card = counts 12 := by
  decide +kernel
theorem count_13 : (independentFinsets (reps 7 13)).card = counts 13 := by
  decide +kernel
theorem count_14 : (independentFinsets (reps 7 14)).card = counts 14 := by
  decide +kernel
theorem count_15 : (independentFinsets (reps 7 15)).card = counts 15 := by
  decide +kernel
theorem count_16 : (independentFinsets (reps 7 16)).card = counts 16 := by
  decide +kernel
theorem count_17 : (independentFinsets (reps 7 17)).card = counts 17 := by
  decide +kernel
theorem count_18 : (independentFinsets (reps 7 18)).card = counts 18 := by
  decide +kernel
theorem count_19 : (independentFinsets (reps 7 19)).card = counts 19 := by
  decide +kernel
theorem count_20 : (independentFinsets (reps 7 20)).card = counts 20 := by
  decide +kernel
theorem count_21 : (independentFinsets (reps 7 21)).card = counts 21 := by
  decide +kernel
theorem count_22 : (independentFinsets (reps 7 22)).card = counts 22 := by
  decide +kernel
theorem count_23 : (independentFinsets (reps 7 23)).card = counts 23 := by
  decide +kernel
theorem count_24 : (independentFinsets (reps 7 24)).card = counts 24 := by
  decide +kernel
theorem count_25 : (independentFinsets (reps 7 25)).card = counts 25 := by
  decide +kernel
theorem count_26 : (independentFinsets (reps 7 26)).card = counts 26 := by
  decide +kernel
theorem count_27 : (independentFinsets (reps 7 27)).card = counts 27 := by
  decide +kernel
theorem count_28 : (independentFinsets (reps 7 28)).card = counts 28 := by
  decide +kernel
theorem count_29 : (independentFinsets (reps 7 29)).card = counts 29 := by
  decide +kernel
theorem count_30 : (independentFinsets (reps 7 30)).card = counts 30 := by
  decide +kernel
theorem count_31 : (independentFinsets (reps 7 31)).card = counts 31 := by
  decide +kernel
theorem count_32 : (independentFinsets (reps 7 32)).card = counts 32 := by
  decide +kernel
theorem count_33 : (independentFinsets (reps 7 33)).card = counts 33 := by
  decide +kernel
theorem count_34 : (independentFinsets (reps 7 34)).card = counts 34 := by
  decide +kernel
theorem count_35 : (independentFinsets (reps 7 35)).card = counts 35 := by
  decide +kernel
theorem count_36 : (independentFinsets (reps 7 36)).card = counts 36 := by
  decide +kernel
theorem count_37 : (independentFinsets (reps 7 37)).card = counts 37 := by
  decide +kernel
theorem count_38 : (independentFinsets (reps 7 38)).card = counts 38 := by
  decide +kernel
theorem count_39 : (independentFinsets (reps 7 39)).card = counts 39 := by
  decide +kernel
theorem count_40 : (independentFinsets (reps 7 40)).card = counts 40 := by
  decide +kernel
theorem count_41 : (independentFinsets (reps 7 41)).card = counts 41 := by
  decide +kernel
theorem count_42 : (independentFinsets (reps 7 42)).card = counts 42 := by
  decide +kernel
theorem count_43 : (independentFinsets (reps 7 43)).card = counts 43 := by
  decide +kernel
theorem count_44 : (independentFinsets (reps 7 44)).card = counts 44 := by
  decide +kernel
theorem count_45 : (independentFinsets (reps 7 45)).card = counts 45 := by
  decide +kernel
theorem count_46 : (independentFinsets (reps 7 46)).card = counts 46 := by
  decide +kernel
theorem count_47 : (independentFinsets (reps 7 47)).card = counts 47 := by
  decide +kernel
theorem count_48 : (independentFinsets (reps 7 48)).card = counts 48 := by
  decide +kernel
theorem count_49 : (independentFinsets (reps 7 49)).card = counts 49 := by
  decide +kernel
theorem count_50 : (independentFinsets (reps 7 50)).card = counts 50 := by
  decide +kernel
theorem count_51 : (independentFinsets (reps 7 51)).card = counts 51 := by
  decide +kernel
theorem count_52 : (independentFinsets (reps 7 52)).card = counts 52 := by
  decide +kernel
theorem count_53 : (independentFinsets (reps 7 53)).card = counts 53 := by
  decide +kernel
theorem count_54 : (independentFinsets (reps 7 54)).card = counts 54 := by
  decide +kernel
theorem count_55 : (independentFinsets (reps 7 55)).card = counts 55 := by
  decide +kernel
theorem count_56 : (independentFinsets (reps 7 56)).card = counts 56 := by
  decide +kernel
theorem count_57 : (independentFinsets (reps 7 57)).card = counts 57 := by
  decide +kernel
theorem count_58 : (independentFinsets (reps 7 58)).card = counts 58 := by
  decide +kernel

theorem counts_correct (i : Fin 59) : (independentFinsets (reps 7 i)).card = counts i := by
  fin_cases i
  · exact count_00
  · exact count_01
  · exact count_02
  · exact count_03
  · exact count_04
  · exact count_05
  · exact count_06
  · exact count_07
  · exact count_08
  · exact count_09
  · exact count_10
  · exact count_11
  · exact count_12
  · exact count_13
  · exact count_14
  · exact count_15
  · exact count_16
  · exact count_17
  · exact count_18
  · exact count_19
  · exact count_20
  · exact count_21
  · exact count_22
  · exact count_23
  · exact count_24
  · exact count_25
  · exact count_26
  · exact count_27
  · exact count_28
  · exact count_29
  · exact count_30
  · exact count_31
  · exact count_32
  · exact count_33
  · exact count_34
  · exact count_35
  · exact count_36
  · exact count_37
  · exact count_38
  · exact count_39
  · exact count_40
  · exact count_41
  · exact count_42
  · exact count_43
  · exact count_44
  · exact count_45
  · exact count_46
  · exact count_47
  · exact count_48
  · exact count_49
  · exact count_50
  · exact count_51
  · exact count_52
  · exact count_53
  · exact count_54
  · exact count_55
  · exact count_56
  · exact count_57
  · exact count_58

theorem sum_counts : ∑ i : Fin 59, counts i = 1857 := by decide +kernel

theorem sum_actual :
    (∑ i : Fin 59, Nat.card {s : Set (Fin 7) // s.Nonempty ∧ (reps 7 i).IsIndepSet s}) = 1857 := by
  calc
    (∑ i : Fin 59, Nat.card {s : Set (Fin 7) // s.Nonempty ∧ (reps 7 i).IsIndepSet s}) =
        ∑ i : Fin 59, (independentFinsets (reps 7 i)).card := by
      apply Finset.sum_congr rfl
      intro i _
      exact actual_set_count (reps 7 i)
    _ = ∑ i : Fin 59, counts i := by
      apply Finset.sum_congr rfl
      intro i _
      exact counts_correct i
    _ = 1857 := sum_counts

end TriangleFreeCandidates

theorem check_Sec4_count_candidates : Challenge.Sec4_count_candidates := by
  refine ⟨reps 7, ?_, ?_, ?_, TriangleFreeCandidates.sum_actual⟩
  · exact TriangleFreeEnumerationValidity.representatives_valid 7 (by decide) (by decide)
  · intro i j h
    exact TriangleFreeRepresentativeFingerprint.representatives_pairwise i j h
  · intro W _ G hcard hc ht
    have hcoverage : Covers (reps 7) :=
      covers_through_seven repCount reps (covers_one (reps 1) 0)
        TriangleFreeEnumerationLayers.layers 7 (by decide) (by decide)
    exact hcoverage W G hcard hc ht

#print axioms check_Sec4_count_candidates

end CodexPaper4
