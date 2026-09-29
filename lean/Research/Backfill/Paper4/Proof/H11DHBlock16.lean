import Research.Backfill.Paper4.Proof.H11SubsetCover
import Research.Backfill.Paper4.Proof.H11Metric

/-! H11 finite certificate block 16, exactly 64 low-coordinate subsets.
Cuts are explicit literal witnesses; no existential cut enumeration occurs.
This module is not a proof of full H11 distance-heredity or Remark5_ii.
Acceptance evidence is recorded separately. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.H11DHBlock16
open BackfillPaper4 ConcreteDHCertificate H11SubsetCover

def fixedHigh : Finset (Fin 5) := {4}

def PointValid (L : Finset (Fin 6)) : Prop :=
  ∃ C : Finset (Fin 11),
    Cut Challenge.H11 (join L fixedHigh) C ∨
    Descent Challenge.H11 H11Metric.D11 (join L fixedHigh)

lemma point_000 : PointValid (∅) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_001 : PointValid ({0}) := by
  refine ⟨({0} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_002 : PointValid ({1}) := by
  refine ⟨({1} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_003 : PointValid ({0, 1}) := by
  refine ⟨({0, 1} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_004 : PointValid ({2}) := by
  refine ⟨({2} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_005 : PointValid ({0, 2}) := by
  refine ⟨({0, 2} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_006 : PointValid ({1, 2}) := by
  refine ⟨({1} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_007 : PointValid ({0, 1, 2}) := by
  refine ⟨({0, 1, 2} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_008 : PointValid ({3}) := by
  refine ⟨({3} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_009 : PointValid ({0, 3}) := by
  refine ⟨({0, 3} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_010 : PointValid ({1, 3}) := by
  refine ⟨({1} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_011 : PointValid ({0, 1, 3}) := by
  refine ⟨({0, 1, 3} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_012 : PointValid ({2, 3}) := by
  refine ⟨({2} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_013 : PointValid ({0, 2, 3}) := by
  refine ⟨({0, 2, 3} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_014 : PointValid ({1, 2, 3}) := by
  refine ⟨({1} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_015 : PointValid ({0, 1, 2, 3}) := by
  refine ⟨({0, 1, 2, 3} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_016 : PointValid ({4}) := by
  refine ⟨({4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_017 : PointValid ({0, 4}) := by
  refine ⟨({0} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_018 : PointValid ({1, 4}) := by
  refine ⟨({1, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_019 : PointValid ({0, 1, 4}) := by
  refine ⟨({0, 1, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_020 : PointValid ({2, 4}) := by
  refine ⟨({2, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_021 : PointValid ({0, 2, 4}) := by
  refine ⟨({0, 2, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_022 : PointValid ({1, 2, 4}) := by
  refine ⟨({1, 2, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_023 : PointValid ({0, 1, 2, 4}) := by
  refine ⟨({0, 1, 2, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_024 : PointValid ({3, 4}) := by
  refine ⟨({3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_025 : PointValid ({0, 3, 4}) := by
  refine ⟨({0, 3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_026 : PointValid ({1, 3, 4}) := by
  refine ⟨({1, 3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_027 : PointValid ({0, 1, 3, 4}) := by
  refine ⟨({0, 1, 3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_028 : PointValid ({2, 3, 4}) := by
  refine ⟨({2, 3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_029 : PointValid ({0, 2, 3, 4}) := by
  refine ⟨({0, 2, 3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_030 : PointValid ({1, 2, 3, 4}) := by
  refine ⟨({1, 2, 3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_031 : PointValid ({0, 1, 2, 3, 4}) := by
  refine ⟨({0, 1, 2, 3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_032 : PointValid ({5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_033 : PointValid ({0, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_034 : PointValid ({1, 5}) := by
  refine ⟨({1} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_035 : PointValid ({0, 1, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_036 : PointValid ({2, 5}) := by
  refine ⟨({2} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_037 : PointValid ({0, 2, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_038 : PointValid ({1, 2, 5}) := by
  refine ⟨({1} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_039 : PointValid ({0, 1, 2, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_040 : PointValid ({3, 5}) := by
  refine ⟨({3} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_041 : PointValid ({0, 3, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_042 : PointValid ({1, 3, 5}) := by
  refine ⟨({1} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_043 : PointValid ({0, 1, 3, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_044 : PointValid ({2, 3, 5}) := by
  refine ⟨({2} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_045 : PointValid ({0, 2, 3, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_046 : PointValid ({1, 2, 3, 5}) := by
  refine ⟨({1} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_047 : PointValid ({0, 1, 2, 3, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_048 : PointValid ({4, 5}) := by
  refine ⟨({4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_049 : PointValid ({0, 4, 5}) := by
  refine ⟨({0, 5, 10} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_050 : PointValid ({1, 4, 5}) := by
  refine ⟨({1, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_051 : PointValid ({0, 1, 4, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_052 : PointValid ({2, 4, 5}) := by
  refine ⟨({2, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_053 : PointValid ({0, 2, 4, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_054 : PointValid ({1, 2, 4, 5}) := by
  refine ⟨({1, 2, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_055 : PointValid ({0, 1, 2, 4, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_056 : PointValid ({3, 4, 5}) := by
  refine ⟨({3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_057 : PointValid ({0, 3, 4, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_058 : PointValid ({1, 3, 4, 5}) := by
  refine ⟨({1, 3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_059 : PointValid ({0, 1, 3, 4, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_060 : PointValid ({2, 3, 4, 5}) := by
  refine ⟨({2, 3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_061 : PointValid ({0, 2, 3, 4, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_062 : PointValid ({1, 2, 3, 4, 5}) := by
  refine ⟨({1, 2, 3, 4} : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma point_063 : PointValid ({0, 1, 2, 3, 4, 5}) := by
  refine ⟨(∅ : Finset (Fin 11)), ?_⟩
  unfold Cut Descent
  decide +kernel

lemma all_entries_valid : lowSubsets.Forall PointValid := by
  exact And.intro point_000 (And.intro point_001 (And.intro point_002 (And.intro point_003 (And.intro point_004 (And.intro point_005 (And.intro point_006 (And.intro point_007 (And.intro point_008 (And.intro point_009 (And.intro point_010 (And.intro point_011 (And.intro point_012 (And.intro point_013 (And.intro point_014 (And.intro point_015 (And.intro point_016 (And.intro point_017 (And.intro point_018 (And.intro point_019 (And.intro point_020 (And.intro point_021 (And.intro point_022 (And.intro point_023 (And.intro point_024 (And.intro point_025 (And.intro point_026 (And.intro point_027 (And.intro point_028 (And.intro point_029 (And.intro point_030 (And.intro point_031 (And.intro point_032 (And.intro point_033 (And.intro point_034 (And.intro point_035 (And.intro point_036 (And.intro point_037 (And.intro point_038 (And.intro point_039 (And.intro point_040 (And.intro point_041 (And.intro point_042 (And.intro point_043 (And.intro point_044 (And.intro point_045 (And.intro point_046 (And.intro point_047 (And.intro point_048 (And.intro point_049 (And.intro point_050 (And.intro point_051 (And.intro point_052 (And.intro point_053 (And.intro point_054 (And.intro point_055 (And.intro point_056 (And.intro point_057 (And.intro point_058 (And.intro point_059 (And.intro point_060 (And.intro point_061 (And.intro point_062 (point_063)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem block_valid (L : Finset (Fin 6)) :
    ∃ C : Finset (Fin 11),
      Cut Challenge.H11 (join L fixedHigh) C ∨
      Descent Challenge.H11 H11Metric.D11 (join L fixedHigh) :=
  (List.forall_iff_forall_mem.mp all_entries_valid) L (low_complete L)

#print axioms block_valid
end CodexPaper4.H11DHBlock16
