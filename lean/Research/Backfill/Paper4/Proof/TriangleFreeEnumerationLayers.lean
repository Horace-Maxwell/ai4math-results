import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationSmallLayers
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent3P00
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent4P00
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent4P01
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent4P02
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent5P00
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent5P01
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent5P02
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent5P03
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent5P04
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent5P05
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P00
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P01
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P02
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P03
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P04
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P05
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P06
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P07
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P08
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P09
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P10
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P11
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P12
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P13
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P14
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P15
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P16
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P17
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationParent6P18

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationLayers
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem layer_3 : LayerStep (reps 3) (reps 4) := by
  intro i S hne hi
  fin_cases i
  · exact TriangleFreeEnumerationParent3P00.parent_layer S hne hi

theorem layer_4 : LayerStep (reps 4) (reps 5) := by
  intro i S hne hi
  fin_cases i
  · exact TriangleFreeEnumerationParent4P00.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent4P01.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent4P02.parent_layer S hne hi

theorem layer_5 : LayerStep (reps 5) (reps 6) := by
  intro i S hne hi
  fin_cases i
  · exact TriangleFreeEnumerationParent5P00.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent5P01.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent5P02.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent5P03.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent5P04.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent5P05.parent_layer S hne hi

theorem layer_6 : LayerStep (reps 6) (reps 7) := by
  intro i S hne hi
  fin_cases i
  · exact TriangleFreeEnumerationParent6P00.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P01.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P02.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P03.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P04.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P05.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P06.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P07.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P08.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P09.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P10.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P11.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P12.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P13.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P14.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P15.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P16.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P17.parent_layer S hne hi
  · exact TriangleFreeEnumerationParent6P18.parent_layer S hne hi

theorem layers (n : ℕ) (hn : 1 ≤ n) (hn6 : n ≤ 6) :
    LayerStep (reps n) (reps (n+1)) := by
  interval_cases n
  · exact TriangleFreeEnumerationSmallLayers.layer_1
  · exact TriangleFreeEnumerationSmallLayers.layer_2
  · exact layer_3
  · exact layer_4
  · exact layer_5
  · exact layer_6

#print axioms layers

end CodexPaper4.TriangleFreeEnumerationLayers
