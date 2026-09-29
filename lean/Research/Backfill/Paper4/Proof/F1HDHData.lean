import Research.Backfill.Paper4.Proof.ConcreteDHCertificate
import Research.HKOTriameterDH

/-! Generated finite F1H certificates for every actual vertex subset.
Each subset has its own kernel-reduced proposition; cuts are preselected.
The final theorem covers all Finsets, including empty and singleton subsets.
Python generation is not Lean acceptance; receipts are recorded separately. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.F1HDHData
open ConcreteDHCertificate

def subsets : List (Finset (Fin 6)) := [
  ∅,
  {0},
  {1},
  {0, 1},
  {2},
  {0, 2},
  {1, 2},
  {0, 1, 2},
  {3},
  {0, 3},
  {1, 3},
  {0, 1, 3},
  {2, 3},
  {0, 2, 3},
  {1, 2, 3},
  {0, 1, 2, 3},
  {4},
  {0, 4},
  {1, 4},
  {0, 1, 4},
  {2, 4},
  {0, 2, 4},
  {1, 2, 4},
  {0, 1, 2, 4},
  {3, 4},
  {0, 3, 4},
  {1, 3, 4},
  {0, 1, 3, 4},
  {2, 3, 4},
  {0, 2, 3, 4},
  {1, 2, 3, 4},
  {0, 1, 2, 3, 4},
  {5},
  {0, 5},
  {1, 5},
  {0, 1, 5},
  {2, 5},
  {0, 2, 5},
  {1, 2, 5},
  {0, 1, 2, 5},
  {3, 5},
  {0, 3, 5},
  {1, 3, 5},
  {0, 1, 3, 5},
  {2, 3, 5},
  {0, 2, 3, 5},
  {1, 2, 3, 5},
  {0, 1, 2, 3, 5},
  {4, 5},
  {0, 4, 5},
  {1, 4, 5},
  {0, 1, 4, 5},
  {2, 4, 5},
  {0, 2, 4, 5},
  {1, 2, 4, 5},
  {0, 1, 2, 4, 5},
  {3, 4, 5},
  {0, 3, 4, 5},
  {1, 3, 4, 5},
  {0, 1, 3, 4, 5},
  {2, 3, 4, 5},
  {0, 2, 3, 4, 5},
  {1, 2, 3, 4, 5},
  {0, 1, 2, 3, 4, 5}]

def cuts : List (Finset (Fin 6)) := [
  ∅,
  ∅,
  ∅,
  {0},
  ∅,
  {0},
  {1},
  {0},
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  {3},
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅]

def subsetCode (S : Finset (Fin 6)) : ℕ :=
  ∑ x ∈ S, 2 ^ x.val

def cut (S : Finset (Fin 6)) : Finset (Fin 6) :=
  cuts.getD (subsetCode S) ∅

def PointValid (S : Finset (Fin 6)) : Prop :=
  Cut HKOTriameter.F1H S (cut S) ∨ Descent HKOTriameter.F1H HKOTriameter.DF1H S

lemma point_000 : PointValid (∅) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_001 : PointValid ({0}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_002 : PointValid ({1}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_003 : PointValid ({0, 1}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_004 : PointValid ({2}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_005 : PointValid ({0, 2}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_006 : PointValid ({1, 2}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_007 : PointValid ({0, 1, 2}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_008 : PointValid ({3}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_009 : PointValid ({0, 3}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_010 : PointValid ({1, 3}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_011 : PointValid ({0, 1, 3}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_012 : PointValid ({2, 3}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_013 : PointValid ({0, 2, 3}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_014 : PointValid ({1, 2, 3}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_015 : PointValid ({0, 1, 2, 3}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_016 : PointValid ({4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_017 : PointValid ({0, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_018 : PointValid ({1, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_019 : PointValid ({0, 1, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_020 : PointValid ({2, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_021 : PointValid ({0, 2, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_022 : PointValid ({1, 2, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_023 : PointValid ({0, 1, 2, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_024 : PointValid ({3, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_025 : PointValid ({0, 3, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_026 : PointValid ({1, 3, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_027 : PointValid ({0, 1, 3, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_028 : PointValid ({2, 3, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_029 : PointValid ({0, 2, 3, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_030 : PointValid ({1, 2, 3, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_031 : PointValid ({0, 1, 2, 3, 4}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_032 : PointValid ({5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_033 : PointValid ({0, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_034 : PointValid ({1, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_035 : PointValid ({0, 1, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_036 : PointValid ({2, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_037 : PointValid ({0, 2, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_038 : PointValid ({1, 2, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_039 : PointValid ({0, 1, 2, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_040 : PointValid ({3, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_041 : PointValid ({0, 3, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_042 : PointValid ({1, 3, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_043 : PointValid ({0, 1, 3, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_044 : PointValid ({2, 3, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_045 : PointValid ({0, 2, 3, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_046 : PointValid ({1, 2, 3, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_047 : PointValid ({0, 1, 2, 3, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_048 : PointValid ({4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_049 : PointValid ({0, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_050 : PointValid ({1, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_051 : PointValid ({0, 1, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_052 : PointValid ({2, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_053 : PointValid ({0, 2, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_054 : PointValid ({1, 2, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_055 : PointValid ({0, 1, 2, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_056 : PointValid ({3, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_057 : PointValid ({0, 3, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_058 : PointValid ({1, 3, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_059 : PointValid ({0, 1, 3, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_060 : PointValid ({2, 3, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_061 : PointValid ({0, 2, 3, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_062 : PointValid ({1, 2, 3, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_063 : PointValid ({0, 1, 2, 3, 4, 5}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma all_subsets : (Finset.univ : Finset (Fin 6)).powerset = subsets.toFinset := by
  decide +kernel

lemma all_entries_valid : subsets.Forall PointValid := by
  exact And.intro point_000 (And.intro point_001 (And.intro point_002 (And.intro point_003 (And.intro point_004 (And.intro point_005 (And.intro point_006 (And.intro point_007 (And.intro point_008 (And.intro point_009 (And.intro point_010 (And.intro point_011 (And.intro point_012 (And.intro point_013 (And.intro point_014 (And.intro point_015 (And.intro point_016 (And.intro point_017 (And.intro point_018 (And.intro point_019 (And.intro point_020 (And.intro point_021 (And.intro point_022 (And.intro point_023 (And.intro point_024 (And.intro point_025 (And.intro point_026 (And.intro point_027 (And.intro point_028 (And.intro point_029 (And.intro point_030 (And.intro point_031 (And.intro point_032 (And.intro point_033 (And.intro point_034 (And.intro point_035 (And.intro point_036 (And.intro point_037 (And.intro point_038 (And.intro point_039 (And.intro point_040 (And.intro point_041 (And.intro point_042 (And.intro point_043 (And.intro point_044 (And.intro point_045 (And.intro point_046 (And.intro point_047 (And.intro point_048 (And.intro point_049 (And.intro point_050 (And.intro point_051 (And.intro point_052 (And.intro point_053 (And.intro point_054 (And.intro point_055 (And.intro point_056 (And.intro point_057 (And.intro point_058 (And.intro point_059 (And.intro point_060 (And.intro point_061 (And.intro point_062 (point_063)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem F1H_valid : Valid HKOTriameter.F1H HKOTriameter.DF1H cut := by
  intro S
  have hs : S ∈ (Finset.univ : Finset (Fin 6)).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ S)
  rw [all_subsets] at hs
  exact (List.forall_iff_forall_mem.mp all_entries_valid) S (List.mem_toFinset.mp hs)

#print axioms F1H_valid
end CodexPaper4.F1HDHData
