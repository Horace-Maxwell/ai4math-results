import Research.Backfill.Paper4.Proof.ConcreteDHCertificate

/-! Generated finite G2 certificate data.
Each subset has its own kernel-reduced proposition. Cuts are preselected,
never searched existentially. The final theorem covers every actual Finset.
Python generation is not acceptance; Lean receipts are recorded separately. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.G2DHData
open ConcreteDHCertificate

def subsets : List (Finset (Fin 8)) := [
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
  {0, 1, 2, 3, 4, 5},
  {6},
  {0, 6},
  {1, 6},
  {0, 1, 6},
  {2, 6},
  {0, 2, 6},
  {1, 2, 6},
  {0, 1, 2, 6},
  {3, 6},
  {0, 3, 6},
  {1, 3, 6},
  {0, 1, 3, 6},
  {2, 3, 6},
  {0, 2, 3, 6},
  {1, 2, 3, 6},
  {0, 1, 2, 3, 6},
  {4, 6},
  {0, 4, 6},
  {1, 4, 6},
  {0, 1, 4, 6},
  {2, 4, 6},
  {0, 2, 4, 6},
  {1, 2, 4, 6},
  {0, 1, 2, 4, 6},
  {3, 4, 6},
  {0, 3, 4, 6},
  {1, 3, 4, 6},
  {0, 1, 3, 4, 6},
  {2, 3, 4, 6},
  {0, 2, 3, 4, 6},
  {1, 2, 3, 4, 6},
  {0, 1, 2, 3, 4, 6},
  {5, 6},
  {0, 5, 6},
  {1, 5, 6},
  {0, 1, 5, 6},
  {2, 5, 6},
  {0, 2, 5, 6},
  {1, 2, 5, 6},
  {0, 1, 2, 5, 6},
  {3, 5, 6},
  {0, 3, 5, 6},
  {1, 3, 5, 6},
  {0, 1, 3, 5, 6},
  {2, 3, 5, 6},
  {0, 2, 3, 5, 6},
  {1, 2, 3, 5, 6},
  {0, 1, 2, 3, 5, 6},
  {4, 5, 6},
  {0, 4, 5, 6},
  {1, 4, 5, 6},
  {0, 1, 4, 5, 6},
  {2, 4, 5, 6},
  {0, 2, 4, 5, 6},
  {1, 2, 4, 5, 6},
  {0, 1, 2, 4, 5, 6},
  {3, 4, 5, 6},
  {0, 3, 4, 5, 6},
  {1, 3, 4, 5, 6},
  {0, 1, 3, 4, 5, 6},
  {2, 3, 4, 5, 6},
  {0, 2, 3, 4, 5, 6},
  {1, 2, 3, 4, 5, 6},
  {0, 1, 2, 3, 4, 5, 6},
  {7},
  {0, 7},
  {1, 7},
  {0, 1, 7},
  {2, 7},
  {0, 2, 7},
  {1, 2, 7},
  {0, 1, 2, 7},
  {3, 7},
  {0, 3, 7},
  {1, 3, 7},
  {0, 1, 3, 7},
  {2, 3, 7},
  {0, 2, 3, 7},
  {1, 2, 3, 7},
  {0, 1, 2, 3, 7},
  {4, 7},
  {0, 4, 7},
  {1, 4, 7},
  {0, 1, 4, 7},
  {2, 4, 7},
  {0, 2, 4, 7},
  {1, 2, 4, 7},
  {0, 1, 2, 4, 7},
  {3, 4, 7},
  {0, 3, 4, 7},
  {1, 3, 4, 7},
  {0, 1, 3, 4, 7},
  {2, 3, 4, 7},
  {0, 2, 3, 4, 7},
  {1, 2, 3, 4, 7},
  {0, 1, 2, 3, 4, 7},
  {5, 7},
  {0, 5, 7},
  {1, 5, 7},
  {0, 1, 5, 7},
  {2, 5, 7},
  {0, 2, 5, 7},
  {1, 2, 5, 7},
  {0, 1, 2, 5, 7},
  {3, 5, 7},
  {0, 3, 5, 7},
  {1, 3, 5, 7},
  {0, 1, 3, 5, 7},
  {2, 3, 5, 7},
  {0, 2, 3, 5, 7},
  {1, 2, 3, 5, 7},
  {0, 1, 2, 3, 5, 7},
  {4, 5, 7},
  {0, 4, 5, 7},
  {1, 4, 5, 7},
  {0, 1, 4, 5, 7},
  {2, 4, 5, 7},
  {0, 2, 4, 5, 7},
  {1, 2, 4, 5, 7},
  {0, 1, 2, 4, 5, 7},
  {3, 4, 5, 7},
  {0, 3, 4, 5, 7},
  {1, 3, 4, 5, 7},
  {0, 1, 3, 4, 5, 7},
  {2, 3, 4, 5, 7},
  {0, 2, 3, 4, 5, 7},
  {1, 2, 3, 4, 5, 7},
  {0, 1, 2, 3, 4, 5, 7},
  {6, 7},
  {0, 6, 7},
  {1, 6, 7},
  {0, 1, 6, 7},
  {2, 6, 7},
  {0, 2, 6, 7},
  {1, 2, 6, 7},
  {0, 1, 2, 6, 7},
  {3, 6, 7},
  {0, 3, 6, 7},
  {1, 3, 6, 7},
  {0, 1, 3, 6, 7},
  {2, 3, 6, 7},
  {0, 2, 3, 6, 7},
  {1, 2, 3, 6, 7},
  {0, 1, 2, 3, 6, 7},
  {4, 6, 7},
  {0, 4, 6, 7},
  {1, 4, 6, 7},
  {0, 1, 4, 6, 7},
  {2, 4, 6, 7},
  {0, 2, 4, 6, 7},
  {1, 2, 4, 6, 7},
  {0, 1, 2, 4, 6, 7},
  {3, 4, 6, 7},
  {0, 3, 4, 6, 7},
  {1, 3, 4, 6, 7},
  {0, 1, 3, 4, 6, 7},
  {2, 3, 4, 6, 7},
  {0, 2, 3, 4, 6, 7},
  {1, 2, 3, 4, 6, 7},
  {0, 1, 2, 3, 4, 6, 7},
  {5, 6, 7},
  {0, 5, 6, 7},
  {1, 5, 6, 7},
  {0, 1, 5, 6, 7},
  {2, 5, 6, 7},
  {0, 2, 5, 6, 7},
  {1, 2, 5, 6, 7},
  {0, 1, 2, 5, 6, 7},
  {3, 5, 6, 7},
  {0, 3, 5, 6, 7},
  {1, 3, 5, 6, 7},
  {0, 1, 3, 5, 6, 7},
  {2, 3, 5, 6, 7},
  {0, 2, 3, 5, 6, 7},
  {1, 2, 3, 5, 6, 7},
  {0, 1, 2, 3, 5, 6, 7},
  {4, 5, 6, 7},
  {0, 4, 5, 6, 7},
  {1, 4, 5, 6, 7},
  {0, 1, 4, 5, 6, 7},
  {2, 4, 5, 6, 7},
  {0, 2, 4, 5, 6, 7},
  {1, 2, 4, 5, 6, 7},
  {0, 1, 2, 4, 5, 6, 7},
  {3, 4, 5, 6, 7},
  {0, 3, 4, 5, 6, 7},
  {1, 3, 4, 5, 6, 7},
  {0, 1, 3, 4, 5, 6, 7},
  {2, 3, 4, 5, 6, 7},
  {0, 2, 3, 4, 5, 6, 7},
  {1, 2, 3, 4, 5, 6, 7},
  {0, 1, 2, 3, 4, 5, 6, 7}]

def cuts : List (Finset (Fin 8)) := [
  ∅,
  ∅,
  ∅,
  {0},
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  {1},
  {0, 3},
  {2},
  ∅,
  {1, 2},
  ∅,
  ∅,
  {0},
  {1},
  {0},
  {2},
  {0, 2},
  {1, 2},
  {0, 1, 2},
  ∅,
  ∅,
  {1},
  {0, 3, 4},
  {2},
  ∅,
  {1, 2},
  ∅,
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
  {1},
  {0, 3, 5},
  ∅,
  ∅,
  ∅,
  ∅,
  {4},
  {0},
  {1},
  {0},
  {2, 5},
  {0, 2, 5},
  {1, 2, 5},
  {0, 1, 2, 5},
  ∅,
  ∅,
  {1},
  {0, 3, 4, 5},
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  ∅,
  {1},
  {0, 6},
  {2},
  ∅,
  {1, 2},
  ∅,
  {3},
  ∅,
  {1},
  {0, 3, 6},
  {2},
  ∅,
  {1, 2},
  ∅,
  {4},
  {0, 6},
  {1},
  {0, 6},
  {2},
  {0, 2, 6},
  {1, 2},
  {0, 1, 2, 6},
  {3, 4},
  ∅,
  {1},
  {0, 3, 4, 6},
  {2},
  ∅,
  {1, 2},
  ∅,
  {5},
  {0, 6},
  {1},
  {0, 6},
  {2, 5},
  ∅,
  {1, 2, 5},
  ∅,
  {3, 5},
  ∅,
  {1},
  {0, 3, 5, 6},
  {2, 3, 5},
  ∅,
  {1, 2, 3, 5},
  ∅,
  {4},
  {0, 6},
  {1},
  {0, 6},
  {2, 5},
  {0, 2, 5, 6},
  {1, 2, 5},
  {0, 1, 2, 5, 6},
  {3, 4, 5},
  ∅,
  {1},
  {0, 3, 4, 5, 6},
  {2, 3, 4, 5},
  ∅,
  {1, 2, 3, 4, 5},
  ∅,
  ∅,
  {0},
  {1},
  {0},
  {2},
  {0, 2},
  {1, 2},
  {0, 1, 2},
  {3},
  {0, 3},
  {1},
  {0, 3},
  {2},
  {0, 2, 3},
  {1, 2},
  {0, 1, 2, 3},
  {4},
  {0},
  {1},
  {0},
  {2},
  {0, 2},
  {1, 2},
  {0, 1, 2},
  {3, 4},
  {0, 3, 4},
  {1},
  {0, 3, 4},
  {2},
  {0, 2, 3, 4},
  {1, 2},
  {0, 1, 2, 3, 4},
  {5},
  {0},
  {1},
  {0},
  {2, 5},
  {0, 2, 5},
  {1, 2, 5},
  {0, 1, 2, 5},
  {3, 5},
  {0, 3, 5},
  {1},
  {0, 3, 5},
  {2, 3, 5},
  {0, 2, 3, 5},
  {1, 2, 3, 5},
  {0, 1, 2, 3, 5},
  {4},
  {0},
  {1},
  {0},
  {2, 5},
  {0, 2, 5},
  {1, 2, 5},
  {0, 1, 2, 5},
  {3, 4, 5},
  {0, 3, 4, 5},
  {1},
  {0, 3, 4, 5},
  {2, 3, 4, 5},
  {0, 2, 3, 4, 5},
  {1, 2, 3, 4, 5},
  {0, 1, 2, 3, 4, 5},
  ∅,
  ∅,
  {1},
  {0, 6, 7},
  {2},
  ∅,
  {1, 2},
  ∅,
  {3},
  ∅,
  {1},
  {0, 3, 6, 7},
  {2},
  ∅,
  {1, 2},
  ∅,
  {4},
  {0, 6, 7},
  {1},
  {0, 6, 7},
  {2},
  {0, 2, 6, 7},
  {1, 2},
  {0, 1, 2, 6, 7},
  {3, 4},
  ∅,
  {1},
  {0, 3, 4, 6, 7},
  {2},
  ∅,
  {1, 2},
  ∅,
  {5},
  {0, 6, 7},
  {1},
  {0, 6, 7},
  {2, 5},
  ∅,
  {1, 2, 5},
  ∅,
  {3, 5},
  ∅,
  {1},
  {0, 3, 5, 6, 7},
  {2, 3, 5},
  ∅,
  {1, 2, 3, 5},
  ∅,
  {4},
  {0, 6, 7},
  {1},
  {0, 6, 7},
  {2, 5},
  {0, 2, 5, 6, 7},
  {1, 2, 5},
  {0, 1, 2, 5, 6, 7},
  {3, 4, 5},
  ∅,
  {1},
  {0, 3, 4, 5, 6, 7},
  {2, 3, 4, 5},
  ∅,
  {1, 2, 3, 4, 5},
  ∅]

def subsetCode (S : Finset (Fin 8)) : ℕ :=
  ∑ x ∈ S, 2 ^ x.val

def cut (S : Finset (Fin 8)) : Finset (Fin 8) :=
  cuts.getD (subsetCode S) ∅

def PointValid (S : Finset (Fin 8)) : Prop :=
  Cut HKOTriameter.G2 S (cut S) ∨ Descent HKOTriameter.G2 HKOTriameter.D2 S

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

lemma point_064 : PointValid ({6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_065 : PointValid ({0, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_066 : PointValid ({1, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_067 : PointValid ({0, 1, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_068 : PointValid ({2, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_069 : PointValid ({0, 2, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_070 : PointValid ({1, 2, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_071 : PointValid ({0, 1, 2, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_072 : PointValid ({3, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_073 : PointValid ({0, 3, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_074 : PointValid ({1, 3, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_075 : PointValid ({0, 1, 3, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_076 : PointValid ({2, 3, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_077 : PointValid ({0, 2, 3, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_078 : PointValid ({1, 2, 3, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_079 : PointValid ({0, 1, 2, 3, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_080 : PointValid ({4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_081 : PointValid ({0, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_082 : PointValid ({1, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_083 : PointValid ({0, 1, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_084 : PointValid ({2, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_085 : PointValid ({0, 2, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_086 : PointValid ({1, 2, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_087 : PointValid ({0, 1, 2, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_088 : PointValid ({3, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_089 : PointValid ({0, 3, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_090 : PointValid ({1, 3, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_091 : PointValid ({0, 1, 3, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_092 : PointValid ({2, 3, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_093 : PointValid ({0, 2, 3, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_094 : PointValid ({1, 2, 3, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_095 : PointValid ({0, 1, 2, 3, 4, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_096 : PointValid ({5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_097 : PointValid ({0, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_098 : PointValid ({1, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_099 : PointValid ({0, 1, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_100 : PointValid ({2, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_101 : PointValid ({0, 2, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_102 : PointValid ({1, 2, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_103 : PointValid ({0, 1, 2, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_104 : PointValid ({3, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_105 : PointValid ({0, 3, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_106 : PointValid ({1, 3, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_107 : PointValid ({0, 1, 3, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_108 : PointValid ({2, 3, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_109 : PointValid ({0, 2, 3, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_110 : PointValid ({1, 2, 3, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_111 : PointValid ({0, 1, 2, 3, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_112 : PointValid ({4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_113 : PointValid ({0, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_114 : PointValid ({1, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_115 : PointValid ({0, 1, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_116 : PointValid ({2, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_117 : PointValid ({0, 2, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_118 : PointValid ({1, 2, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_119 : PointValid ({0, 1, 2, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_120 : PointValid ({3, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_121 : PointValid ({0, 3, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_122 : PointValid ({1, 3, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_123 : PointValid ({0, 1, 3, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_124 : PointValid ({2, 3, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_125 : PointValid ({0, 2, 3, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_126 : PointValid ({1, 2, 3, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_127 : PointValid ({0, 1, 2, 3, 4, 5, 6}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_128 : PointValid ({7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_129 : PointValid ({0, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_130 : PointValid ({1, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_131 : PointValid ({0, 1, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_132 : PointValid ({2, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_133 : PointValid ({0, 2, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_134 : PointValid ({1, 2, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_135 : PointValid ({0, 1, 2, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_136 : PointValid ({3, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_137 : PointValid ({0, 3, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_138 : PointValid ({1, 3, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_139 : PointValid ({0, 1, 3, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_140 : PointValid ({2, 3, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_141 : PointValid ({0, 2, 3, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_142 : PointValid ({1, 2, 3, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_143 : PointValid ({0, 1, 2, 3, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_144 : PointValid ({4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_145 : PointValid ({0, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_146 : PointValid ({1, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_147 : PointValid ({0, 1, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_148 : PointValid ({2, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_149 : PointValid ({0, 2, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_150 : PointValid ({1, 2, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_151 : PointValid ({0, 1, 2, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_152 : PointValid ({3, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_153 : PointValid ({0, 3, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_154 : PointValid ({1, 3, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_155 : PointValid ({0, 1, 3, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_156 : PointValid ({2, 3, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_157 : PointValid ({0, 2, 3, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_158 : PointValid ({1, 2, 3, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_159 : PointValid ({0, 1, 2, 3, 4, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_160 : PointValid ({5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_161 : PointValid ({0, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_162 : PointValid ({1, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_163 : PointValid ({0, 1, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_164 : PointValid ({2, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_165 : PointValid ({0, 2, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_166 : PointValid ({1, 2, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_167 : PointValid ({0, 1, 2, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_168 : PointValid ({3, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_169 : PointValid ({0, 3, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_170 : PointValid ({1, 3, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_171 : PointValid ({0, 1, 3, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_172 : PointValid ({2, 3, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_173 : PointValid ({0, 2, 3, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_174 : PointValid ({1, 2, 3, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_175 : PointValid ({0, 1, 2, 3, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_176 : PointValid ({4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_177 : PointValid ({0, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_178 : PointValid ({1, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_179 : PointValid ({0, 1, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_180 : PointValid ({2, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_181 : PointValid ({0, 2, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_182 : PointValid ({1, 2, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_183 : PointValid ({0, 1, 2, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_184 : PointValid ({3, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_185 : PointValid ({0, 3, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_186 : PointValid ({1, 3, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_187 : PointValid ({0, 1, 3, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_188 : PointValid ({2, 3, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_189 : PointValid ({0, 2, 3, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_190 : PointValid ({1, 2, 3, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_191 : PointValid ({0, 1, 2, 3, 4, 5, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_192 : PointValid ({6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_193 : PointValid ({0, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_194 : PointValid ({1, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_195 : PointValid ({0, 1, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_196 : PointValid ({2, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_197 : PointValid ({0, 2, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_198 : PointValid ({1, 2, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_199 : PointValid ({0, 1, 2, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_200 : PointValid ({3, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_201 : PointValid ({0, 3, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_202 : PointValid ({1, 3, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_203 : PointValid ({0, 1, 3, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_204 : PointValid ({2, 3, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_205 : PointValid ({0, 2, 3, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_206 : PointValid ({1, 2, 3, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_207 : PointValid ({0, 1, 2, 3, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_208 : PointValid ({4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_209 : PointValid ({0, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_210 : PointValid ({1, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_211 : PointValid ({0, 1, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_212 : PointValid ({2, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_213 : PointValid ({0, 2, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_214 : PointValid ({1, 2, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_215 : PointValid ({0, 1, 2, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_216 : PointValid ({3, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_217 : PointValid ({0, 3, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_218 : PointValid ({1, 3, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_219 : PointValid ({0, 1, 3, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_220 : PointValid ({2, 3, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_221 : PointValid ({0, 2, 3, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_222 : PointValid ({1, 2, 3, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_223 : PointValid ({0, 1, 2, 3, 4, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_224 : PointValid ({5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_225 : PointValid ({0, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_226 : PointValid ({1, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_227 : PointValid ({0, 1, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_228 : PointValid ({2, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_229 : PointValid ({0, 2, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_230 : PointValid ({1, 2, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_231 : PointValid ({0, 1, 2, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_232 : PointValid ({3, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_233 : PointValid ({0, 3, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_234 : PointValid ({1, 3, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_235 : PointValid ({0, 1, 3, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_236 : PointValid ({2, 3, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_237 : PointValid ({0, 2, 3, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_238 : PointValid ({1, 2, 3, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_239 : PointValid ({0, 1, 2, 3, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_240 : PointValid ({4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_241 : PointValid ({0, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_242 : PointValid ({1, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_243 : PointValid ({0, 1, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_244 : PointValid ({2, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_245 : PointValid ({0, 2, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_246 : PointValid ({1, 2, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_247 : PointValid ({0, 1, 2, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_248 : PointValid ({3, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_249 : PointValid ({0, 3, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_250 : PointValid ({1, 3, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_251 : PointValid ({0, 1, 3, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_252 : PointValid ({2, 3, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_253 : PointValid ({0, 2, 3, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_254 : PointValid ({1, 2, 3, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma point_255 : PointValid ({0, 1, 2, 3, 4, 5, 6, 7}) := by
  unfold PointValid Cut Descent
  decide +kernel

lemma all_subsets : (Finset.univ : Finset (Fin 8)).powerset = subsets.toFinset := by
  decide +kernel

lemma all_entries_valid : subsets.Forall PointValid := by
  exact And.intro point_000 (And.intro point_001 (And.intro point_002 (And.intro point_003 (And.intro point_004 (And.intro point_005 (And.intro point_006 (And.intro point_007 (And.intro point_008 (And.intro point_009 (And.intro point_010 (And.intro point_011 (And.intro point_012 (And.intro point_013 (And.intro point_014 (And.intro point_015 (And.intro point_016 (And.intro point_017 (And.intro point_018 (And.intro point_019 (And.intro point_020 (And.intro point_021 (And.intro point_022 (And.intro point_023 (And.intro point_024 (And.intro point_025 (And.intro point_026 (And.intro point_027 (And.intro point_028 (And.intro point_029 (And.intro point_030 (And.intro point_031 (And.intro point_032 (And.intro point_033 (And.intro point_034 (And.intro point_035 (And.intro point_036 (And.intro point_037 (And.intro point_038 (And.intro point_039 (And.intro point_040 (And.intro point_041 (And.intro point_042 (And.intro point_043 (And.intro point_044 (And.intro point_045 (And.intro point_046 (And.intro point_047 (And.intro point_048 (And.intro point_049 (And.intro point_050 (And.intro point_051 (And.intro point_052 (And.intro point_053 (And.intro point_054 (And.intro point_055 (And.intro point_056 (And.intro point_057 (And.intro point_058 (And.intro point_059 (And.intro point_060 (And.intro point_061 (And.intro point_062 (And.intro point_063 (And.intro point_064 (And.intro point_065 (And.intro point_066 (And.intro point_067 (And.intro point_068 (And.intro point_069 (And.intro point_070 (And.intro point_071 (And.intro point_072 (And.intro point_073 (And.intro point_074 (And.intro point_075 (And.intro point_076 (And.intro point_077 (And.intro point_078 (And.intro point_079 (And.intro point_080 (And.intro point_081 (And.intro point_082 (And.intro point_083 (And.intro point_084 (And.intro point_085 (And.intro point_086 (And.intro point_087 (And.intro point_088 (And.intro point_089 (And.intro point_090 (And.intro point_091 (And.intro point_092 (And.intro point_093 (And.intro point_094 (And.intro point_095 (And.intro point_096 (And.intro point_097 (And.intro point_098 (And.intro point_099 (And.intro point_100 (And.intro point_101 (And.intro point_102 (And.intro point_103 (And.intro point_104 (And.intro point_105 (And.intro point_106 (And.intro point_107 (And.intro point_108 (And.intro point_109 (And.intro point_110 (And.intro point_111 (And.intro point_112 (And.intro point_113 (And.intro point_114 (And.intro point_115 (And.intro point_116 (And.intro point_117 (And.intro point_118 (And.intro point_119 (And.intro point_120 (And.intro point_121 (And.intro point_122 (And.intro point_123 (And.intro point_124 (And.intro point_125 (And.intro point_126 (And.intro point_127 (And.intro point_128 (And.intro point_129 (And.intro point_130 (And.intro point_131 (And.intro point_132 (And.intro point_133 (And.intro point_134 (And.intro point_135 (And.intro point_136 (And.intro point_137 (And.intro point_138 (And.intro point_139 (And.intro point_140 (And.intro point_141 (And.intro point_142 (And.intro point_143 (And.intro point_144 (And.intro point_145 (And.intro point_146 (And.intro point_147 (And.intro point_148 (And.intro point_149 (And.intro point_150 (And.intro point_151 (And.intro point_152 (And.intro point_153 (And.intro point_154 (And.intro point_155 (And.intro point_156 (And.intro point_157 (And.intro point_158 (And.intro point_159 (And.intro point_160 (And.intro point_161 (And.intro point_162 (And.intro point_163 (And.intro point_164 (And.intro point_165 (And.intro point_166 (And.intro point_167 (And.intro point_168 (And.intro point_169 (And.intro point_170 (And.intro point_171 (And.intro point_172 (And.intro point_173 (And.intro point_174 (And.intro point_175 (And.intro point_176 (And.intro point_177 (And.intro point_178 (And.intro point_179 (And.intro point_180 (And.intro point_181 (And.intro point_182 (And.intro point_183 (And.intro point_184 (And.intro point_185 (And.intro point_186 (And.intro point_187 (And.intro point_188 (And.intro point_189 (And.intro point_190 (And.intro point_191 (And.intro point_192 (And.intro point_193 (And.intro point_194 (And.intro point_195 (And.intro point_196 (And.intro point_197 (And.intro point_198 (And.intro point_199 (And.intro point_200 (And.intro point_201 (And.intro point_202 (And.intro point_203 (And.intro point_204 (And.intro point_205 (And.intro point_206 (And.intro point_207 (And.intro point_208 (And.intro point_209 (And.intro point_210 (And.intro point_211 (And.intro point_212 (And.intro point_213 (And.intro point_214 (And.intro point_215 (And.intro point_216 (And.intro point_217 (And.intro point_218 (And.intro point_219 (And.intro point_220 (And.intro point_221 (And.intro point_222 (And.intro point_223 (And.intro point_224 (And.intro point_225 (And.intro point_226 (And.intro point_227 (And.intro point_228 (And.intro point_229 (And.intro point_230 (And.intro point_231 (And.intro point_232 (And.intro point_233 (And.intro point_234 (And.intro point_235 (And.intro point_236 (And.intro point_237 (And.intro point_238 (And.intro point_239 (And.intro point_240 (And.intro point_241 (And.intro point_242 (And.intro point_243 (And.intro point_244 (And.intro point_245 (And.intro point_246 (And.intro point_247 (And.intro point_248 (And.intro point_249 (And.intro point_250 (And.intro point_251 (And.intro point_252 (And.intro point_253 (And.intro point_254 (point_255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem G2_valid : Valid HKOTriameter.G2 HKOTriameter.D2 cut := by
  intro S
  have hs : S ∈ (Finset.univ : Finset (Fin 8)).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ S)
  rw [all_subsets] at hs
  exact (List.forall_iff_forall_mem.mp all_entries_valid) S (List.mem_toFinset.mp hs)

#print axioms G2_valid
end CodexPaper4.G2DHData
