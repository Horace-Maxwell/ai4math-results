import Research.Backfill.Paper7.MomentB6Type1122WindowEvalCore

/-! Source-only constructive outer transport of the original1122 windows.
Every evaluation definition precedes proof-local classical reasoning. The
original21 catalogue pairs are counted once as a finite set. No numerical
catalogue block or full reflection count is supplied by this file. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6R1122EvalLoadCenter (S : ℤ) : ℕ := (S-6).toNat
#print axioms Paper7MomentCounts.b6R1122EvalLoadCenter

def b6R1122EvalQLower (C Z : ℕ) : ℕ := C-Z
#print axioms Paper7MomentCounts.b6R1122EvalQLower

def b6R1122EvalQUpper (C Z : ℕ) : ℕ :=
  if Z≤C then min Z (36-Z) else min Z (min (36-Z) (C+2-Z))
#print axioms Paper7MomentCounts.b6R1122EvalQUpper

def b6R1122EvalMassWindow (S M : ℤ) : Finset ℕ :=
  (Finset.Icc ((b6R1122EvalLoadCenter S+1)/2)
    (min 36 (b6R1122EvalLoadCenter S+2))).filter (fun Z =>
      decide (M≤12+5*(Z : ℤ)+(Z : ℤ)^2 ∧ ((Z : ℤ)+9)^2≤6*M+9)=true)
#print axioms Paper7MomentCounts.b6R1122EvalMassWindow

def b6R1122EvalCatalog : Finset (ℤ × ℤ) :=
  {(9,72), (13,84), (17,96),
   (16,240), (20,252), (24,264), (25,312), (29,324),
   (33,336), (34,384), (38,396), (42,408),
   (25,600), (29,612), (33,624), (34,672), (38,684), (42,696), (41,840),
   (36,1260), (40,1272)}
#print axioms Paper7MomentCounts.b6R1122EvalCatalog

def b6R1122EvalQBlock (sm : ℤ × ℤ) (Z B : ℕ) : ℕ :=
  ∑ Q ∈ Finset.Icc (b6R1122EvalQLower (b6R1122EvalLoadCenter sm.1) Z)
    (b6R1122EvalQUpper (b6R1122EvalLoadCenter sm.1) Z),
      b6R1122EvalTerm (Z-2*B) B Q sm.2
#print axioms Paper7MomentCounts.b6R1122EvalQBlock

def b6R1122EvalMassBlock (sm : ℤ × ℤ) (Z : ℕ) : ℕ :=
  ∑ B ∈ Finset.range (Z/2+1),b6R1122EvalQBlock sm Z B
#print axioms Paper7MomentCounts.b6R1122EvalMassBlock

def b6R1122EvalCatalogBlock (sm : ℤ × ℤ) : ℕ :=
  ∑ Z ∈ b6R1122EvalMassWindow sm.1 sm.2,b6R1122EvalMassBlock sm Z
#print axioms Paper7MomentCounts.b6R1122EvalCatalogBlock

def b6R1122EvalTotal : ℕ :=
  ∑ sm ∈ b6R1122EvalCatalog,b6R1122EvalCatalogBlock sm
#print axioms Paper7MomentCounts.b6R1122EvalTotal

theorem b6R1122EvalLoadCenter_eq (S : ℤ) :
    b6R1122EvalLoadCenter S=b6Type1122LoadCenter S := rfl
#print axioms Paper7MomentCounts.b6R1122EvalLoadCenter_eq

theorem b6R1122EvalQLower_eq (C Z : ℕ) :
    b6R1122EvalQLower C Z=b6Type1122QLower C Z := rfl
#print axioms Paper7MomentCounts.b6R1122EvalQLower_eq

theorem b6R1122EvalQUpper_eq (C Z : ℕ) :
    b6R1122EvalQUpper C Z=b6Type1122QUpper C Z := rfl
#print axioms Paper7MomentCounts.b6R1122EvalQUpper_eq

theorem b6R1122EvalMassWindow_eq (S M : ℤ) :
    b6R1122EvalMassWindow S M=b6Type1122MassWindow S M := by
  classical
  ext Z
  simp only [b6R1122EvalMassWindow,b6Type1122MassWindow,b6R1122EvalLoadCenter_eq,
    Finset.mem_filter,decide_eq_true_eq]
#print axioms Paper7MomentCounts.b6R1122EvalMassWindow_eq

theorem b6R1122EvalCatalog_eq : b6R1122EvalCatalog=b6FeatureCatalog := by
  classical
  ext sm
  simp only [b6R1122EvalCatalog,b6FeatureCatalog,Finset.mem_insert,Finset.mem_singleton]
#print axioms Paper7MomentCounts.b6R1122EvalCatalog_eq

theorem b6R1122EvalQBlock_eq (sm : ↥b6FeatureCatalog)
    (Z : ↥(b6Type1122MassWindow sm.val.1 sm.val.2)) (B : Fin (Z.val/2+1)) :
    b6R1122EvalQBlock sm.val Z.val B.val=b6Type1122WindowQBlock sm Z B := by
  classical
  unfold b6R1122EvalQBlock b6Type1122WindowQBlock
  simp only [b6R1122EvalLoadCenter_eq,b6R1122EvalQLower_eq,b6R1122EvalQUpper_eq,
    b6R1122EvalTerm_eq]
  exact (Finset.sum_coe_sort _ _).symm
#print axioms Paper7MomentCounts.b6R1122EvalQBlock_eq

theorem b6R1122EvalMassBlock_eq (sm : ↥b6FeatureCatalog)
    (Z : ↥(b6Type1122MassWindow sm.val.1 sm.val.2)) :
    b6R1122EvalMassBlock sm.val Z.val=b6Type1122WindowMassBlock sm Z := by
  classical
  unfold b6R1122EvalMassBlock b6Type1122WindowMassBlock
  rw [← Fin.sum_univ_eq_sum_range (fun B : ℕ => b6R1122EvalQBlock sm.val Z.val B)
    (Z.val/2+1)]
  apply Finset.sum_congr rfl
  intro B _hB
  exact b6R1122EvalQBlock_eq sm Z B
#print axioms Paper7MomentCounts.b6R1122EvalMassBlock_eq

theorem b6R1122EvalCatalogBlock_eq (sm : ↥b6FeatureCatalog) :
    b6R1122EvalCatalogBlock sm.val=b6Type1122WindowCatalogBlock sm := by
  classical
  unfold b6R1122EvalCatalogBlock b6Type1122WindowCatalogBlock
  rw [b6R1122EvalMassWindow_eq,
    ← Finset.sum_coe_sort (b6Type1122MassWindow sm.val.1 sm.val.2)
      (fun Z : ℕ => b6R1122EvalMassBlock sm.val Z)]
  apply Finset.sum_congr rfl
  intro Z _hZ
  exact b6R1122EvalMassBlock_eq sm Z
#print axioms Paper7MomentCounts.b6R1122EvalCatalogBlock_eq

theorem b6R1122EvalTotal_eq : b6R1122EvalTotal=b6Type1122WindowCount := by
  classical
  unfold b6R1122EvalTotal b6Type1122WindowCount
  rw [b6R1122EvalCatalog_eq,
    ← Finset.sum_coe_sort b6FeatureCatalog (fun sm : ℤ × ℤ => b6R1122EvalCatalogBlock sm)]
  apply Finset.sum_congr rfl
  intro sm _hsm
  exact b6R1122EvalCatalogBlock_eq sm
#print axioms Paper7MomentCounts.b6R1122EvalTotal_eq

end Paper7MomentCounts
namespace Paper7MomentCanonicalSix
open Paper7MomentCounts

theorem b6_reflection_zero_count_eq_eval_total :
    b6FixedCount (b6Reflection 0)=b6R1122EvalTotal :=
  b6_reflection_zero_count_eq_window_sum.trans b6R1122EvalTotal_eq.symm
#print axioms Paper7MomentCanonicalSix.b6_reflection_zero_count_eq_eval_total

end Paper7MomentCanonicalSix
