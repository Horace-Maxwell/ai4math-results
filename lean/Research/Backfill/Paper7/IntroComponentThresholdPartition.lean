import Research.Backfill.Paper7.IntroDegreeThreshold
import Research.Backfill.Paper7.IntroSeparatedPartitionSpectrum

/-! Assemble the threshold partition before instantiating a concrete deleted graph. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroHighBranch
open BackfillPaper7.Challenge Paper7IntroCutGap

theorem induced_component_threshold_budget
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (f : W → V)
    (hf : Function.Injective f) (hAdj : ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j))
    (C : H.ConnectedComponent) (t : ℝ) :
    Ngt (H.induce C.supp) t + Ngt (H.induce (C.suppᶜ : Set W)) t ≤ Ngt G t := by
  have hsep : ∀ i ∈ C.supp, ∀ j ∉ C.supp, ¬H.Adj i j := by
    intro i hi j hj hij
    exact hj (C.mem_supp_of_adj_mem_supp hi hij)
  have hcount (T : Set W) (i j : Fintype T) :
      @Ngt T i inferInstance (H.induce T) inferInstance t =
        @Ngt T j inferInstance (H.induce T) inferInstance t := by
    cases Subsingleton.elim i j
    rfl
  have part (T : Set W) (ht : ∀ i ∈ T, ∀ j ∉ T, ¬H.Adj i j) :
      Ngt H t = Ngt (H.induce T) t + Ngt (H.induce (Tᶜ : Set W)) t := by
    unfold Ngt
    rw [separated_partition_spec H T ht, Multiset.filter_add, Multiset.card_add]
  have hpart : Ngt H t =
      Ngt (H.induce C.supp) t + Ngt (H.induce (C.suppᶜ : Set W)) t := by
    convert part C.supp hsep using 1
    exact congrArg₂ (fun x y : ℕ => x + y)
      (hcount C.supp _ _) (hcount (C.suppᶜ : Set W) _ _)
  calc
    Ngt (H.induce C.supp) t + Ngt (H.induce (C.suppᶜ : Set W)) t = Ngt H t := hpart.symm
    _ ≤ Ngt G t := induced_Ngt_le G H f hf hAdj t
#print axioms Paper7IntroHighBranch.induced_component_threshold_budget

end Paper7IntroHighBranch
