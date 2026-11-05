import Research.Backfill.Paper7.IntroRootedTreeShortArms
import Research.Backfill.Paper7.IntroTerminalLeafPair
import Research.Backfill.Paper7.IntroOffCycleTerminal

/-! Explicit component instances and neighbor-set cardinalities transport
an actual terminal fan to the original graph. Original nonroot degree at
most three then forces the terminal parent to be the attachment. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroNonattachmentThree
open SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroTerminalExistence Paper7IntroLocalQuartic

theorem outside_component_short_arms_of_degree_le_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (hthree : (integerSpectrum G).count 3 = 1)
    (S : Set V) (hforest : (deleteVertices G S).IsAcyclic)
    (C : (deleteVertices G S).ConnectedComponent)
    [Fintype C.supp] [DecidableEq C.supp] [DecidableRel C.toSimpleGraph.Adj]
    (a : C.supp)
    (hgate : ∀ (v : {q : V // q ∉ S}), v ∈ C.supp →
      ∀ t : S, G.Adj v.val t.val → v = a.val)
    (hbound : ∀ v : C.supp, v ≠ a → G.degree v.val.val ≤ 3) :
    ∀ u : C.supp, u ≠ a → G.degree u.val.val ≤ 2 ∧
      (2 ≤ G.degree u.val.val → G.Adj u.val.val a.val.val) := by
  have hd (x : C.supp) (hxa : x ≠ a) :
      C.toSimpleGraph.degree x = G.degree x.val.val := by
    have hxs : G.neighborSet x.val.val ⊆ (Sᶜ : Set V) := by
      intro j hxj hjS
      exact hxa (Subtype.ext (hgate x.val x.property ⟨j, hjS⟩ hxj))
    calc
      C.toSimpleGraph.degree x = (C.toSimpleGraph.neighborSet x).ncard :=
        (C.toSimpleGraph.ncard_neighborSet x).symm
      _ = ((G.induce (Sᶜ : Set V)).neighborSet x.val).ncard :=
        component_neighborSet_ncard_eq (G.induce (Sᶜ : Set V)) C x
      _ = (G.induce (Sᶜ : Set V)).degree x.val :=
        (G.induce (Sᶜ : Set V)).ncard_neighborSet x.val
      _ = G.degree x.val.val :=
        SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := Sᶜ) (v := x.val) hxs
  have hT : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph,
      Paper7UnicyclicComponentPaths.connected_component_isAcyclic (deleteVertices G S) hforest C⟩
  have hterminal : ∀ x p : C.supp, x ≠ a → 2 ≤ C.toSimpleGraph.degree x →
      C.toSimpleGraph.Adj x p →
      (∀ j, C.toSimpleGraph.Adj x j → j ≠ p →
        C.toSimpleGraph.degree j = 1 ∧ j ≠ a) →
      C.toSimpleGraph.degree x = 2 ∧ p = a := by
    intro x p hxa hx hxp hleaf
    have hxG : 2 ≤ G.degree x.val.val := (hd x hxa) ▸ hx
    have hleafG : ∀ j, G.Adj x.val.val j → j ≠ p.val.val → G.degree j = 1 := by
      intro j hxj hjp
      have hjS : j ∉ S := by
        intro hjS
        exact hxa (Subtype.ext (hgate x.val x.property ⟨j, hjS⟩ hxj))
      let jo : {q : V // q ∉ S} := ⟨j, hjS⟩
      have hjC : jo ∈ C.supp := C.mem_supp_of_adj_mem_supp x.property hxj
      let y : C.supp := ⟨jo, hjC⟩
      have hyp : y ≠ p := by
        intro he
        exact hjp (congrArg (fun v : C.supp => v.val.val) he)
      obtain ⟨hy, hya⟩ := hleaf y hxj hyp
      exact (hd y hya) ▸ hy
    have hfan := integral_radius_three_small_terminal_fan_degree_two
      G hG hI hthree x.val.val p.val.val hxp hxG (hbound x hxa) hleafG
    refine ⟨(hd x hxa).trans hfan.1, ?_⟩
    by_contra hpa
    have hp := hbound p hpa
    omega
  have hshort := rooted_tree_short_arms_of_terminal_parent_root C.toSimpleGraph hT a hterminal
  intro u hua
  have hu := hshort u hua
  refine ⟨(hd u hua) ▸ hu.1, ?_⟩
  intro hu2
  exact hu.2 ((hd u hua).symm ▸ hu2)
#print axioms Paper7IntroNonattachmentThree.outside_component_short_arms_of_degree_le_three

end Paper7IntroNonattachmentThree
