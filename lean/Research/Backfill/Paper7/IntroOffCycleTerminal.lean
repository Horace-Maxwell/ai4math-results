import Research.Backfill.Paper7.IntroRootedTreeTerminal
import Research.Backfill.Paper7.UnicyclicOffCycleForest
import Research.Backfill.Paper7.UnicyclicComponentAttachment
import Research.Backfill.Paper7.IntroTerminalFanQuartic
import Research.Backfill.Paper7.IntroDegreeThreshold
import Research.Backfill.Paper7.UnicyclicComponentPaths

/-! Actual unique-cycle attachment data transfer a terminal fan from the
outside component to the original graph. The final radius-three dichotomy
derives its leaf condition. It does not assert a positive complementary
spectral count, a Sun shape, or concentration at one cycle vertex. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroTerminalExistence
open SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7UnicyclicStructure Paper7UnicyclicAttachment Paper7IntroLocalQuartic

theorem component_neighborSet_ncard_eq
    {V : Type} (G : SimpleGraph V) (C : G.ConnectedComponent) (x : C.supp) :
    (C.toSimpleGraph.neighborSet x).ncard = (G.neighborSet x.val).ncard := by
  let e : C.toSimpleGraph.neighborSet x ≃ G.neighborSet x.val :=
    { toFun := fun y => ⟨y.val.val, y.property⟩
      invFun := fun y =>
        ⟨⟨y.val, C.mem_supp_of_adj_mem_supp x.property y.property⟩, y.property⟩
      left_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        rfl }
  exact Set.ncard_congr' e
#print axioms Paper7IntroTerminalExistence.component_neighborSet_ncard_eq

theorem outside_component_degree_eq_of_ne_attachment
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (C : (G.induce (Sᶜ : Set V)).ConnectedComponent) (a x : C.supp)
    (hgate : ∀ (y : {v : V // v ∉ S}), y ∈ C.supp →
      ∀ z : S, G.Adj y.val z.val → y = a.val)
    (hxa : x ≠ a) : C.toSimpleGraph.degree x = G.degree x.val.val := by
  have hxs : G.neighborSet x.val.val ⊆ (Sᶜ : Set V) := by
    intro y hxy hyS
    have he := hgate x.val x.property ⟨y, hyS⟩ hxy
    exact hxa (Subtype.ext he)
  calc
    C.toSimpleGraph.degree x = (C.toSimpleGraph.neighborSet x).ncard :=
      (C.toSimpleGraph.ncard_neighborSet x).symm
    _ = ((G.induce (Sᶜ : Set V)).neighborSet x.val).ncard :=
      component_neighborSet_ncard_eq (G.induce (Sᶜ : Set V)) C x
    _ = (G.induce (Sᶜ : Set V)).degree x.val :=
      (G.induce (Sᶜ : Set V)).ncard_neighborSet x.val
    _ = G.degree x.val.val :=
      SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := Sᶜ) (v := x.val) hxs
#print axioms Paper7IntroTerminalExistence.outside_component_degree_eq_of_ne_attachment

private theorem outside_forest_component_terminal_transfer
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (hforest : (deleteVertices G S).IsAcyclic)
    (C : (deleteVertices G S).ConnectedComponent) (a : C.supp)
    (hgate : ∀ (y : {v : V // v ∉ S}), y ∈ C.supp →
      ∀ z : S, G.Adj y.val z.val → y = a.val)
    (hex : ∃ u : C.supp, u ≠ a ∧ 2 ≤ G.degree u.val.val) :
    ∃ x p : C.supp, x ≠ a ∧ 2 ≤ G.degree x.val.val ∧ G.Adj x.val.val p.val.val ∧
      ∀ j, G.Adj x.val.val j → j ≠ p.val.val → G.degree j = 1 := by
  have hd (x : C.supp) (hxa : x ≠ a) : C.toSimpleGraph.degree x = G.degree x.val.val :=
    outside_component_degree_eq_of_ne_attachment G S C a x hgate hxa
  have hT : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph,
      Paper7UnicyclicComponentPaths.connected_component_isAcyclic (deleteVertices G S) hforest C⟩
  have hexT : ∃ u : C.supp, u ≠ a ∧ 2 ≤ C.toSimpleGraph.degree u := by
    obtain ⟨u, hua, hu⟩ := hex
    exact ⟨u, hua, (hd u hua).symm ▸ hu⟩
  obtain ⟨x, p, hxa, hx, hxp, hleaf⟩ :=
    rooted_tree_terminal_nonleaf_exists C.toSimpleGraph hT a hexT
  refine ⟨x, p, hxa, (hd x hxa) ▸ hx, hxp, ?_⟩
  intro j hxj hjp
  have hjS : j ∉ S := by
    intro hjS
    exact hxa (Subtype.ext (hgate x.val x.property ⟨j, hjS⟩ hxj))
  let j' : {v : V // v ∉ S} := ⟨j, hjS⟩
  have hjC : j' ∈ C.supp := C.mem_supp_of_adj_mem_supp x.property hxj
  let y : C.supp := ⟨j', hjC⟩
  have hyp : y ≠ p := by
    intro he
    exact hjp (congrArg (fun t : C.supp => t.val.val) he)
  obtain ⟨hydeg, hya⟩ := hleaf y hxj hyp
  exact (hd y hya) ▸ hydeg

theorem unicyclic_component_terminal_nonleaf_exists
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {v | v ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {v : V // v ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hex : ∃ u : C.supp, u ≠ a ∧ 2 ≤ G.degree u.val.val) :
    ∃ x p : C.supp, x ≠ a ∧ 2 ≤ G.degree x.val.val ∧ G.Adj x.val.val p.val.val ∧
      ∀ j, G.Adj x.val.val j → j ≠ p.val.val → G.degree j = 1 := by
  have hgate : ∀ (y : {v : V // v ∉ w.support}), y ∈ C.supp →
      ∀ z : {v : V // v ∈ w.support}, G.Adj y.val z.val → y = a.val := by
    intro y hy z hyz
    obtain ⟨pair, _hpair, huniq⟩ :=
      unicyclic_component_attachment_endpoints G b hG r w hw hlen C
    have hya := huniq (y, z) ⟨hy, hyz⟩
    have haa := huniq (a.val, c) ⟨a.property, hac⟩
    exact congrArg Prod.fst (hya.trans haa.symm)
  exact outside_forest_component_terminal_transfer G {v | v ∈ w.support}
    (unicyclic_off_cycle_isAcyclic G b hG r w hw hlen) C a hgate hex
#print axioms Paper7IntroTerminalExistence.unicyclic_component_terminal_nonleaf_exists

theorem integral_radius_three_off_cycle_terminal_dichotomy
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hthree : (integerSpectrum G).count 3 = 1)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {v | v ∈ w.support}).ConnectedComponent) :
    ∃ (a : C.supp) (c : {v : V // v ∈ w.support}), G.Adj a.val.val c.val ∧
      ((∀ u : C.supp, u ≠ a → G.degree u.val.val ≤ 1) ∨
        ∃ x p : C.supp, x ≠ a ∧ 2 ≤ G.degree x.val.val ∧ G.Adj x.val.val p.val.val ∧
          (4 ≤ G.degree x.val.val ∨ 4 ≤ G.degree p.val.val) ∧
          ∀ j, G.Adj x.val.val j → j ≠ p.val.val → G.degree j = 1) := by
  obtain ⟨⟨a, c⟩, ⟨ha, hac⟩, _hu⟩ :=
    unicyclic_component_attachment_endpoints G b hG r w hw hlen C
  let a' : C.supp := ⟨a, ha⟩
  refine ⟨a', c, hac, ?_⟩
  by_cases hex : ∃ u : C.supp, u ≠ a' ∧ 2 ≤ G.degree u.val.val
  · obtain ⟨x, p, hxa, hx, hxp, hleaf⟩ :=
      unicyclic_component_terminal_nonleaf_exists G b hG r w hw hlen C a' c hac hex
    right
    refine ⟨x, p, hxa, hx, hxp, ?_, hleaf⟩
    by_cases hx4 : 4 ≤ G.degree x.val.val
    · exact Or.inl hx4
    · exact Or.inr (integral_radius_three_small_terminal_fan_parent_ge_four
        G hG.1 hI hthree x.val.val p.val.val hxp (by omega) hleaf)
  · left
    intro u hua
    have hn : ¬2 ≤ G.degree u.val.val := fun hu => hex ⟨u, hua, hu⟩
    omega
#print axioms Paper7IntroTerminalExistence.integral_radius_three_off_cycle_terminal_dichotomy

end Paper7IntroTerminalExistence
