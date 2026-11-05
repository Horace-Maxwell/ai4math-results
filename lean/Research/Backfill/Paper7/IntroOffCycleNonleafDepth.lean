import Research.Backfill.Paper7.IntroTreeTerminalDepth
import Research.Backfill.Paper7.IntroOffCycleStrictBounds
import Research.Backfill.Paper7.IntroOffCycleTerminal
import Research.Backfill.Paper7.IntroTerminalLeafPair

/-! Actual outside-component nonleaves lie within two tree edges of the
unique attachment. Route P is a pending dependency until Root verifies it.
No no-branching, terminal shape, or positive complementary count is assumed
in the final original-graph statement. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroTreeDepth
open SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroCutGap Paper7IntroHighVertex Paper7IntroCycleComplement
open Paper7IntroTerminalExistence Paper7IntroLocalQuartic Paper7UnicyclicAttachment

theorem intro21_even_component_degree_four_only_next_to_attachment
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val) :
    ∀ x : C.supp, x ≠ a → G.degree x.val.val ≤ 4 ∧
      (4 ≤ G.degree x.val.val → G.Adj x.val.val a.val.val) := by
  intro x hxa
  have hxv : x.val.val ≠ a.val.val := by
    intro he
    exact hxa (Subtype.ext (Subtype.ext he))
  let u : {q : V // q ≠ a.val.val} := ⟨x.val.val, hxv⟩
  let D := (vertexDeletedGraph G a.val.val).connectedComponentMk u
  let i : D.supp := ⟨u, rfl⟩
  have hp := intro21_even_attachment_residual_positive_and_degree_bound
    G b hG hI hn hb r w hw hlen C a.val a.property c hac
    D u (show u ∈ D.supp from rfl) x.val.property x.property
  have hi := hp.2 i
  have hr := deleted_component_original_degree_restore G a.val.val D i
  change G.degree x.val.val = ((vertexDeletedGraph G a.val.val).induce D.supp).degree i +
    if G.Adj x.val.val a.val.val then 1 else 0 at hr
  refine ⟨?_, ?_⟩
  · split_ifs at hr <;> omega
  · intro hx4
    by_contra hno
    rw [ite_eq_right hno, add_zero] at hr
    omega
#print axioms Paper7IntroTreeDepth.intro21_even_component_degree_four_only_next_to_attachment

private theorem outside_tree_nonleaf_depth_from_degree_location
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (hthree : (integerSpectrum G).count 3 = 1) (S : Set V)
    (hforest : (deleteVertices G S).IsAcyclic)
    (C : (deleteVertices G S).ConnectedComponent) (a : C.supp)
    (hgate : ∀ (y : {q : V // q ∉ S}), y ∈ C.supp →
      ∀ z : S, G.Adj y.val z.val → y = a.val)
    (hbound : ∀ x : C.supp, x ≠ a → G.degree x.val.val ≤ 4 ∧
      (4 ≤ G.degree x.val.val → G.Adj x.val.val a.val.val)) :
    ∀ u : C.supp, u ≠ a → 2 ≤ G.degree u.val.val → C.toSimpleGraph.dist a u ≤ 2 := by
  have hd (x : C.supp) (hxa : x ≠ a) : C.toSimpleGraph.degree x = G.degree x.val.val :=
    outside_component_degree_eq_of_ne_attachment G S C a x hgate hxa
  have hT : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph,
      Paper7UnicyclicComponentPaths.connected_component_isAcyclic (deleteVertices G S) hforest C⟩
  have hterminal : ∀ x p : C.supp, x ≠ a → 2 ≤ C.toSimpleGraph.degree x →
      C.toSimpleGraph.Adj x p →
      (∀ j, C.toSimpleGraph.Adj x j → j ≠ p → C.toSimpleGraph.degree j = 1 ∧ j ≠ a) →
      C.toSimpleGraph.Adj a x ∨ p = a ∨ C.toSimpleGraph.Adj a p := by
    intro x p hxa hx hxp hleaf
    have hxG : 2 ≤ G.degree x.val.val := (hd x hxa) ▸ hx
    by_cases hx4 : 4 ≤ G.degree x.val.val
    · exact Or.inl ((hbound x hxa).2 hx4).symm
    · have hleafG : ∀ j, G.Adj x.val.val j → j ≠ p.val.val → G.degree j = 1 := by
        intro j hxj hjp
        have hjS : j ∉ S := by
          intro hjS
          exact hxa (Subtype.ext (hgate x.val x.property ⟨j, hjS⟩ hxj))
        let j' : {q : V // q ∉ S} := ⟨j, hjS⟩
        have hjC : j' ∈ C.supp := C.mem_supp_of_adj_mem_supp x.property hxj
        let y : C.supp := ⟨j', hjC⟩
        have hyp : y ≠ p := by
          intro he
          exact hjp (congrArg (fun t : C.supp => t.val.val) he)
        obtain ⟨hydeg, hya⟩ := hleaf y hxj hyp
        exact (hd y hya) ▸ hydeg
      have hp := (integral_radius_three_small_terminal_fan_degree_two
        G hG hI hthree x.val.val p.val.val hxp hxG (by omega) hleafG).2
      by_cases hpa : p = a
      · exact Or.inr (Or.inl hpa)
      · exact Or.inr (Or.inr ((hbound p hpa).2 hp).symm)
  intro u hua hu
  exact rooted_tree_nonleaf_depth_le_two_of_terminal_location C.toSimpleGraph hT a
    hterminal u hua ((hd u hua).symm ▸ hu)

theorem intro21_even_radius_three_component_nonleaf_depth_le_two
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (hthree : (integerSpectrum G).count 3 = 1)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent) :
    ∃ (a : C.supp) (c : {q : V // q ∈ w.support}), G.Adj a.val.val c.val ∧
      ∀ u : C.supp, u ≠ a → 2 ≤ G.degree u.val.val → C.toSimpleGraph.dist a u ≤ 2 := by
  obtain ⟨ao, c, ha, hac, huniq, _hwalk⟩ :=
    unicyclic_component_attachment_data G b hG r w hw hlen C
  let a : C.supp := ⟨ao, ha⟩
  have hgate : ∀ (y : {q : V // q ∉ w.support}), y ∈ C.supp →
      ∀ z : {q : V // q ∈ w.support}, G.Adj y.val z.val → y = a.val := by
    intro y hy z hyz
    exact (huniq y z hy hyz).1
  refine ⟨a, c, hac, ?_⟩
  exact outside_tree_nonleaf_depth_from_degree_location G hG.1 hI hthree
    {q | q ∈ w.support} (Paper7UnicyclicStructure.unicyclic_off_cycle_isAcyclic G b hG r w hw hlen)
    C a hgate (intro21_even_component_degree_four_only_next_to_attachment
      G b hG hI hn hb r w hw hlen C a c hac)
#print axioms Paper7IntroTreeDepth.intro21_even_radius_three_component_nonleaf_depth_le_two

end Paper7IntroTreeDepth
