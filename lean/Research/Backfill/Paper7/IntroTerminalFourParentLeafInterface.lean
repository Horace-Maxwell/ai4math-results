import Research.Backfill.Paper7.IntroOffCycleTerminalFourRadiusOne
import Research.Backfill.Paper7.IntroOffCycleTerminalCompetition

/-! Under the original even integral order bound, an actual degree-four
terminal adjacent to the outside-component attachment forces all other
attachment neighbors, except its actual cycle neighbor, to be genuine leaves.
No conditional parent-norm candidate is imported. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroTerminalFourRemote
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7UnicyclicAttachment Paper7IntroPendantFour Paper7IntroTerminalCompetition

theorem intro21_even_attachment_terminal_four_other_neighbors_leaves
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x : C.supp) (hxa : G.Adj x.val.val a.val.val) (hx : G.degree x.val.val = 4)
    (hxleaf : ∀ j, G.Adj x.val.val j → j ≠ a.val.val → G.degree j = 1) :
    ∀ j, G.Adj a.val.val j → j ≠ x.val.val → j ≠ c.val → G.degree j = 1 := by
  have hrad := intro21_even_attachment_terminal_four_all_nonleaves_adjacent
    G b hG hI hn hb r w hw hlen C a c hac x hxa hx hxleaf
  obtain ⟨_pair, _hpair, huniq⟩ :=
    unicyclic_component_attachment_endpoints G b hG r w hw hlen C
  have hgate : ∀ (y : {q : V // q ∉ w.support}), y ∈ C.supp →
      ∀ z : {q : V // q ∈ w.support}, G.Adj y.val z.val → y = a.val := by
    intro y hy z hyz
    have hyA := huniq (y, z) ⟨hy, hyz⟩
    have haA := huniq (a.val, c) ⟨a.property, hac⟩
    exact congrArg Prod.fst (hyA.trans haA.symm)
  have hcycle : ∀ z : {q : V // q ∈ w.support}, G.Adj a.val.val z.val → z = c := by
    intro z haz
    have hzA := huniq (a.val, z) ⟨a.property, haz⟩
    have hcA := huniq (a.val, c) ⟨a.property, hac⟩
    exact congrArg Prod.snd (hzA.trans hcA.symm)
  have hbridge : ∀ j, G.Adj a.val.val j → G.IsBridge s(a.val.val, j) := by
    intro j haj
    exact unicyclic_off_cycle_edge_isBridge G b hG r w hw hlen a.val.val j a.val.property haj
  intro j haj hjx hjc
  have hjS : j ∉ w.support := by
    intro hjS
    exact hjc (congrArg Subtype.val (hcycle ⟨j, hjS⟩ haj))
  let j' : {q : V // q ∉ w.support} := ⟨j, hjS⟩
  have hjC : j' ∈ C.supp := C.mem_supp_of_adj_mem_supp a.property haj
  let y : C.supp := ⟨j', hjC⟩
  have hya : y ≠ a := by
    intro he
    exact haj.ne (congrArg (fun t : C.supp => t.val.val) he).symm
  have hyleaf : ∀ k, G.Adj y.val.val k → k ≠ a.val.val → G.degree k = 1 := by
    intro k hyk hka
    have hkS : k ∉ w.support := by
      intro hkS
      exact hya (Subtype.ext (hgate y.val y.property ⟨k, hkS⟩ hyk))
    let k' : {q : V // q ∉ w.support} := ⟨k, hkS⟩
    have hkC : k' ∈ C.supp := C.mem_supp_of_adj_mem_supp y.property hyk
    let z : C.supp := ⟨k', hkC⟩
    have hza : z ≠ a := by
      intro he
      exact hka (congrArg (fun t : C.supp => t.val.val) he)
    have hkpos : 0 < G.degree k := hyk.degree_pos_right
    by_contra hk1
    have hz2 : 2 ≤ G.degree z.val.val := by
      change 2 ≤ G.degree k
      omega
    have hzaAdj := hrad z hza hz2
    exact bridge_vertex_no_neighbor_triangle G a.val.val hbridge k j
      hzaAdj.symm haj hyk
  have hjpos : 0 < G.degree j := haj.degree_pos_right
  by_contra hj1
  have hy2 : 2 ≤ G.degree y.val.val := by
    change 2 ≤ G.degree j
    omega
  have he := intro21_even_attachment_degree_four_terminal_unique
    G b hG hI hn hb r w hw hlen C a c hac x y hxa haj.symm hx hy2 hxleaf hyleaf
  exact hjx (congrArg (fun t : C.supp => t.val.val) he).symm
#print axioms Paper7IntroTerminalFourRemote.intro21_even_attachment_terminal_four_other_neighbors_leaves

end Paper7IntroTerminalFourRemote
