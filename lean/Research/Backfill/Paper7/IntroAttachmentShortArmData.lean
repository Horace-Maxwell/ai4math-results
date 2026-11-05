import Research.Backfill.Paper7.IntroNonattachmentDegreeThreeExclusion
import Research.Backfill.Paper7.IntroMixedPendantArmExclusion

/-! Local data for an actual outside component. The spectral-three count
and each terminal leaf are derived from the original hypotheses. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroAttachmentShape
open SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7UnicyclicAttachment Paper7IntroNonattachmentThree
open Paper7IntroEven Paper7IntroFour Paper7IntroCycleNeighborhood
open Paper7IntroTerminalExistence Paper7IntroLocalQuartic Paper7IntroPendantFour

theorem degree_two_neighbor_split
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x p : V) (hx : G.degree x = 2) (hxp : G.Adj x p) :
    ∃ l : V, l ≠ p ∧ G.Adj x l ∧
      ∀ z : V, G.Adj x z ↔ z = p ∨ z = l := by
  have hp : p ∈ G.neighborFinset x := (G.mem_neighborFinset x p).mpr hxp
  have hc : ((G.neighborFinset x).erase p).card = 1 := by
    rw [Finset.card_erase_of_mem hp, G.card_neighborFinset_eq_degree, hx]
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hc
  have hlmem : l ∈ (G.neighborFinset x).erase p := by rw [hl]; simp
  obtain ⟨hlp, hlx⟩ := Finset.mem_erase.mp hlmem
  refine ⟨l, hlp, (G.mem_neighborFinset x l).mp hlx, ?_⟩
  intro z
  constructor
  · intro hxz
    by_cases hzp : z = p
    · exact Or.inl hzp
    · right
      have hz : z ∈ (G.neighborFinset x).erase p :=
        Finset.mem_erase.mpr ⟨hzp, (G.mem_neighborFinset x z).mpr hxz⟩
      rw [hl, Finset.mem_singleton] at hz
      exact hz
  · intro hz
    rcases hz with hzp | hzl
    · exact hzp.symm ▸ hxp
    · exact hzl.symm ▸ (G.mem_neighborFinset x l).mp hlx
#print axioms Paper7IntroAttachmentShape.degree_two_neighbor_split

theorem intro21_even_nonleaf_component_count_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hex : ∃ x : C.supp, x ≠ a ∧ 2 ≤ G.degree x.val.val) :
    (integerSpectrum G).count 3 = 1 := by
  obtain ⟨x, p, _hxa, _hx, hxp, hleaf⟩ :=
    unicyclic_component_terminal_nonleaf_exists G b hG r w hw hlen C a c hac hex
  have hnotalltwo : ¬ (∀ v : V, G.degree v = 2) := by
    intro hall
    obtain ⟨l, hlp, hxl, _hN⟩ :=
      degree_two_neighbor_split G x.val.val p.val.val (hall x.val.val) hxp
    have hl := hleaf l hxl hlp
    have hl2 := hall l
    omega
  rcases intro21_even_actual_spectral_alternatives G b hG hI hn hb with
    hC4 | hC6 | hR3 | hR4
  · obtain ⟨e⟩ : Nonempty (G ≃g cycleGraph 4) := hC4
    exact (hnotalltwo (cycle_iso_degree_two G 4 (by norm_num) e)).elim
  · obtain ⟨e⟩ : Nonempty (G ≃g cycleGraph 6) := hC6
    exact (hnotalltwo (cycle_iso_degree_two G 6 (by norm_num) e)).elim
  · obtain ⟨_z, _u, _v, _hz, _hu, _hv, _hn, _hm, _hlimit, hthree, _hfour, _hdev⟩ := hR3
    exact hthree
  · obtain ⟨_z, _u, _v, _hz, _hu, _hv, _hn, _hm, _hlimit, _hthree, hfour, _hdev⟩ := hR4
    exact (intro21_even_no_top_four G b hG hI hn hb hfour).elim
#print axioms Paper7IntroAttachmentShape.intro21_even_nonleaf_component_count_three

theorem intro21_even_nonattachment_nonleaf_arm
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x : C.supp) (hxa : x ≠ a) (hx : 2 ≤ G.degree x.val.val) :
    G.degree x.val.val = 2 ∧ G.Adj a.val.val x.val.val ∧
    ∃ l : V, l ≠ a.val.val ∧ G.Adj x.val.val l ∧ G.degree l = 1 ∧
      (∃ q : C.supp, q.val.val = l) ∧
      (∀ z : V, G.Adj x.val.val z ↔ z = a.val.val ∨ z = l) ∧
      (∀ z : V, G.Adj l z ↔ z = x.val.val) := by
  have hthree := intro21_even_nonleaf_component_count_three
    G b hG hI hn hb r w hw hlen C a c hac ⟨x, hxa, hx⟩
  have hshort := intro21_even_radius_three_nonattachment_short_arms
    G b hG hI hn hb hthree r w hw hlen C a c hac
  have hx2 : G.degree x.val.val = 2 := by have ht := (hshort x hxa).1; omega
  have hax : G.Adj a.val.val x.val.val := ((hshort x hxa).2 hx).symm
  obtain ⟨l, hla, hxl, hNx⟩ := degree_two_neighbor_split G x.val.val a.val.val hx2 hax.symm
  obtain ⟨_pair, _hp, huniq⟩ :=
    unicyclic_component_attachment_endpoints G b hG r w hw hlen C
  have hlout : l ∉ w.support := by
    intro hlS
    have he := (huniq (x.val, ⟨l, hlS⟩) ⟨x.property, hxl⟩).trans
      (huniq (a.val, c) ⟨a.property, hac⟩).symm
    exact hxa (Subtype.ext (congrArg Prod.fst he))
  let lo : {q : V // q ∉ w.support} := ⟨l, hlout⟩
  have hlC : lo ∈ C.supp := C.mem_supp_of_adj_mem_supp x.property hxl
  let q : C.supp := ⟨lo, hlC⟩
  have hqa : q ≠ a := by
    intro he
    exact hla (congrArg (fun v : C.supp => v.val.val) he)
  have hl1 : G.degree l = 1 := by
    have hpos := hxl.degree_pos_right
    have hlt : G.degree l < 2 := by
      by_contra hnot
      have hlaAdj : G.Adj l a.val.val := (hshort q hqa).2 (by
        change 2 ≤ G.degree l
        omega)
      exact bridge_vertex_no_neighbor_triangle G x.val.val
        (fun v hv => unicyclic_off_cycle_edge_isBridge G b hG r w hw hlen
          x.val.val v x.val.property hv) a.val.val l hax.symm hxl hlaAdj
    omega
  refine ⟨hx2, hax, l, hla, hxl, hl1, ⟨q, rfl⟩, hNx, ?_⟩
  obtain ⟨t, _hlt, hut⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hl1
  intro z
  constructor
  · intro hlz
    exact (hut z hlz).trans (hut x.val.val hxl.symm).symm
  · intro hz
    exact hz.symm ▸ hxl.symm
#print axioms Paper7IntroAttachmentShape.intro21_even_nonattachment_nonleaf_arm

end Paper7IntroAttachmentShape
