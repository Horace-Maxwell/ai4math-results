import Research.Backfill.Paper7.IntroNonattachmentNonleafExclusion

/-! The actual deleted-cycle component is its attachment and genuine leaves.
The finite leaf index is canonical; no path, coverage, leaf, spectral-count,
or classification premise is added to the original graph conditions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroAttachmentLeafStar
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7UnicyclicAttachment Paper7IntroStarExclusion Paper7IntroFour

theorem intro21_even_nonattachment_adj_attachment
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x : C.supp) (hxa : x ≠ a) : G.Adj x.val.val a.val.val := by
  obtain ⟨_pair, _hp, huniq⟩ :=
    unicyclic_component_attachment_endpoints G b hG r w hw hlen C
  have hgate : ∀ (v : {q : V // q ∉ w.support}), v ∈ C.supp →
      ∀ t : {q : V // q ∈ w.support}, G.Adj v.val t.val → v = a.val := by
    intro v hv t hvt
    exact congrArg Prod.fst ((huniq (v, t) ⟨hv, hvt⟩).trans
      (huniq (a.val, c) ⟨a.property, hac⟩).symm)
  obtain ⟨j, z, hxj, hjz, hzx⟩ := unicyclic_two_step_continuation G b hG x.val.val
  have hj2 : 2 ≤ G.degree j := by
    have hpos := hxj.degree_pos_right
    by_contra hnot
    have hj1 : G.degree j = 1 := by omega
    obtain ⟨t, _hjt, hut⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hj1
    exact hzx ((hut z hjz).trans (hut x.val.val hxj.symm).symm)
  have hjout : j ∉ w.support := by
    intro hjS
    exact hxa (Subtype.ext (hgate x.val x.property ⟨j, hjS⟩ hxj))
  let jo : {q : V // q ∉ w.support} := ⟨j, hjout⟩
  have hjC : jo ∈ C.supp := C.mem_supp_of_adj_mem_supp x.property hxj
  let q : C.supp := ⟨jo, hjC⟩
  have hja : j = a.val.val := by
    by_contra hne
    have hqa : q ≠ a := by
      intro he
      exact hne (congrArg (fun v : C.supp => v.val.val) he)
    have hq1 := intro21_even_nonattachment_degree_one G b hG hI hn hb r w hw hlen C a c hac q hqa
    change G.degree j = 1 at hq1
    omega
  simpa only [hja] using hxj
#print axioms Paper7IntroAttachmentLeafStar.intro21_even_nonattachment_adj_attachment

theorem intro21_even_actual_attachment_leaf_star
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val) :
    ∃ Y : Finset V,
      Y = (G.neighborFinset a.val.val).erase c.val ∧
      G.degree a.val.val = Y.card + 1 ∧ a.val.val ≠ c.val ∧
      Function.Injective (fun i : Y => i.val) ∧
      (∀ i : Y, (∃ x : C.supp, x.val.val = i.val) ∧
        G.degree i.val = 1 ∧ i.val ≠ a.val.val ∧ i.val ≠ c.val) ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val) ∧
      (∀ z : V, G.Adj a.val.val z ↔ z = c.val ∨ ∃ i : Y, z = i.val) ∧
      (∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a.val.val) := by
  obtain ⟨_pair, _hp, huniq⟩ :=
    unicyclic_component_attachment_endpoints G b hG r w hw hlen C
  have hchild : ∀ y : V, G.Adj a.val.val y → y ≠ c.val →
      ∃ x : C.supp, x.val.val = y := by
    intro y hay hyc
    have hyout : y ∉ w.support := by
      intro hyS
      have he := (huniq (a.val, ⟨y, hyS⟩) ⟨a.property, hay⟩).trans
        (huniq (a.val, c) ⟨a.property, hac⟩).symm
      exact hyc (congrArg (fun p : {q : V // q ∉ w.support} ×
        {q : V // q ∈ w.support} => p.2.val) he)
    let yo : {q : V // q ∉ w.support} := ⟨y, hyout⟩
    have hyC : yo ∈ C.supp := C.mem_supp_of_adj_mem_supp a.property hay
    exact ⟨⟨yo, hyC⟩, rfl⟩
  let Y : Finset V := (G.neighborFinset a.val.val).erase c.val
  have hY (y : V) : y ∈ Y ↔ y ≠ c.val ∧ G.Adj a.val.val y := by
    simp only [Y, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
  have hYC (i : Y) : ∃ x : C.supp, x.val.val = i.val :=
    hchild i.val ((hY i.val).mp i.property).2 ((hY i.val).mp i.property).1
  have hleaf (i : Y) : G.degree i.val = 1 := by
    obtain ⟨x, hxi⟩ := hYC i
    have hai := ((hY i.val).mp i.property).2
    have hxa : x ≠ a := by
      intro he
      have hv : x.val.val = a.val.val := congrArg (fun q : C.supp => q.val.val) he
      exact hai.ne (hv.symm.trans hxi)
    have hx1 := intro21_even_nonattachment_degree_one G b hG hI hn hb r w hw hlen C a c hac x hxa
    exact hxi ▸ hx1
  have hcard : G.degree a.val.val = Y.card + 1 := by
    have hc : Y.card = G.degree a.val.val - 1 := by
      dsimp [Y]
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset a.val.val c.val).mpr hac),
        G.card_neighborFinset_eq_degree]
    have hpos := hac.degree_pos_left
    omega
  refine ⟨Y, rfl, hcard, hac.ne, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact Subtype.ext hij
  · intro i
    have hi := (hY i.val).mp i.property
    exact ⟨hYC i, hleaf i, hi.2.ne.symm, hi.1⟩
  · intro x
    by_cases hxa : x = a
    · exact Or.inl hxa
    · have hax := (intro21_even_nonattachment_adj_attachment G b hG hI hn hb
        r w hw hlen C a c hac x hxa).symm
      have hxc : x.val.val ≠ c.val := by
        intro he
        exact x.val.property (he.symm ▸ c.property)
      exact Or.inr ⟨⟨x.val.val, (hY x.val.val).mpr ⟨hxc, hax⟩⟩, rfl⟩
  · intro z
    constructor
    · intro haz
      by_cases hzc : z = c.val
      · exact Or.inl hzc
      · exact Or.inr ⟨⟨z, (hY z).mpr ⟨hzc, haz⟩⟩, rfl⟩
    · rintro (rfl | ⟨i, rfl⟩)
      · exact hac
      · exact ((hY i.val).mp i.property).2
  · intro i z
    obtain ⟨t, _hit, hut⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp (hleaf i)
    have hia : G.Adj i.val a.val.val := ((hY i.val).mp i.property).2.symm
    constructor
    · intro hiz
      exact (hut z hiz).trans (hut a.val.val hia).symm
    · rintro rfl
      exact hia
#print axioms Paper7IntroAttachmentLeafStar.intro21_even_actual_attachment_leaf_star

end Paper7IntroAttachmentLeafStar
