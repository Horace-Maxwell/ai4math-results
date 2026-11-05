import Research.Backfill.Paper7.IntroAttachmentShortArmData

/-! The whole actual outside component is a subdivided star whenever it
contains a nonattachment nonleaf. Its finite index is the actual neighbor
finset of the attachment with its unique cycle neighbor removed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroAttachmentShape
open SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7UnicyclicAttachment Paper7IntroNonattachmentThree Paper7IntroFour
open Paper7IntroLocalQuartic Paper7IntroMixedArms

theorem intro21_even_actual_attachment_subdivided_star
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hex : ∃ x : C.supp, x ≠ a ∧ 2 ≤ G.degree x.val.val) :
    ∃ (Y : Finset V) (leaf : Y → V),
      Y = (G.neighborFinset a.val.val).erase c.val ∧
      3 ≤ Y.card ∧ G.degree a.val.val = Y.card + 1 ∧
      (∀ i : Y, ∃ x : C.supp, x.val.val = i.val) ∧
      (∀ i : Y, ∃ x : C.supp, x.val.val = leaf i) ∧
      Function.Injective leaf ∧
      (∀ i : Y, G.degree i.val = 2 ∧ G.degree (leaf i) = 1 ∧
        i.val ≠ a.val.val ∧ i.val ≠ c.val ∧
        leaf i ≠ a.val.val ∧ leaf i ≠ c.val ∧
        ∀ j : Y, leaf i ≠ j.val) ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val ∨ x.val.val = leaf i) ∧
      (∀ z : V, G.Adj a.val.val z ↔ z = c.val ∨ ∃ i : Y, z = i.val) ∧
      (∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a.val.val ∨ z = leaf i) ∧
      (∀ (i : Y) (z : V), G.Adj (leaf i) z ↔ z = i.val) := by
  have hthree := intro21_even_nonleaf_component_count_three
    G b hG hI hn hb r w hw hlen C a c hac hex
  have hshort := intro21_even_radius_three_nonattachment_short_arms
    G b hG hI hn hb hthree r w hw hlen C a c hac
  obtain ⟨x₀, hx₀a, hx₀⟩ := hex
  obtain ⟨hx₀2, hax₀, l₀, hl₀a, hx₀l, hl₀1, _hl₀C, hNx₀, _hNl₀⟩ :=
    intro21_even_nonattachment_nonleaf_arm G b hG hI hn hb r w hw hlen C a c hac x₀ hx₀a hx₀
  have hnoleaf : ∀ k : V, G.Adj a.val.val k → G.degree k ≠ 1 := by
    intro k hak hk
    exact intro21_even_no_mixed_pendant_arms G b hG hI hn hb
      a.val.val x₀.val.val k l₀ hak hax₀ hx₀l hl₀a.symm hk hx₀2 hl₀1
  have ha4 : 4 ≤ G.degree a.val.val := by
    apply (integral_radius_three_small_terminal_fan_degree_two
      G hG.1 hI hthree x₀.val.val a.val.val hax₀.symm
      (by omega) (by omega) ?_).2
    intro z hxz hza
    have hzl : z = l₀ := ((hNx₀ z).mp hxz).resolve_left hza
    exact hzl.symm ▸ hl₀1
  obtain ⟨_pair, _hp, huniq⟩ :=
    unicyclic_component_attachment_endpoints G b hG r w hw hlen C
  have hgate : ∀ (v : {q : V // q ∉ w.support}), v ∈ C.supp →
      ∀ t : {q : V // q ∈ w.support}, G.Adj v.val t.val → v = a.val := by
    intro v hv t hvt
    exact congrArg Prod.fst ((huniq (v, t) ⟨hv, hvt⟩).trans
      (huniq (a.val, c) ⟨a.property, hac⟩).symm)
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
  have hdata : ∀ i : Y, ∃ l : V,
      G.degree i.val = 2 ∧ G.degree l = 1 ∧ l ≠ a.val.val ∧
      (∃ x : C.supp, x.val.val = l) ∧
      (∀ z : V, G.Adj i.val z ↔ z = a.val.val ∨ z = l) ∧
      (∀ z : V, G.Adj l z ↔ z = i.val) := by
    intro i
    obtain ⟨x, hxi⟩ := hYC i
    have hai : G.Adj a.val.val i.val := ((hY i.val).mp i.property).2
    have hxa : x ≠ a := by
      intro he
      have hv : x.val.val = a.val.val := congrArg (fun q : C.supp => q.val.val) he
      exact hai.ne (hv.symm.trans hxi)
    have hxpos : 0 < G.degree x.val.val := by rw [hxi]; exact hai.degree_pos_right
    have hxnot : G.degree x.val.val ≠ 1 := by rw [hxi]; exact hnoleaf i.val hai
    obtain ⟨hx2, _hax, l, hla, _hxl, hl1, hlC, hNx, hNl⟩ :=
      intro21_even_nonattachment_nonleaf_arm G b hG hI hn hb r w hw hlen C a c hac
        x hxa (by omega)
    refine ⟨l, ?_, hl1, hla, hlC, ?_, ?_⟩
    · exact hxi ▸ hx2
    · exact hxi ▸ hNx
    · exact hxi ▸ hNl
  choose leaf hd using hdata
  have hleafinj : Function.Injective leaf := by
    intro i j hij
    apply Subtype.ext
    have hadj : G.Adj (leaf i) i.val := ((hd i).2.2.2.2.2 i.val).mpr rfl
    have he : i.val = j.val := ((hd j).2.2.2.2.2 i.val).mp (hij ▸ hadj)
    exact he
  have hcard : G.degree a.val.val = Y.card + 1 := by
    have hc : Y.card = G.degree a.val.val - 1 := by
      dsimp [Y]
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset a.val.val c.val).mpr hac),
        G.card_neighborFinset_eq_degree]
    omega
  refine ⟨Y, leaf, rfl, by omega, hcard, hYC, ?_, hleafinj, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hd i).2.2.2.1
  · intro i
    have hai := ((hY i.val).mp i.property).2
    refine ⟨(hd i).1, (hd i).2.1, hai.ne.symm,
      ((hY i.val).mp i.property).1, (hd i).2.2.1, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := (hd i).2.2.2.1
      intro he
      exact x.val.property ((hx.trans he).symm ▸ c.property)
    · intro j he
      have h1 := (hd i).2.1
      have h2 := (hd j).1
      rw [he] at h1
      omega
  · intro x
    by_cases hxa : x = a
    · exact Or.inl hxa
    · right
      have hxc : x.val.val ≠ c.val := by
        intro he
        exact x.val.property (he.symm ▸ c.property)
      by_cases hx2 : 2 ≤ G.degree x.val.val
      · have hax := ((hshort x hxa).2 hx2).symm
        let i : Y := ⟨x.val.val, (hY x.val.val).mpr ⟨hxc, hax⟩⟩
        exact ⟨i, Or.inl rfl⟩
      · have hx1 : G.degree x.val.val = 1 := by
          have hpos := unicyclic_positive_degree G b hG x.val.val
          omega
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
        have hqa : q ≠ a := by
          intro he
          have hv : j = a.val.val := congrArg (fun v : C.supp => v.val.val) he
          exact hnoleaf x.val.val (hv ▸ hxj.symm) hx1
        have haj : G.Adj a.val.val j := ((hshort q hqa).2 hj2).symm
        have hjc : j ≠ c.val := by
          intro he
          exact hjout (he.symm ▸ c.property)
        let i : Y := ⟨j, (hY j).mpr ⟨hjc, haj⟩⟩
        refine ⟨i, Or.inr ?_⟩
        have hsplit := ((hd i).2.2.2.2.1 x.val.val).mp hxj.symm
        apply hsplit.resolve_left
        intro he
        exact hxa (Subtype.ext (Subtype.ext he))
  · intro z
    constructor
    · intro haz
      by_cases hzc : z = c.val
      · exact Or.inl hzc
      · exact Or.inr ⟨⟨z, (hY z).mpr ⟨hzc, haz⟩⟩, rfl⟩
    · rintro (rfl | ⟨i, rfl⟩)
      · exact hac
      · exact ((hY i.val).mp i.property).2
  · intro i
    exact (hd i).2.2.2.2.1
  · intro i
    exact (hd i).2.2.2.2.2
#print axioms Paper7IntroAttachmentShape.intro21_even_actual_attachment_subdivided_star

end Paper7IntroAttachmentShape
