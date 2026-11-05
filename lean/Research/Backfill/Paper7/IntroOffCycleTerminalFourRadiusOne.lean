import Research.Backfill.Paper7.IntroTerminalFourRemoteFan
import Research.Backfill.Paper7.IntroTerminalFourParentOrder
import Research.Backfill.Paper7.IntroOffCycleNonleafDepth
import Research.Backfill.Paper7.IntroEvenRadiusFourExclusion

/-! The remote-fan obstruction is connected to an actual outside component.
A degree-four terminal forces every other nonleaf in that component to be
adjacent to its attachment. The needed Perron-three count is derived from
the original even integral order bound and the actual degree-four vertex. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroTerminalFourRemote
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroFour Paper7IntroEven Paper7IntroTreeDepth Paper7IntroLocalQuartic
open Paper7IntroTerminalExistence Paper7UnicyclicAttachment Paper7IntroTerminalFourParent

theorem intro21_even_degree_four_count_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (x : V) (hx : G.degree x = 4) : (integerSpectrum G).count 3 = 1 := by
  obtain ⟨R, hR, htop, hbound⟩ := intro21_perron_integer_data G b hG hI hn
  rcases hR with rfl | rfl | rfl
  · have hcap : ∀ t ∈ spec G, t ≤ (2 : ℝ) := by
      intro t ht
      rw [← integerSpectrum_cast G hI] at ht
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ht
      have h := (le_abs_self z).trans (hbound z hz)
      exact_mod_cast h
    have hd := unicyclic_degree_lt_spectral_bound_sq G b hG 2 (by norm_num) hcap x
    norm_num [hx] at hd
  · exact htop
  · exact (intro21_even_no_top_four G b hG hI hn hb htop).elim
#print axioms Paper7IntroTerminalFourRemote.intro21_even_degree_four_count_three

theorem intro21_even_attachment_terminal_four_no_remote_fan
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x y z : C.supp) (hxa : G.Adj x.val.val a.val.val) (hx : G.degree x.val.val = 4)
    (hxleaf : ∀ j, G.Adj x.val.val j → j ≠ a.val.val → G.degree j = 1)
    (hay : G.Adj a.val.val y.val.val) (hyx : y.val.val ≠ x.val.val)
    (hyz : G.Adj y.val.val z.val.val) (hza : z ≠ a) (hz : 2 ≤ G.degree z.val.val)
    (hzleaf : ∀ j, G.Adj z.val.val j → j ≠ y.val.val → G.degree j = 1) : False := by
  have hbound := intro21_even_component_degree_four_only_next_to_attachment
    G b hG hI hn hb r w hw hlen C a c hac
  have hya : y ≠ a := by
    intro he
    have hyv := congrArg (fun t : C.supp => t.val.val) he
    exact hay.ne hyv.symm
  have hzaV : z.val.val ≠ a.val.val := by
    intro he
    exact hza (Subtype.ext (Subtype.ext he))
  have ha4 := intro21_degree_four_terminal_off_cycle_parent_le_four
    G b hG hI hn r w hw hlen x.val.val a.val.val a.val.property hxa hx hxleaf
  have hy4 := (hbound y hya).1
  have hz4 := (hbound z hza).1
  have habridge : ∀ j, G.Adj a.val.val j → G.IsBridge s(a.val.val, j) := by
    intro j haj
    exact unicyclic_off_cycle_edge_isBridge G b hG r w hw hlen a.val.val j a.val.property haj
  have hybridge : ∀ j, G.Adj y.val.val j → G.IsBridge s(y.val.val, j) := by
    intro j hyj
    exact unicyclic_off_cycle_edge_isBridge G b hG r w hw hlen y.val.val j y.val.property hyj
  have hsum := integral_terminal_four_remote_fan_degree_sum G hI
    (intro21_even_spectrum_abs_le_three G b hG hI hn hb)
    x.val.val a.val.val y.val.val z.val.val hxa hx hxleaf hay hyx hyz hzaV hz hzleaf
    habridge hybridge
  omega
#print axioms Paper7IntroTerminalFourRemote.intro21_even_attachment_terminal_four_no_remote_fan

private theorem outside_component_neighbor_ncard_eq
    {V : Type} (G : SimpleGraph V) (S : Set V)
    (C : (deleteVertices G S).ConnectedComponent) (a x : C.supp)
    (hgate : ∀ (v : {q : V // q ∉ S}), v ∈ C.supp →
      ∀ t : S, G.Adj v.val t.val → v = a.val)
    (hxa : x ≠ a) :
    (C.toSimpleGraph.neighborSet x).ncard = (G.neighborSet x.val.val).ncard := by
  have hxs (j : V) (hxj : G.Adj x.val.val j) : j ∉ S := by
    intro hjS
    exact hxa (Subtype.ext (hgate x.val x.property ⟨j, hjS⟩ hxj))
  let e : C.toSimpleGraph.neighborSet x ≃ G.neighborSet x.val.val :=
    { toFun := fun y => ⟨y.val.val.val, y.property⟩
      invFun := fun y => by
        let y' : {q : V // q ∉ S} := ⟨y.val, hxs y.val y.property⟩
        have hyC : y' ∈ C.supp := C.mem_supp_of_adj_mem_supp x.property y.property
        exact ⟨⟨y', hyC⟩, y.property⟩
      left_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        rfl }
  exact Set.ncard_congr' e

private theorem outside_component_terminal_leaf_transfer
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (C : (deleteVertices G S).ConnectedComponent)
    [Fintype C.supp] [DecidableEq C.supp] [DecidableRel C.toSimpleGraph.Adj]
    (a : C.supp)
    (hgate : ∀ (v : {q : V // q ∉ S}), v ∈ C.supp →
      ∀ t : S, G.Adj v.val t.val → v = a.val)
    (z y : C.supp) (hza : z ≠ a)
    (hleaf : ∀ j, C.toSimpleGraph.Adj z j → j ≠ y →
      C.toSimpleGraph.degree j = 1 ∧ j ≠ a) :
    ∀ j, G.Adj z.val.val j → j ≠ y.val.val → G.degree j = 1 := by
  intro j hzj hjy
  have hjS : j ∉ S := by
    intro hjS
    exact hza (Subtype.ext (hgate z.val z.property ⟨j, hjS⟩ hzj))
  let j' : {q : V // q ∉ S} := ⟨j, hjS⟩
  have hjC : j' ∈ C.supp := C.mem_supp_of_adj_mem_supp z.property hzj
  let t : C.supp := ⟨j', hjC⟩
  have hty : t ≠ y := by
    intro he
    exact hjy (congrArg (fun v : C.supp => v.val.val) he)
  obtain ⟨htdeg, hta⟩ := hleaf t hzj hty
  have hd : C.toSimpleGraph.degree t = G.degree t.val.val := by
    rw [← C.toSimpleGraph.ncard_neighborSet t, ← G.ncard_neighborSet t.val.val]
    exact outside_component_neighbor_ncard_eq G S C a t hgate hta
  exact hd ▸ htdeg

private theorem tree_nonleaf_adjacent_of_terminal_obstruction
    {V U : Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph U) [DecidableRel T.Adj] (hT : T.IsTree)
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (hthree : (integerSpectrum G).count 3 = 1)
    (f : U → V) (hf : Function.Injective f) (a x : U)
    (hxleaf : ∀ j, G.Adj (f x) j → j ≠ f a → G.degree j = 1)
    (hadj : ∀ i j, T.Adj i j ↔ G.Adj (f i) (f j))
    (hdegree : ∀ v, v ≠ a → T.degree v = G.degree (f v))
    (hbound : ∀ v, v ≠ a → G.degree (f v) ≤ 4 ∧
      (4 ≤ G.degree (f v) → T.Adj v a))
    (hleaf : ∀ z y, z ≠ a →
      (∀ j, T.Adj z j → j ≠ y → T.degree j = 1 ∧ j ≠ a) →
      ∀ j, G.Adj (f z) j → j ≠ f y → G.degree j = 1)
    (hremote : ∀ y z, T.Adj a y → y ≠ x → T.Adj y z → z ≠ a →
      2 ≤ G.degree (f z) →
      (∀ j, G.Adj (f z) j → j ≠ f y → G.degree j = 1) → False) :
    ∀ u, u ≠ a → 2 ≤ G.degree (f u) → T.Adj u a := by
  intro u hua hu
  by_contra hno
  have hdu : 1 < T.dist a u :=
    hT.connected.one_lt_dist_of_ne_of_not_adj hua.symm (fun hau => hno hau.symm)
  obtain ⟨z, y, hza, hzT, hzy, hzleafT, hmax⟩ :=
    rooted_tree_farthest_terminal_nonleaf T hT a ⟨u, hua, (hdegree u hua).symm ▸ hu⟩
  have hmaxu := hmax u hua ((hdegree u hua).symm ▸ hu)
  have hdz : 1 < T.dist a z := by omega
  have hznot : ¬ T.Adj z a := by
    intro hzaT
    have he : T.dist a z = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hzaT.symm
    omega
  have hzG : 2 ≤ G.degree (f z) := (hdegree z hza) ▸ hzT
  have hz3 : G.degree (f z) ≤ 3 := by
    by_contra h
    exact hznot ((hbound z hza).2 (by omega))
  have hzleafG := hleaf z y hza hzleafT
  have hy4 := (integral_radius_three_small_terminal_fan_degree_two
    G hG hI hthree (f z) (f y) ((hadj z y).mp hzy) hzG hz3 hzleafG).2
  have hya : y ≠ a := by
    intro he
    exact hznot (he ▸ hzy)
  have hay : T.Adj a y := ((hbound y hya).2 hy4).symm
  have hyx : y ≠ x := by
    intro he
    have hxz : G.Adj (f x) (f z) := (hadj x z).mp (he ▸ hzy.symm)
    have hzaV : f z ≠ f a := fun hez => hza (hf hez)
    have hd1 := hxleaf (f z) hxz hzaV
    omega
  exact hremote y z hay hyx hzy.symm hza hzG hzleafG

private theorem outside_component_nonleaf_radius_one
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (hthree : (integerSpectrum G).count 3 = 1)
    (S : Set V) (hforest : (deleteVertices G S).IsAcyclic)
    (C : (deleteVertices G S).ConnectedComponent)
    [Fintype C.supp] [DecidableEq C.supp] [DecidableRel C.toSimpleGraph.Adj]
    (a x : C.supp)
    (hxleaf : ∀ j, G.Adj x.val.val j → j ≠ a.val.val → G.degree j = 1)
    (hgate : ∀ (v : {q : V // q ∉ S}), v ∈ C.supp →
      ∀ t : S, G.Adj v.val t.val → v = a.val)
    (hbound : ∀ v : C.supp, v ≠ a → G.degree v.val.val ≤ 4 ∧
      (4 ≤ G.degree v.val.val → G.Adj v.val.val a.val.val))
    (hremote : ∀ y z : C.supp, G.Adj a.val.val y.val.val → y.val.val ≠ x.val.val →
      G.Adj y.val.val z.val.val → z ≠ a → 2 ≤ G.degree z.val.val →
      (∀ j, G.Adj z.val.val j → j ≠ y.val.val → G.degree j = 1) → False) :
    ∀ u : C.supp, u ≠ a → 2 ≤ G.degree u.val.val → G.Adj u.val.val a.val.val := by
  have hd (v : C.supp) (hva : v ≠ a) : C.toSimpleGraph.degree v = G.degree v.val.val := by
    rw [← C.toSimpleGraph.ncard_neighborSet v, ← G.ncard_neighborSet v.val.val]
    exact outside_component_neighbor_ncard_eq G S C a v hgate hva
  have hT : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph,
      Paper7UnicyclicComponentPaths.connected_component_isAcyclic (deleteVertices G S) hforest C⟩
  have hf : Function.Injective (fun v : C.supp => v.val.val) := by
    intro u v huv
    exact Subtype.ext (Subtype.ext huv)
  have hadj : ∀ i j : C.supp, C.toSimpleGraph.Adj i j ↔ G.Adj i.val.val j.val.val :=
    fun _ _ => Iff.rfl
  have hremoteT : ∀ y z : C.supp, C.toSimpleGraph.Adj a y → y ≠ x →
      C.toSimpleGraph.Adj y z → z ≠ a → 2 ≤ G.degree z.val.val →
      (∀ j, G.Adj z.val.val j → j ≠ y.val.val → G.degree j = 1) → False := by
    intro y z hay hyx hyz hza hz hzleaf
    have hyxV : y.val.val ≠ x.val.val := fun he => hyx (hf he)
    exact hremote y z hay hyxV hyz hza hz hzleaf
  exact tree_nonleaf_adjacent_of_terminal_obstruction G C.toSimpleGraph hT hG hI hthree
    (fun v : C.supp => v.val.val) hf a x hxleaf hadj hd hbound
    (outside_component_terminal_leaf_transfer G S C a hgate) hremoteT

theorem intro21_even_attachment_terminal_four_all_nonleaves_adjacent
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x : C.supp) (hxa : G.Adj x.val.val a.val.val) (hx : G.degree x.val.val = 4)
    (hxleaf : ∀ j, G.Adj x.val.val j → j ≠ a.val.val → G.degree j = 1) :
    ∀ u : C.supp, u ≠ a → 2 ≤ G.degree u.val.val → G.Adj u.val.val a.val.val := by
  have hthree := intro21_even_degree_four_count_three G b hG hI hn hb x.val.val hx
  have hbound := intro21_even_component_degree_four_only_next_to_attachment
    G b hG hI hn hb r w hw hlen C a c hac
  obtain ⟨_pair, _hpair, huniq⟩ :=
    unicyclic_component_attachment_endpoints G b hG r w hw hlen C
  have hgate : ∀ (y : {q : V // q ∉ w.support}), y ∈ C.supp →
      ∀ z : {q : V // q ∈ w.support}, G.Adj y.val z.val → y = a.val := by
    intro y hy z hyz
    have hyA := huniq (y, z) ⟨hy, hyz⟩
    have haA := huniq (a.val, c) ⟨a.property, hac⟩
    exact congrArg Prod.fst (hyA.trans haA.symm)
  have hremote : ∀ y z : C.supp, G.Adj a.val.val y.val.val → y.val.val ≠ x.val.val →
      G.Adj y.val.val z.val.val → z ≠ a → 2 ≤ G.degree z.val.val →
      (∀ j, G.Adj z.val.val j → j ≠ y.val.val → G.degree j = 1) → False := by
    exact fun y z hay hyx hyz hza hz hzleaf =>
      intro21_even_attachment_terminal_four_no_remote_fan G b hG hI hn hb
        r w hw hlen C a c hac x y z hxa hx hxleaf hay hyx hyz hza hz hzleaf
  exact outside_component_nonleaf_radius_one G hG.1 hI hthree {q | q ∈ w.support}
    (Paper7UnicyclicStructure.unicyclic_off_cycle_isAcyclic G b hG r w hw hlen)
    C a x hxleaf hgate hbound hremote
#print axioms Paper7IntroTerminalFourRemote.intro21_even_attachment_terminal_four_all_nonleaves_adjacent

end Paper7IntroTerminalFourRemote
