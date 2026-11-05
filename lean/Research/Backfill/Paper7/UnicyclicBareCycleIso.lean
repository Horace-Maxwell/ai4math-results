import Research.Backfill.Paper7.UnicyclicCardinality
import Research.Backfill.Paper7.CycleFirstDart
import Research.Backfill.Paper7.SunEdgeCount
import Research.Backfill.Paper7.SunGraphAdjacency

/-! Source-only zero-attachment branch for the original arbitrary finite
unicyclic predicate. An actual cycle covering the vertices gives a genuine
graph isomorphism to cycleGraph b and then to the empty-arm sunGraph.
No integrality, order bound, or pre-existing Sun representation is assumed.
The general nonempty off-cycle path-decomposition bridge remains separate. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicStructure
open SimpleGraph BackfillPaper7.Challenge

theorem closed_walk_mod_successor_adj {V : Type} {G : SimpleGraph V}
    {r : V} (w : G.Walk r r) (i : ℕ) (hi : i < w.length) :
    G.Adj (w.getVert i) (w.getVert ((i + 1) % w.length)) := by
  have ha := w.adj_getVert_succ hi
  by_cases hnext : i + 1 < w.length
  · simpa only [Nat.mod_eq_of_lt hnext] using ha
  · have hend : i + 1 = w.length := by omega
    rw [hend, Nat.mod_self, Walk.getVert_zero]
    simpa only [hend, Walk.getVert_length] using ha
#print axioms Paper7UnicyclicStructure.closed_walk_mod_successor_adj

theorem cycle_walk_vertex_injective {V : Type} {G : SimpleGraph V}
    {r : V} (w : G.Walk r r) (hw : w.IsCycle) (b : ℕ) (hlen : w.length = b) :
    Function.Injective (fun i : Fin b => w.getVert i.val) := by
  intro i j hij
  apply Fin.ext
  apply hw.getVert_injOn' (show i.val ≤ w.length - 1 from by
    have hi := i.isLt
    omega) (show j.val ≤ w.length - 1 from by
      have hj := j.isLt
      omega)
  exact hij
#print axioms Paper7UnicyclicStructure.cycle_walk_vertex_injective

theorem cycle_walk_vertex_surjective {V : Type} {G : SimpleGraph V}
    {r : V} (w : G.Walk r r) (hw : w.IsCycle) (b : ℕ) (hlen : w.length = b)
    (hcover : ∀ v : V, v ∈ w.support) :
    Function.Surjective (fun i : Fin b => w.getVert i.val) := by
  intro v
  obtain ⟨i, hiv, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hcover v)
  by_cases hib : i < b
  · exact ⟨⟨i, hib⟩, hiv⟩
  · have hil : i = w.length := by omega
    have hbpos : 0 < b := by
      have hh := hw.three_le_length
      omega
    refine ⟨⟨0, hbpos⟩, ?_⟩
    change w.getVert 0 = v
    rw [Walk.getVert_zero]
    simpa only [hil, Walk.getVert_length] using hiv
#print axioms Paper7UnicyclicStructure.cycle_walk_vertex_surjective

theorem cycle_walk_vertex_adj {V : Type} {G : SimpleGraph V}
    {r : V} (w : G.Walk r r) (b : ℕ) (hb : 3 ≤ b) (hlen : w.length = b)
    (i j : Fin b) (hij : (cycleGraph b).Adj i j) :
    G.Adj (w.getVert i.val) (w.getVert j.val) := by
  have hroot := (Paper7Cleared.sun_cycle_adj_iff b (fun _ => []) hb i j).mpr hij
  change (Sum.inl i ≠ (Sum.inl j : SunV b (fun _ => [])) ∧
    (j.val = (i.val + 1) % b ∨ i.val = (j.val + 1) % b)) at hroot
  rcases hroot.2 with hnext | hprev
  · have ha := closed_walk_mod_successor_adj w i.val (by
      simpa only [hlen] using i.isLt)
    simpa only [hlen, ← hnext] using ha
  · have ha := closed_walk_mod_successor_adj w j.val (by
      simpa only [hlen] using j.isLt)
    have hrev : G.Adj (w.getVert j.val) (w.getVert i.val) := by
      simpa only [hlen, ← hprev] using ha
    exact hrev.symm
#print axioms Paper7UnicyclicStructure.cycle_walk_vertex_adj

/-- A vertex equivalence that preserves edges is a graph isomorphism when
both finite graphs have the same number of edges. Keeping the graphs and
vertex equivalence as parameters isolates all edge-finset instances. -/
theorem iso_of_equiv_adj_and_edge_card {U V : Type}
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (H : SimpleGraph U) [DecidableRel H.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : U ≃ V)
    (hadj : ∀ i j : U, H.Adj i j → G.Adj (e i) (e j))
    (hcard : H.edgeFinset.card = G.edgeFinset.card) :
    Nonempty (G ≃g H) := by
  classical
  let K : SimpleGraph U := G.comap e
  have hle : H ≤ K := by
    intro i j hij
    exact hadj i j hij
  let ek : K ≃g G := SimpleGraph.Iso.comap e G
  have hcardK : H.edgeFinset.card = K.edgeFinset.card :=
    hcard.trans ek.card_edgeFinset_eq.symm
  have heq : H = K := by
    apply SimpleGraph.edgeFinset_inj.mp
    exact Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hle) hcardK.ge
  have eh : H ≃g G := by
    rw [heq]
    exact ek
  exact ⟨eh.symm⟩
#print axioms Paper7UnicyclicStructure.iso_of_equiv_adj_and_edge_card

theorem unicyclic_support_all_iso_cycle {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (r : V) (w : G.Walk r r)
    (hw : w.IsCycle) (hlen : w.length = b) (hcover : ∀ v : V, v ∈ w.support) :
    Nonempty (G ≃g cycleGraph b) := by
  classical
  have hb := Paper7Unicyclic.unicyclic_three_le hG
  let e : Fin b ≃ V := Equiv.ofBijective (fun i : Fin b => w.getVert i.val)
    ⟨cycle_walk_vertex_injective w hw b hlen,
      cycle_walk_vertex_surjective w hw b hlen hcover⟩
  apply iso_of_equiv_adj_and_edge_card (cycleGraph b) G e
  · intro i j hij
    exact cycle_walk_vertex_adj w b hb hlen i j hij
  · calc
      (cycleGraph b).edgeFinset.card = b := Paper7SunMoments.cycleGraph_edge_card b hb
      _ = Fintype.card V := by
        simpa only [Fintype.card_fin] using Fintype.card_congr e
      _ = G.edgeFinset.card := (Paper7Unicyclic.unicyclic_card_edges G hG).symm
#print axioms Paper7UnicyclicStructure.unicyclic_support_all_iso_cycle

theorem unicyclic_card_eq_cycle_iso {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hcard : Fintype.card V = b) :
    Nonempty (G ≃g cycleGraph b) := by
  obtain ⟨s, ⟨r, w, hw, hlen, _hs⟩, _huniq⟩ := hG.2
  have hsupport : w.support.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Paper7Cycles.cycle_support_card w hw, hlen, hcard]
  apply unicyclic_support_all_iso_cycle G b hG r w hw hlen
  intro v
  apply List.mem_toFinset.mp
  rw [hsupport]
  exact Finset.mem_univ v
#print axioms Paper7UnicyclicStructure.unicyclic_card_eq_cycle_iso

theorem cycleGraph_iso_empty_sun (b : ℕ) (hb : 3 ≤ b) :
    Nonempty (cycleGraph b ≃g sunGraph b (fun _ => [])) := by
  let f : Fin b → SunV b (fun _ => []) := Sum.inl
  have hf : Function.Bijective f := by
    constructor
    · exact Sum.inl_injective
    · intro v
      rcases v with i | ⟨k, j, a⟩
      · exact ⟨i, rfl⟩
      · exact Fin.elim0 j
  let e : Fin b ≃ SunV b (fun _ => []) := Equiv.ofBijective f hf
  exact ⟨{ toEquiv := e
           map_rel_iff' := fun {i j} =>
             Paper7Cleared.sun_cycle_adj_iff b (fun _ => []) hb i j }⟩
#print axioms Paper7UnicyclicStructure.cycleGraph_iso_empty_sun

theorem unicyclic_support_all_empty_sun {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (r : V) (w : G.Walk r r)
    (hw : w.IsCycle) (hlen : w.length = b) (hcover : ∀ v : V, v ∈ w.support) :
    ∃ L : Fin b → List ℕ, Nonempty (G ≃g sunGraph b L) ∧ pendantCount b L = 0 := by
  obtain ⟨e⟩ := unicyclic_support_all_iso_cycle G b hG r w hw hlen hcover
  obtain ⟨f⟩ := cycleGraph_iso_empty_sun b (Paper7Unicyclic.unicyclic_three_le hG)
  exact ⟨(fun _ => []), ⟨e.trans f⟩, by simp [pendantCount]⟩
#print axioms Paper7UnicyclicStructure.unicyclic_support_all_empty_sun

theorem unicyclic_card_eq_empty_sun {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hcard : Fintype.card V = b) :
    ∃ L : Fin b → List ℕ, Nonempty (G ≃g sunGraph b L) ∧ pendantCount b L = 0 := by
  obtain ⟨e⟩ := unicyclic_card_eq_cycle_iso G b hG hcard
  obtain ⟨f⟩ := cycleGraph_iso_empty_sun b (Paper7Unicyclic.unicyclic_three_le hG)
  exact ⟨(fun _ => []), ⟨e.trans f⟩, by simp [pendantCount]⟩
#print axioms Paper7UnicyclicStructure.unicyclic_card_eq_empty_sun

end Paper7UnicyclicStructure
