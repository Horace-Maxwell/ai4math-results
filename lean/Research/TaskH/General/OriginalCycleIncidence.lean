import Research.TaskH.General.AllCycleSingletonOriginal
import Research.TaskH.CycleIncidence

/-! Incidence lower bounds for the ACTUAL original edge-set collection.
The extra cycle is separated by its real first neighbor; the two singleton
collections are separated by actual root membership. No list of orders is counted. -/

set_option autoImplicit false
universe u
namespace TaskH.General
open SimpleGraph _root_.TaskH.Challenge
variable {k : ℕ} {V : Type u} {G : SimpleGraph V}

/-- Every real vertex lies on at least h+1 original counted cycles. -/
theorem equality_original_vertex_cycle_incidence_lower [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k) (x : V) :
    (k - 1).factorial / 2 + 1 ≤ (_root_.TaskH.modCyclesThrough k G x).ncard := by
  classical
  have hd := _root_.TaskH.critical_degree_ge hcrit x
  have hpos : 0 < (G.neighborFinset x).card := by
    rw [G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
  obtain ⟨c⟩ := _root_.TaskH.critical_colorable_deletedEdge hcrit hxy
  obtain ⟨p, hp, hlen, _, _⟩ := equality_original_edge_ordered_cycle
    hk hcrit hcount hxy c (Equiv.refl (Fin k))
  let z : V := p.snd
  have hxz : G.Adj x z := p.adj_snd hp.not_nil
  let C : Finset (Sym2 V) := p.edges.toFinset
  have hC : C ∈ _root_.TaskH.modCyclesThrough k G x := by
    refine ⟨(Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr ?_, ?_⟩
    · simpa only [hlen] using (dvd_refl k)
    · exact (_root_.TaskH.cycleContains_edges_toFinset_iff p hp.not_nil x).mpr
        p.start_mem_support
  have hCz : _root_.TaskH.CycleContains C z :=
    (_root_.TaskH.cycleContains_edges_toFinset_iff p hp.not_nil z).mpr
      (p.getVert_mem_support 1)
  let A := _root_.TaskH.modCyclesThroughAvoid k G x z
  have hA : A.Finite :=
    (Basics.modCycleEdgeSets_finite k G).subset (fun _ hm => hm.1)
  have hnot : C ∉ A := by
    intro hm
    exact hm.2.2 hCz
  have hlow : (k - 1).factorial / 2 ≤ A.ncard :=
    equality_original_edge_cycle_lower hk hcrit hcount hxz
  have hsub : insert C A ⊆ _root_.TaskH.modCyclesThrough k G x := by
    intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact hC
    · exact ⟨hs.1, hs.2.1⟩
  have hle := Set.ncard_le_ncard hsub (_root_.TaskH.modCyclesThrough_finite k G x)
  rw [Set.ncard_insert_of_notMem hnot hA] at hle
  omega

/-- A real singleton center has two disjoint h-sized actual cycle collections. -/
theorem equality_original_singleton_center_incidence_lower [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩) :
    2 * ((k - 1).factorial / 2) ≤
      (_root_.TaskH.modCyclesThrough k G a).ncard := by
  classical
  let A := _root_.TaskH.modCyclesThroughAvoid k G v b
  let B := _root_.TaskH.modCyclesThroughAvoid k G a v
  have hA : A.Finite :=
    (Basics.modCycleEdgeSets_finite k G).subset (fun _ hm => hm.1)
  have hB : B.Finite :=
    (Basics.modCycleEdgeSets_finite k G).subset (fun _ hm => hm.1)
  have hdisj : Disjoint A B := by
    refine Set.disjoint_left.mpr ?_
    intro s hs ht
    exact ht.2.2 hs.2.1
  have hsub : A ∪ B ⊆ _root_.TaskH.modCyclesThrough k G a := by
    intro s hs
    rcases hs with hs | hs
    · exact ⟨hs.1, (equality_all_edge_sets_retain_and_omit hk hcrit hcount
        hvb hva c hbunique haunique habcolor.symm s hs).1⟩
    · exact ⟨hs.1, hs.2.1⟩
  have hle := Set.ncard_le_ncard hsub (_root_.TaskH.modCyclesThrough_finite k G a)
  rw [Set.ncard_union_eq hdisj hA hB] at hle
  have hlA : (k - 1).factorial / 2 ≤ A.ncard :=
    equality_original_edge_cycle_lower hk hcrit hcount hvb
  have hlB : (k - 1).factorial / 2 ≤ B.ncard :=
    equality_original_edge_cycle_lower hk hcrit hcount hva.symm
  omega
end TaskH.General
#print axioms TaskH.General.equality_original_vertex_cycle_incidence_lower
#print axioms TaskH.General.equality_original_singleton_center_incidence_lower
