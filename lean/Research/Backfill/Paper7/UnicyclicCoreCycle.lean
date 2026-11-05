import Research.Backfill.Paper7.UnicyclicBareCycleIso

/-! The direct import is a sealed uncompiled candidate. Restrict the actual
cycle to its support and inherit unique-cycle data through the subtype
embedding. This supplies the missing full core cycle isomorphism. -/
set_option autoImplicit false
noncomputable section
namespace Paper7SunAssembly
open SimpleGraph BackfillPaper7.Challenge
open scoped Classical

theorem unicyclic_core_iso_cycle {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (r : V) (w : G.Walk r r)
    (hw : w.IsCycle) (hlen : w.length = b) :
    Nonempty (cycleGraph b ≃g G.induce {v | v ∈ w.support}) := by
  let S : Set V := {v | v ∈ w.support}
  let K := G.induce S
  let a : S := ⟨r, w.start_mem_support⟩
  let q : K.Walk a a := w.induce S (fun _ h => h)
  let f : K ↪g G := SimpleGraph.Embedding.induce S
  have hmap : q.map f.toHom = w := Walk.map_induce w _
  have hq : q.IsCycle := Walk.IsCycle.of_map (hmap.symm ▸ hw)
  have hqlen : q.length = b := by
    exact (Walk.length_map f.toHom q).symm.trans
      ((congrArg (fun z : G.Walk r r => z.length) hmap).trans hlen)
  have hcover : ∀ v : S, v ∈ q.support := by
    intro v
    have hv : v.val ∈ (q.map f.toHom).support := hmap.symm ▸ v.property
    rw [Walk.support_map, List.mem_map] at hv
    obtain ⟨u, hu, huv⟩ := hv
    have he : u = v := Subtype.ext huv
    exact he ▸ hu
  have hK : IsUnicyclicWithCycle K b := by
    refine ⟨w.connected_induce_support, q.edges.toFinset, ⟨a, q, hq, hqlen, rfl⟩, ?_⟩
    intro ell t ht
    obtain ⟨u, p, hp, _hpl, rfl⟩ := ht
    obtain ⟨s, _hs, huniq⟩ := Paper7Unicyclic.unicyclic_cycle_unique_data hG
    have hpmap : (p.map f.toHom).IsCycle := hp.map f.injective
    have hqmap : (q.map f.toHom).IsCycle := hq.map f.injective
    have he : (p.map f.toHom).edges.toFinset = (q.map f.toHom).edges.toFinset :=
      ((huniq _ _ ⟨_, _, hpmap, rfl, rfl⟩).2).trans
        ((huniq _ _ ⟨_, _, hqmap, rfl, rfl⟩).2).symm
    apply Finset.ext
    intro d
    constructor
    · intro hd
      have hd' : Sym2.map f d ∈ (p.map f.toHom).edges.toFinset := by
        simp only [Walk.edges_map, List.mem_toFinset, List.mem_map]
        exact ⟨d, List.mem_toFinset.mp hd, rfl⟩
      rw [he] at hd'
      simp only [Walk.edges_map, List.mem_toFinset, List.mem_map] at hd'
      obtain ⟨d', hd', hdeq⟩ := hd'
      have hdd : d' = d := Sym2.map.injective f.injective hdeq
      exact List.mem_toFinset.mpr (hdd ▸ hd')
    · intro hd
      have hd' : Sym2.map f d ∈ (q.map f.toHom).edges.toFinset := by
        simp only [Walk.edges_map, List.mem_toFinset, List.mem_map]
        exact ⟨d, List.mem_toFinset.mp hd, rfl⟩
      rw [← he] at hd'
      simp only [Walk.edges_map, List.mem_toFinset, List.mem_map] at hd'
      obtain ⟨d', hd', hdeq⟩ := hd'
      have hdd : d' = d := Sym2.map.injective f.injective hdeq
      exact List.mem_toFinset.mpr (hdd ▸ hd')
  obtain ⟨e⟩ := Paper7UnicyclicStructure.unicyclic_support_all_iso_cycle
    K b hK a q hq hqlen hcover
  exact ⟨e.symm⟩
#print axioms Paper7SunAssembly.unicyclic_core_iso_cycle

end Paper7SunAssembly
