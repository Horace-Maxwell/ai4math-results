import Research.Backfill.Paper7.SchwenkPathDeletion

/-! Acyclicity kills every term of the single-vertex cofactor recurrence
except the actual next vertex of the supplied path. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicSchwenk
open SimpleGraph
open scoped BigOperators Classical

/-- In G-u, a different neighbor of u cannot reach the endpoint of the given
path. Otherwise prepending u would create two distinct simple paths. -/
theorem puncture_other_neighbor_not_reachable {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) (hp : p.IsPath) (hu : u ∉ p.support)
    (z : {x : V // x ≠ u}) (hz : G.Adj z.val u) (hzv : z.val ≠ v) :
    ¬(G.induce {x | x ≠ u}).Reachable z
      ⟨w, fun he => hu (he ▸ p.end_mem_support)⟩ := by
  intro hr
  obtain ⟨q, hq⟩ := hr.exists_isPath
  let f := (Embedding.induce (G := G) {x | x ≠ u}).toHom
  have hqmap : (q.map f).IsPath := hq.map Subtype.val_injective
  have havoid : u ∉ (q.map f).support := by
    intro hm
    rw [Walk.support_map] at hm
    obtain ⟨x, _hx, hxu⟩ := List.mem_map.mp hm
    exact x.property hxu
  have heq : Walk.cons hz.symm (q.map f) = Walk.cons h p :=
    congrArg Subtype.val ((hG.subsingleton_path u w).elim
      ⟨_, hqmap.cons havoid⟩ ⟨_, hp.cons hu⟩)
  apply hzv
  have hs := congrArg (fun q : G.Walk u w => q.snd) heq
  exact (Walk.snd_cons (q.map f) hz.symm).symm.trans
    (hs.trans (Walk.snd_cons p h))
#print axioms Paper7UnicyclicSchwenk.puncture_other_neighbor_not_reachable

/-- Remove the initial vertex of an actual simple path in an arbitrary finite
acyclic graph. The endpoint cofactor becomes the one for its induced tail. -/
theorem acyclic_adjugate_step {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) (hp : p.IsPath) (hu : u ∉ p.support) :
    (Matrix.charmatrix (G.adjMatrix ℤ)).adjugate w u =
      (Matrix.charmatrix ((G.induce {x | x ≠ u}).adjMatrix ℤ)).adjugate
        ⟨w, fun he => hu (he ▸ p.end_mem_support)⟩
        ⟨v, fun he => hu (he ▸ p.start_mem_support)⟩ := by
  let H := G.induce {x | x ≠ u}
  let a : {x : V // x ≠ u} := ⟨v, fun he => hu (he ▸ p.start_mem_support)⟩
  let b : {x : V // x ≠ u} := ⟨w, fun he => hu (he ▸ p.end_mem_support)⟩
  change (Matrix.charmatrix (G.adjMatrix ℤ)).adjugate b.val u =
    (Matrix.charmatrix (H.adjMatrix ℤ)).adjugate b a
  rw [graph_adjugate_puncture G u b, Finset.sum_eq_single a]
  · have hva : G.Adj a.val u := h.symm
    simp only [H, hva, ite_true]
  · intro z _hz hza
    by_cases hz : G.Adj z.val u
    · rw [ite_eq_left hz]
      apply graph_adjugate_zero_of_not_reachable H z b
      apply puncture_other_neighbor_not_reachable G hG h p hp hu z hz
      intro hzv
      exact hza (Subtype.ext hzv)
    · exact ite_eq_right hz
  · intro ha
    exact (ha (Finset.mem_univ a)).elim
#print axioms Paper7UnicyclicSchwenk.acyclic_adjugate_step

end Paper7UnicyclicSchwenk
