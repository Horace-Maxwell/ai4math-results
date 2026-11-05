import Research.Backfill.Paper7.DihedralReindex
import Research.Backfill.Paper7.SunIsoRoots

set_option autoImplicit false

noncomputable section

namespace Paper7Setup

open SimpleGraph BackfillPaper7.Challenge
open scoped Classical

theorem cycle_aut_mapped_edges (n : ℕ)
    (e : cycleGraph (n + 3) ≃g cycleGraph (n + 3)) :
    ((cycleGraph.cycle n).map e.toHom).edges.toFinset =
      (cycleGraph.cycle n).edges.toFinset := by
  apply Paper7Cycles.cycle_edgeFinset_eq_of_subset
    (cycleGraph.isCycle_cycle.map e.injective) cycleGraph.isCycle_cycle
  intro x hx
  induction x using Sym2.inductionOn with
  | hf i j =>
    have hadj : (cycleGraph (n + 3)).Adj i j :=
      ((cycleGraph.cycle n).map e.toHom).adj_of_mem_edges (List.mem_toFinset.mp hx)
    exact List.mem_toFinset.mpr (Paper7SunMoments.cycleGraph_adj_mem_cycle_edges n i j hadj)

#print axioms Paper7Setup.cycle_aut_mapped_edges

/-- Agreement on a vertex and one neighbor determines an automorphism of the
entire cycle, including the triangle. -/
theorem cycle_aut_ext_zero_last (n : ℕ)
    (e f : cycleGraph (n + 3) ≃g cycleGraph (n + 3))
    (h0 : e 0 = f 0) (hlast : e (Fin.last (n + 2)) = f (Fin.last (n + 2))) :
    ∀ k, e k = f k := by
  let c := cycleGraph.cycle n
  let p := c.map e.toHom
  let q := (c.map f.toHom).copy h0.symm h0.symm
  have hc : c.IsCycle := cycleGraph.isCycle_cycle
  have hp : p.IsCycle := hc.map e.injective
  have hq : q.IsCycle := by
    exact (Walk.isCycle_copy (c.map f.toHom) h0.symm).mpr (hc.map f.injective)
  have hedge : p.edges.toFinset = q.edges.toFinset := by
    simp only [p, q, Walk.edges_copy]
    exact (cycle_aut_mapped_edges n e).trans (cycle_aut_mapped_edges n f).symm
  have hsnd : c.snd = Fin.last (n + 2) := by
    simp only [c, cycleGraph.cycle, Walk.snd_cons]
  have hs : p.snd = q.snd := by
    change p.getVert 1 = q.getVert 1
    simp only [p, q, Walk.getVert_copy, Walk.getVert_map]
    change e c.snd = f c.snd
    rw [hsnd]
    exact hlast
  have hpq : p = q := Paper7Cycles.cycle_eq_of_edgeFinset_snd hp hq hedge hs
  have hh : c.IsHamiltonianCycle :=
    Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hc, by simp [c]⟩
  intro k
  obtain ⟨i, hi, _hil⟩ := Walk.mem_support_iff_exists_getVert.mp (hh.mem_support k)
  have h := congrArg (fun w : (cycleGraph (n + 3)).Walk (e 0) (e 0) => w.getVert i) hpq
  simpa only [p, q, Walk.getVert_copy, Walk.getVert_map, hi] using! h

#print axioms Paper7Setup.cycle_aut_ext_zero_last

/-- Every actual automorphism of the base circle satisfies the exact frozen
natural-number IsDihedral predicate. -/
theorem cycle_iso_isDihedral (b : ℕ) (hb : 3 ≤ b)
    (e : cycleGraph b ≃g cycleGraph b) : IsDihedral b e := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
  have hlastneg : (Fin.last (n + 2) : Fin (n + 3)) = -1 := by
    have h := congrArg (fun x : Fin (n + 3) => -x) (Fin.neg_last (n + 2))
    simpa only [neg_neg] using h
  have hadj : (cycleGraph (n + 3)).Adj (0 : Fin (n + 3)) (Fin.last (n + 2)) := by
    rw [cycleGraph_adj, hlastneg]
    exact Or.inl (by abel)
  have hn : e (Fin.last (n + 2)) ∈ (cycleGraph (n + 3)).neighborSet (e 0) :=
    e.toHom.map_adj hadj
  rw [cycleGraph_neighborSet] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  refine ⟨(e 0).val, ?_⟩
  rcases hn with hminus | hplus
  · apply Or.inl
    have he : ∀ k, e k = cycleTranslation n (e 0) k := by
      apply cycle_aut_ext_zero_last
      · change e 0 = 0 + e 0
        simp
      · change e (Fin.last (n + 2)) = Fin.last (n + 2) + e 0
        rw [hminus, hlastneg]
        abel
    intro k
    rw [he k]
    change (k + e 0).val = (k.val + (e 0).val) % (n + 3)
    exact Fin.val_add k (e 0)
  · apply Or.inr
    have he : ∀ k, e k = cycleReflection n (e 0) k := by
      apply cycle_aut_ext_zero_last
      · change e 0 = e 0 - 0
        simp
      · change e (Fin.last (n + 2)) = e 0 - Fin.last (n + 2)
        rw [hplus, hlastneg]
        abel
    intro k
    have hfin : e k + k = e 0 := by
      rw [he k]
      change (e 0 - k) + k = e 0
      exact sub_add_cancel _ _
    have hv := congrArg Fin.val hfin
    change ((e k).val + k.val) % (n + 3) = (e 0).val at hv
    exact hv.trans (Nat.mod_eq_of_lt (e 0).isLt).symm

#print axioms Paper7Setup.cycle_iso_isDihedral

end Paper7Setup
