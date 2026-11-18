import Research.TaskH.General.SingletonSpineBudgetOriginal
import Research.TaskH.General.SingletonFiberBoundaryOriginal

/-! Duplicate vertices in one actual root-color fiber cannot hook distinct
singleton centers. The contradiction is an actual k-cycle in the original
G, closed from the internally selected k-3-vertex spine. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_same_color_frame_impossible (hk : 5 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v p p' a b : V} (hvp : G.Adj v p) (hvp' : G.Adj v p') (hpp' : p ≠ p')
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcolor : c ⟨p, hvp.ne.symm⟩ = c ⟨p', hvp'.ne.symm⟩)
    (hpA : G.Adj p a) (hp'B : G.Adj p' b)
    (L : G.Walk a b) (hL : L.IsPath) (hLen : L.length = k - 4)
    (hvL : v ∉ L.support) (hpL : p ∉ L.support) (hp'L : p' ∉ L.support) : False := by
  let q := Walk.cons hpA L
  have hq : q.IsPath := hL.cons hpL
  have hp'q : p' ∉ q.support := by
    simpa only [q, Walk.support_cons, List.mem_cons, not_or] using And.intro hpp'.symm hp'L
  let t := q.concat hp'B.symm
  have ht : t.IsPath := hq.concat hp'q hp'B.symm
  have hvt : v ∉ t.support := by
    intro hz
    change v ∈ (q.concat hp'B.symm).support at hz
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hz
    rcases hz with hzq | he
    · change v ∈ (Walk.cons hpA L).support at hzq
      rw [Walk.support_cons, List.mem_cons] at hzq
      exact hzq.elim hvp.ne hvL
    · exact hvp'.ne he
  let r := Walk.cons hvp t
  have hr : r.IsPath := ht.cons hvt
  have hvrtail : v ∉ r.support.tail := by
    have hn : (v :: r.support.tail).Nodup := by
      rw [Walk.cons_tail_support r]
      exact hr.support_nodup
    exact (List.nodup_cons.mp hn).1
  have hd : r.support.tail.Disjoint hvp'.symm.toWalk.support.tail := by
    rw [List.disjoint_left]
    intro z hz hzc
    have he : z = v := by
      simpa only [SimpleGraph.Adj.support_toWalk, List.tail_cons, List.tail_nil,
        List.mem_singleton] using hzc
    subst z
    exact hvrtail hz
  let C := r.append hvp'.symm.toWalk
  have hrLen : r.length = L.length + 3 := by
    calc
      r.length = t.length + 1 := Walk.length_cons hvp t
      _ = (q.length + 1) + 1 :=
        congrArg (fun n : ℕ => n + 1) (Walk.length_concat q hp'B.symm)
      _ = L.length + 3 := by
        change ((L.length + 1) + 1) + 1 = L.length + 3
        omega
  have hC : C.IsCycle := hr.isCycle_append hvp'.symm.isPath_toWalk hd
    (Or.inl (by rw [hrLen]; omega))
  have hClen : C.length = k := by
    change (r.append hvp'.symm.toWalk).length = k
    rw [Walk.length_append, hrLen, SimpleGraph.Adj.length_toWalk, hLen]
    omega
  have hpC : p ∈ C.support := by
    apply (Walk.mem_support_append_iff r hvp'.symm.toWalk).mpr
    left
    have hpt : p ∈ t.support := by
      change p ∈ (q.concat hp'B.symm).support
      rw [Walk.support_concat, List.mem_append]
      exact Or.inl q.start_mem_support
    exact List.mem_cons_of_mem v hpt
  have hp'C : p' ∈ C.support :=
    (Walk.mem_support_append_iff r hvp'.symm.toWalk).mpr (Or.inl r.end_mem_support)
  exact hpp' (equality_original_cycle_support_rainbow (by omega) hcrit hcount c
    C hC hClen hpC hp'C hvp.ne.symm hvp'.ne.symm hcolor)

theorem equality_original_duplicate_fiber_hooks_agree (hk : 5 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v p p' a b : V} (hvp : G.Adj v p) (hvp' : G.Adj v p') (hpp' : p ≠ p')
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcolor : c ⟨p, hvp.ne.symm⟩ = c ⟨p', hvp'.ne.symm⟩)
    (hcard : 3 ≤ (originalSingletonCenters c).card)
    (ha : a ∈ originalSingletonCenters c) (hb : b ∈ originalSingletonCenters c)
    (hpA : G.Adj p a) (hp'B : G.Adj p' b) : a = b := by
  have hpJ : p ∉ originalSingletonCenters c := by
    intro hh
    obtain ⟨_, hu⟩ := (mem_originalSingletonCenters c).mp hh
    exact hpp' (hu p' hvp'.ne.symm hvp' hcolor.symm).symm
  have hp'J : p' ∉ originalSingletonCenters c := by
    intro hh
    obtain ⟨_, hu⟩ := (mem_originalSingletonCenters c).mp hh
    exact hpp' (hu p hvp.ne.symm hvp hcolor)
  by_contra hab
  obtain ⟨L, hL, hLen, hvL, hav⟩ := equality_original_singleton_spine_root_color_avoidance
    hk hcrit hcount c hcard ha hb hab (c ⟨p, hvp.ne.symm⟩)
  exact equality_original_same_color_frame_impossible hk hcrit hcount hvp hvp' hpp'
    c hcolor hpA hp'B L hL hLen hvL
    (hav p hvp.ne.symm rfl hpJ) (hav p' hvp'.ne.symm hcolor.symm hp'J)

end TaskH.General

#print axioms TaskH.General.equality_original_same_color_frame_impossible
#print axioms TaskH.General.equality_original_duplicate_fiber_hooks_agree
