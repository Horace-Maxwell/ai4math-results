import Research.TaskH.Five.LowDegreeAvoidCount
import Research.TaskH.Five.CliqueCompletion

/-!
Completion of the degree-five branch using actual critical colorings,
actual cycle edge sets and the original total count seventy-two. The short-cycle
hypothesis is internal and must be supplied from the frozen equality case.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open _root_.TaskH.Challenge SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

/-- The twelve unoriented color orders cover every pair of distinct colors. -/
theorem fiveColorCycle_pair_covered (i t : Fin 5) (hne : i ≠ t) :
    ∃ j : Fin 12, fiveColorCycle j i = t ∨ fiveColorCycle j t = i := by
  have h : ∀ (i t : Fin 5), i ≠ t →
      ∃ j : Fin 12, fiveColorCycle j i = t ∨ fiveColorCycle j t = i := by decide +kernel
  exact h i t hne

/-- A five-step following closed walk has no two distinct vertices of the
same color. This is derived from the walk, rather than assumed as rainbow. -/
theorem follows_five_cycle_color_unique [DecidableEq V] {a : V}
    (p : G.Walk a a) (c : V → Fin 5) (j : Fin 12)
    (hf : Follows p c (fiveColorCycle j)) (hl : p.length = 5)
    {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) (he : c x = c y) : x = y := by
  by_contra hne
  have hrot := follows_rotate_degreeFive p x hx c j hf
  have hlen : (p.rotate x hx).length = 5 := by simpa only [Walk.length_rotate] using hl
  have hyn : y ∉ (p.rotate x hx).support :=
    follows_five_cycle_avoids_same_color (p.rotate x hx) c j hrot hlen he.symm hne
  exact hyn ((Walk.mem_support_rotate_iff p x hx).mpr hy)

section FiniteGraph

variable [Fintype V] [DecidableRel G.Adj]

theorem degreeFiveNeighbor_extension_color (hcrit : IsCriticalPlus 5 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) :
    deletedColorExtension v c (degreeFiveNeighbor hcrit v c hdegree i).val = i := by
  rw [deletedColorExtension_outside v c _
    (degreeFiveNeighbor hcrit v c hdegree i).property]
  exact degreeFiveNeighbor_color hcrit v c hdegree i

theorem degreeFive_neighbor_adj_of_step (hcrit : IsCriticalPlus 5 G)
    (hs : ShortFiveCycles G) (hcount : modCycleCount 5 G = 72) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i t : Fin 5) (j : Fin 12) (hstep : fiveColorCycle j i = t) :
    G.Adj (degreeFiveNeighbor hcrit v c hdegree i).val
      (degreeFiveNeighbor hcrit v c hdegree t).val := by
  classical
  let P := degreeFiveAvoidCycle hcrit hs v c hdegree 0 j
  let xi := (degreeFiveNeighbor hcrit v c hdegree i).val
  let xt := (degreeFiveNeighbor hcrit v c hdegree t).val
  have hxi : xi ∈ P.support :=
    degreeFiveAvoidCycle_contains_neighbors hcrit hs hcount v c hdegree i j
  have hxt : xt ∈ P.support :=
    degreeFiveAvoidCycle_contains_neighbors hcrit hs hcount v c hdegree t j
  let q := P.rotate xi hxi
  have hqf : Follows q (deletedColorExtension v c) (fiveColorCycle j) :=
    follows_rotate_degreeFive P xi hxi (deletedColorExtension v c) j
      (degreeFiveAvoidCycle_follows hcrit hs v c hdegree 0 j)
  have hql : q.length = 5 := by
    simpa only [q, Walk.length_rotate] using
      degreeFiveAvoidCycle_length hcrit hs v c hdegree 0 j
  have hnext := follows_getVert q (deletedColorExtension v c) (fiveColorCycle j)
    hqf 1 (by omega)
  have hcolor : deletedColorExtension v c (q.getVert 1) = deletedColorExtension v c xt := by
    calc
      deletedColorExtension v c (q.getVert 1) =
          fiveColorCycle j (deletedColorExtension v c xi) := by
        simpa only [pow_one] using hnext
      _ = fiveColorCycle j i := congrArg (fiveColorCycle j)
        (degreeFiveNeighbor_extension_color hcrit v c hdegree i)
      _ = t := hstep
      _ = deletedColorExtension v c xt :=
        (degreeFiveNeighbor_extension_color hcrit v c hdegree t).symm
  have hxtq : xt ∈ q.support := (Walk.mem_support_rotate_iff P xi hxi).mpr hxt
  have hnext_eq : q.getVert 1 = xt := follows_five_cycle_color_unique q
    (deletedColorExtension v c) j hqf hql (q.getVert_mem_support 1) hxtq hcolor
  have hadj : G.Adj xi (q.getVert 1) := by
    simpa only [Walk.getVert_zero] using q.adj_getVert_succ (i := 0) (by omega)
  change G.Adj xi xt
  rw [← hnext_eq]
  exact hadj

theorem degreeFive_neighbors_adj (hcrit : IsCriticalPlus 5 G)
    (hs : ShortFiveCycles G) (hcount : modCycleCount 5 G = 72) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    {a b : V} (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) : G.Adj a b := by
  let za : {x : V // x ≠ v} := ⟨a, ha.ne.symm⟩
  let zb : {x : V // x ≠ v} := ⟨b, hb.ne.symm⟩
  have hza := degreeFiveNeighbor_eq_of_color hcrit v c hdegree (c za) za ha rfl
  have hzb := degreeFiveNeighbor_eq_of_color hcrit v c hdegree (c zb) zb hb rfl
  have hne : c za ≠ c zb := by
    intro he
    apply hab
    rw [he] at hza
    exact congrArg Subtype.val (hza.trans hzb.symm)
  obtain ⟨j, hstep | hstep⟩ := fiveColorCycle_pair_covered (c za) (c zb) hne
  · change G.Adj za.val zb.val
    rw [hza, hzb]
    exact degreeFive_neighbor_adj_of_step hcrit hs hcount v c hdegree (c za) (c zb) j hstep
  · change G.Adj za.val zb.val
    rw [hza, hzb]
    exact (degreeFive_neighbor_adj_of_step hcrit hs hcount v c hdegree
      (c zb) (c za) j hstep).symm

theorem degreeFive_closed_neighborhood_clique (hcrit : IsCriticalPlus 5 G)
    (hs : ShortFiveCycles G) (hcount : modCycleCount 5 G = 72) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5) :
    G.IsClique (insert v (G.neighborFinset v) : Finset V) := by
  classical
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
  rcases ha with hav | ha
  · rcases hb with hbv | hb
    · exact (hab (hav.trans hbv.symm)).elim
    · rw [hav]
      exact (G.mem_neighborFinset v b).mp hb
  · rcases hb with hbv | hb
    · rw [hbv]
      exact ((G.mem_neighborFinset v a).mp ha).symm
    · exact degreeFive_neighbors_adj hcrit hs hcount v c hdegree
        ((G.mem_neighborFinset v a).mp ha) ((G.mem_neighborFinset v b).mp hb) hab

/-- The requested branch interface uses only original criticality, original
count seventy-two, actual degree four, and the internal short-cycle conclusion. -/
theorem degreeFive_isCompleteOfOrder (hcrit : IsCriticalPlus 5 G)
    (hs : ShortFiveCycles G) (hcount : modCycleCount 5 G = 72)
    (v : V) (hv : G.degree v = 5) : IsCompleteOfOrder G 6 := by
  classical
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  apply critical_six_clique_complete hcrit (insert v (G.neighborFinset v))
    (degreeFive_closed_neighborhood_clique hcrit hs hcount v c hv)
  calc
    (insert v (G.neighborFinset v)).card = (G.neighborFinset v).card + 1 :=
      Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v)
    _ = 6 := by rw [G.card_neighborFinset_eq_degree, hv]

end FiniteGraph

end TaskH.Five

#print axioms TaskH.Five.fiveColorCycle_pair_covered
#print axioms TaskH.Five.follows_five_cycle_color_unique
#print axioms TaskH.Five.degreeFiveNeighbor_extension_color
#print axioms TaskH.Five.degreeFive_neighbor_adj_of_step
#print axioms TaskH.Five.degreeFive_neighbors_adj
#print axioms TaskH.Five.degreeFive_closed_neighborhood_clique
#print axioms TaskH.Five.degreeFive_isCompleteOfOrder
