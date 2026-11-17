import Research.TaskH.LowDegreeAvoidCount
import Research.TaskH.CliqueCompletion

/-!
Completion of the degree-four branch using actual critical colorings,
actual cycle edge sets and the original total count fifteen. The short-cycle
hypothesis is internal and must be supplied from the frozen equality case.
-/

set_option autoImplicit false

universe u

namespace TaskH

open Challenge SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

/-- The three unoriented color orders cover every pair of distinct colors. -/
theorem fourColorCycle_pair_covered (i t : Fin 4) (hne : i ≠ t) :
    ∃ j : Fin 3, fourColorCycle j i = t ∨ fourColorCycle j t = i := by
  have h : ∀ (i t : Fin 4), i ≠ t →
      ∃ j : Fin 3, fourColorCycle j i = t ∨ fourColorCycle j t = i := by decide +kernel
  exact h i t hne

/-- A four-step following closed walk has no two distinct vertices of the
same color. This is derived from the walk, rather than assumed as rainbow. -/
theorem follows_four_cycle_color_unique [DecidableEq V] {a : V}
    (p : G.Walk a a) (c : V → Fin 4) (j : Fin 3)
    (hf : Follows p c (fourColorCycle j)) (hl : p.length = 4)
    {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) (he : c x = c y) : x = y := by
  by_contra hne
  have hrot := follows_rotate_degreeFour p x hx c j hf
  have hlen : (p.rotate x hx).length = 4 := by simpa only [Walk.length_rotate] using hl
  have hyn : y ∉ (p.rotate x hx).support :=
    follows_four_cycle_avoids_same_color (p.rotate x hx) c j hrot hlen he.symm hne
  exact hyn ((Walk.mem_support_rotate_iff p x hx).mpr hy)

section FiniteGraph

variable [Fintype V] [DecidableRel G.Adj]

theorem degreeFourNeighbor_extension_color (hcrit : IsCriticalPlus 4 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) :
    deletedColorExtension v c (degreeFourNeighbor hcrit v c hdegree i).val = i := by
  rw [deletedColorExtension_outside v c _
    (degreeFourNeighbor hcrit v c hdegree i).property]
  exact degreeFourNeighbor_color hcrit v c hdegree i

theorem degreeFour_neighbor_adj_of_step (hcrit : IsCriticalPlus 4 G)
    (hs : ShortFourCycles G) (hcount : modCycleCount 4 G = 15) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i t : Fin 4) (j : Fin 3) (hstep : fourColorCycle j i = t) :
    G.Adj (degreeFourNeighbor hcrit v c hdegree i).val
      (degreeFourNeighbor hcrit v c hdegree t).val := by
  classical
  let P := degreeFourAvoidCycle hcrit hs v c hdegree 0 j
  let xi := (degreeFourNeighbor hcrit v c hdegree i).val
  let xt := (degreeFourNeighbor hcrit v c hdegree t).val
  have hxi : xi ∈ P.support :=
    degreeFourAvoidCycle_contains_neighbors hcrit hs hcount v c hdegree i j
  have hxt : xt ∈ P.support :=
    degreeFourAvoidCycle_contains_neighbors hcrit hs hcount v c hdegree t j
  let q := P.rotate xi hxi
  have hqf : Follows q (deletedColorExtension v c) (fourColorCycle j) :=
    follows_rotate_degreeFour P xi hxi (deletedColorExtension v c) j
      (degreeFourAvoidCycle_follows hcrit hs v c hdegree 0 j)
  have hql : q.length = 4 := by
    simpa only [q, Walk.length_rotate] using
      degreeFourAvoidCycle_length hcrit hs v c hdegree 0 j
  have hnext := follows_getVert q (deletedColorExtension v c) (fourColorCycle j)
    hqf 1 (by omega)
  have hcolor : deletedColorExtension v c (q.getVert 1) = deletedColorExtension v c xt := by
    calc
      deletedColorExtension v c (q.getVert 1) =
          fourColorCycle j (deletedColorExtension v c xi) := by
        simpa only [pow_one] using hnext
      _ = fourColorCycle j i := congrArg (fourColorCycle j)
        (degreeFourNeighbor_extension_color hcrit v c hdegree i)
      _ = t := hstep
      _ = deletedColorExtension v c xt :=
        (degreeFourNeighbor_extension_color hcrit v c hdegree t).symm
  have hxtq : xt ∈ q.support := (Walk.mem_support_rotate_iff P xi hxi).mpr hxt
  have hnext_eq : q.getVert 1 = xt := follows_four_cycle_color_unique q
    (deletedColorExtension v c) j hqf hql (q.getVert_mem_support 1) hxtq hcolor
  have hadj : G.Adj xi (q.getVert 1) := by
    simpa only [Walk.getVert_zero] using q.adj_getVert_succ (i := 0) (by omega)
  change G.Adj xi xt
  rw [← hnext_eq]
  exact hadj

theorem degreeFour_neighbors_adj (hcrit : IsCriticalPlus 4 G)
    (hs : ShortFourCycles G) (hcount : modCycleCount 4 G = 15) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    {a b : V} (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) : G.Adj a b := by
  let za : {x : V // x ≠ v} := ⟨a, ha.ne.symm⟩
  let zb : {x : V // x ≠ v} := ⟨b, hb.ne.symm⟩
  have hza := degreeFourNeighbor_eq_of_color hcrit v c hdegree (c za) za ha rfl
  have hzb := degreeFourNeighbor_eq_of_color hcrit v c hdegree (c zb) zb hb rfl
  have hne : c za ≠ c zb := by
    intro he
    apply hab
    rw [he] at hza
    exact congrArg Subtype.val (hza.trans hzb.symm)
  obtain ⟨j, hstep | hstep⟩ := fourColorCycle_pair_covered (c za) (c zb) hne
  · change G.Adj za.val zb.val
    rw [hza, hzb]
    exact degreeFour_neighbor_adj_of_step hcrit hs hcount v c hdegree (c za) (c zb) j hstep
  · change G.Adj za.val zb.val
    rw [hza, hzb]
    exact (degreeFour_neighbor_adj_of_step hcrit hs hcount v c hdegree
      (c zb) (c za) j hstep).symm

theorem degreeFour_closed_neighborhood_clique (hcrit : IsCriticalPlus 4 G)
    (hs : ShortFourCycles G) (hcount : modCycleCount 4 G = 15) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4) :
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
    · exact degreeFour_neighbors_adj hcrit hs hcount v c hdegree
        ((G.mem_neighborFinset v a).mp ha) ((G.mem_neighborFinset v b).mp hb) hab

/-- The requested branch interface uses only original criticality, original
count fifteen, actual degree four, and the internal short-cycle conclusion. -/
theorem degreeFour_isCompleteOfOrder (hcrit : IsCriticalPlus 4 G)
    (hs : ShortFourCycles G) (hcount : modCycleCount 4 G = 15)
    (v : V) (hv : G.degree v = 4) : IsCompleteOfOrder G 5 := by
  classical
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  apply critical_five_clique_complete hcrit (insert v (G.neighborFinset v))
    (degreeFour_closed_neighborhood_clique hcrit hs hcount v c hv)
  calc
    (insert v (G.neighborFinset v)).card = (G.neighborFinset v).card + 1 :=
      Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v)
    _ = 5 := by rw [G.card_neighborFinset_eq_degree, hv]

end FiniteGraph

end TaskH

#print axioms TaskH.fourColorCycle_pair_covered
#print axioms TaskH.follows_four_cycle_color_unique
#print axioms TaskH.degreeFour_neighbor_adj_of_step
#print axioms TaskH.degreeFour_closed_neighborhood_clique
#print axioms TaskH.degreeFour_isCompleteOfOrder
