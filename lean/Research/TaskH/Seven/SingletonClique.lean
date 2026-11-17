import Research.TaskH.Seven.SingletonCycles
import Research.TaskH.LayerCycleSeparation

/-!
Three singleton neighbor colors force their actual vertices, together with
the deleted vertex, to form a clique. All following cycles come from the
same actual deleted-edge coloring, and R is used at a different deleted point.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def singletonDeletedColoring (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (j : ↥(singletonNeighborColors v c)) :
    (G.induce {x | x ≠ (singletonNeighbor v c j).val}).Coloring (Fin 7) := by
  classical
  refine SimpleGraph.Coloring.mk
    (fun z => if hz : z.val = v then j.val else c ⟨z.val, hz⟩) ?_
  intro a b hab
  have hg : G.Adj a.val b.val := hab
  by_cases ha : a.val = v
  · have hvb : G.Adj v b.val := by simpa only [ha] using hg
    have hb : b.val ≠ v := hvb.ne.symm
    simp only [dite_eq_left ha, dite_eq_right hb]
    intro he
    have hs := singletonNeighbor_eq_of_color v c j ⟨b.val, hvb⟩ he.symm
    exact b.property (congrArg Subtype.val hs)
  · by_cases hb : b.val = v
    · have hva : G.Adj v a.val := by simpa only [hb] using hg.symm
      simp only [dite_eq_right ha, dite_eq_left hb]
      intro he
      have hs := singletonNeighbor_eq_of_color v c j ⟨a.val, hva⟩ he
      exact a.property (congrArg Subtype.val hs)
    · simp only [dite_eq_right ha, dite_eq_right hb]
      exact c.valid hg

theorem singletonDeletedColoring_base (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (j : ↥(singletonNeighborColors v c)) :
    singletonDeletedColoring v c j ⟨v, (singletonNeighbor v c j).property.ne⟩ = j.val := by
  classical
  change (if h : v = v then j.val else c ⟨v, h⟩) = j.val
  exact dite_eq_left rfl

theorem singletonDeletedColoring_outside (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (j : ↥(singletonNeighborColors v c))
    (x : {z : V // z ≠ (singletonNeighbor v c j).val}) (hx : x.val ≠ v) :
    singletonDeletedColoring v c j x = c ⟨x.val, hx⟩ := by
  classical
  change (if h : x.val = v then j.val else c ⟨x.val, h⟩) = c ⟨x.val, hx⟩
  exact dite_eq_right hx

theorem singleton_cycle_contains_other_neighbor (hr : RainbowSevenCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i j : ↥(singletonNeighborColors v c)) (hij : i ≠ j)
    (π : Equiv.Perm (Fin 7)) (p : G.Walk v v) (hp : p.IsCycle) (hlen : p.length = 7)
    (hf : Follows p (fun z => π (singletonEdgeColoring v c i z)) (finRotate 7)) :
    (singletonNeighbor v c j).val ∈ p.support := by
  by_contra hjout
  have hijval : i.val ≠ j.val := fun he => hij (Subtype.ext he)
  obtain ⟨z, hzc, hzmem⟩ := singleton_cycle_visits_other_color v c i π p hlen hf j.val hijval
  have hzout : z.val ≠ (singletonNeighbor v c j).val := by
    intro he
    exact hjout (he ▸ hzmem)
  let d := singletonDeletedColoring v c j
  have he : d ⟨v, (singletonNeighbor v c j).property.ne⟩ = d ⟨z.val, hzout⟩ := by
    rw [singletonDeletedColoring_base, singletonDeletedColoring_outside v c j _ z.property]
    exact hzc.symm
  have hvz := hr (singletonNeighbor v c j).val d p hp hlen
    ⟨v, (singletonNeighbor v c j).property.ne⟩ ⟨z.val, hzout⟩ p.start_mem_support hzmem he
  exact z.property (congrArg Subtype.val hvz).symm

/-- A finite permutation sending two distinct colors to consecutive ranks. -/
theorem exists_order_zero_one (a b : Fin 7) (hab : a ≠ b) :
    ∃ π : Equiv.Perm (Fin 7), π a = 0 ∧ π b = 1 := by
  classical
  let τ : Equiv.Perm (Fin 7) := Equiv.swap a 0
  have hτa : τ a = 0 := by simp [τ]
  have hτb : τ b ≠ 0 := by
    intro he
    exact hab (τ.injective (hτa.trans he.symm))
  let π : Equiv.Perm (Fin 7) := τ.trans (Equiv.swap (τ b) 1)
  refine ⟨π, ?_, ?_⟩
  · change Equiv.swap (τ b) 1 (τ a) = 0
    rw [hτa]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hτb) (by decide)
  · change Equiv.swap (τ b) 1 (τ b) = 1
    exact Equiv.swap_apply_left _ _

omit [Fintype V] [DecidableRel G.Adj] in
theorem follows_seven_cycle_color_unique {a : V} (p : G.Walk a a)
    (c : V → Fin 7) (hf : Follows p c (finRotate 7)) (hlen : p.length = 7)
    {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) (he : c x = c y) : x = y := by
  classical
  by_contra hne
  have hrot : Follows (p.rotate x hx) c (finRotate 7) :=
    (TaskH.GoodCycles.follows_rotate_iff p x hx c (finRotate 7)).mpr hf
  have hl : (p.rotate x hx).length = 7 := by simpa only [Walk.length_rotate] using hlen
  have hn := follows_seven_cycle_avoids_same_color (p.rotate x hx) c hrot hl he.symm hne
  exact hn ((Walk.mem_support_rotate_iff p x hx).mpr hy)

theorem singleton_neighbors_adj (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (hcard : 3 ≤ (singletonNeighborColors v c).card)
    (j l : ↥(singletonNeighborColors v c)) (hjl : j ≠ l) :
    G.Adj (singletonNeighbor v c j).val (singletonNeighbor v c l).val := by
  classical
  have hsmall : ({j.val, l.val} : Finset (Fin 7)).card < (singletonNeighborColors v c).card := by
    have hp := Finset.card_insert_le j.val ({l.val} : Finset (Fin 7))
    simp only [Finset.card_singleton] at hp
    omega
  obtain ⟨i0, hi0, hiout⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  let i : ↥(singletonNeighborColors v c) := ⟨i0, hi0⟩
  have hij : i ≠ j := by
    intro he
    apply hiout
    exact Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val he))
  have hil : i ≠ l := by
    intro he
    apply hiout
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (congrArg Subtype.val he)))
  have hvals : j.val ≠ l.val := fun he => hjl (Subtype.ext he)
  obtain ⟨π, hπj, hπl⟩ := exists_order_zero_one j.val l.val hvals
  obtain ⟨p, hp, hlen, hf, _hy⟩ := singleton_through_ordered_cycle hcrit hs v c i π
  let xj := (singletonNeighbor v c j).val
  let xl := (singletonNeighbor v c l).val
  have hxj : xj ∈ p.support := singleton_cycle_contains_other_neighbor hr v c i j hij π p hp hlen hf
  have hxl : xl ∈ p.support := singleton_cycle_contains_other_neighbor hr v c i l hil π p hp hlen hf
  let q := p.rotate xj hxj
  have hqf : Follows q (fun z => π (singletonEdgeColoring v c i z)) (finRotate 7) :=
    (TaskH.GoodCycles.follows_rotate_iff p xj hxj _ (finRotate 7)).mpr hf
  have hqlen : q.length = 7 := by simpa only [q, Walk.length_rotate] using hlen
  have hjcolor : π (singletonEdgeColoring v c i xj) = 0 := by
    rw [singletonEdgeColoring_outside v c i xj (singletonNeighbor v c j).property.ne.symm]
    exact (congrArg π (singletonNeighbor_color v c j)).trans hπj
  have hlcolor : π (singletonEdgeColoring v c i xl) = 1 := by
    rw [singletonEdgeColoring_outside v c i xl (singletonNeighbor v c l).property.ne.symm]
    exact (congrArg π (singletonNeighbor_color v c l)).trans hπl
  have hnext := follows_getVert q (fun z => π (singletonEdgeColoring v c i z))
    (finRotate 7) hqf 1 (by omega)
  have hcolor : π (singletonEdgeColoring v c i (q.getVert 1)) =
      π (singletonEdgeColoring v c i xl) := by
    calc
      _ = finRotate 7 (π (singletonEdgeColoring v c i xj)) := by simpa only [pow_one] using hnext
      _ = 1 := by rw [hjcolor]; decide +kernel
      _ = _ := hlcolor.symm
  have hxlq : xl ∈ q.support := (Walk.mem_support_rotate_iff p xj hxj).mpr hxl
  have hnext_eq := follows_seven_cycle_color_unique q _ hqf hqlen
    (q.getVert_mem_support 1) hxlq hcolor
  have hadj : G.Adj xj (q.getVert 1) := by
    simpa only [Walk.getVert_zero] using q.adj_getVert_succ (i := 0) (by omega)
  change G.Adj xj xl
  rw [← hnext_eq]
  exact hadj

end TaskH.Seven

#print axioms TaskH.Seven.singletonDeletedColoring
#print axioms TaskH.Seven.singletonDeletedColoring_base
#print axioms TaskH.Seven.singletonDeletedColoring_outside
#print axioms TaskH.Seven.singleton_cycle_contains_other_neighbor
#print axioms TaskH.Seven.exists_order_zero_one
#print axioms TaskH.Seven.follows_seven_cycle_color_unique
#print axioms TaskH.Seven.singleton_neighbors_adj
