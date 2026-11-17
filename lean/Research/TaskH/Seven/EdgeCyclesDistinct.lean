import Research.TaskH.Seven.EdgeCycles

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- Rank orders admitting a genuine based seven-cycle with this actual edge set. -/
noncomputable def basedCycleOrders (c : V → Fin 7) (x : V) (s : Finset (Sym2 V)) :
    Finset (Equiv.Perm (Fin 7)) := by
  classical
  exact Finset.univ.filter (fun π => ∃ p : G.Walk x x, p.IsCycle ∧ p.length = 7 ∧
    p.edgeSet = (s : Set (Sym2 V)) ∧ Follows p (fun z => π (c z)) (finRotate 7))

theorem mem_basedCycleOrders (c : V → Fin 7) (x : V) (s : Finset (Sym2 V))
    (π : Equiv.Perm (Fin 7)) : π ∈ basedCycleOrders (G := G) c x s ↔
      ∃ p : G.Walk x x, p.IsCycle ∧ p.length = 7 ∧
        p.edgeSet = (s : Set (Sym2 V)) ∧ Follows p (fun z => π (c z)) (finRotate 7) := by
  classical
  simp only [basedCycleOrders, Finset.mem_filter, Finset.mem_univ, true_and]

theorem basedCycleOrders_subset_traversals (c : V → Fin 7) (x : V)
    (s : Finset (Sym2 V)) (p : G.Walk x x) (hp : p.IsCycle)
    (hset : p.edgeSet = (s : Set (Sym2 V))) :
    basedCycleOrders (G := G) c x s ⊆ followingOrders p c ∪ followingOrders p.reverse c := by
  classical
  intro π hπ
  obtain ⟨q, hq, _hlen, hqs, hf⟩ := (mem_basedCycleOrders c x s π).mp hπ
  obtain hdir | hdir := CycleOrientation.cycle_eq_or_reverse hp hq (hset.trans hqs.symm)
  · apply Finset.mem_union.mpr
    left
    apply (mem_followingOrders p c π).mpr
    simpa only [hdir] using hf
  · apply Finset.mem_union.mpr
    right
    apply (mem_followingOrders p.reverse c π).mpr
    simpa only [hdir] using hf

/-- Both orientations together have at most fourteen of the 5040 rank orders. -/
theorem basedCycleOrders_card_le_fourteen (c : V → Fin 7) (x : V)
    (s : Finset (Sym2 V)) : (basedCycleOrders (G := G) c x s).card ≤ 14 := by
  classical
  by_cases hn : (basedCycleOrders (G := G) c x s).Nonempty
  · obtain ⟨π, hπ⟩ := hn
    obtain ⟨p, hp, hlen, hset, _hf⟩ := (mem_basedCycleOrders c x s π).mp hπ
    have hs := Finset.card_le_card (basedCycleOrders_subset_traversals c x s p hp hset)
    have hu := Finset.card_union_le (followingOrders p c) (followingOrders p.reverse c)
    have h1 := followingOrders_card_le_seven p hlen c
    have h2 := followingOrders_card_le_seven p.reverse
      (by simpa only [Walk.length_reverse] using hlen) c
    omega
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he]
    simp

end TaskH.Seven

#print axioms TaskH.Seven.basedCycleOrders
#print axioms TaskH.Seven.mem_basedCycleOrders
#print axioms TaskH.Seven.basedCycleOrders_subset_traversals
#print axioms TaskH.Seven.basedCycleOrders_card_le_fourteen
