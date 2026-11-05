import Research.Backfill.Paper7.ChallengeV3

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper7Cleared

open BackfillPaper7.Challenge

theorem sun_cycle_adj_iff (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (i j : Fin b) :
    (sunGraph b L).Adj (Sum.inl i) (Sum.inl j) ↔ (SimpleGraph.cycleGraph b).Adj i j := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 2 := ⟨b - 2, by omega⟩
  have hsuc (u v : Fin (n + 2)) :
      v.val = (u.val + 1) % (n + 2) ↔ v = u + 1 := by
    rw [Fin.ext_iff, Fin.val_add, Fin.val_one]
  have hc : (SimpleGraph.cycleGraph (n + 2)).Adj i j ↔
      j.val = (i.val + 1) % (n + 2) ∨ i.val = (j.val + 1) % (n + 2) := by
    rw [SimpleGraph.cycleGraph_adj, sub_eq_iff_eq_add', sub_eq_iff_eq_add',
      hsuc, hsuc]
    exact or_comm
  change (Sum.inl i ≠ (Sum.inl j : SunV (n + 2) L) ∧
    (j.val = (i.val + 1) % (n + 2) ∨ i.val = (j.val + 1) % (n + 2))) ↔ _
  constructor
  · intro h
    exact hc.mpr h.2
  · intro h
    exact ⟨fun hij => h.ne (Sum.inl.inj hij), hc.mp h⟩

#print axioms Paper7Cleared.sun_cycle_adj_iff

theorem sun_root_arm_adj_iff (b : ℕ) (L : Fin b → List ℕ) (i k : Fin b)
    (j : Fin (L k).length) (a : Fin ((L k).get j)) :
    (sunGraph b L).Adj (Sum.inl i) (Sum.inr ⟨k, j, a⟩) ↔ k = i ∧ a.val = 0 := by
  simp [sunGraph, SimpleGraph.fromRel_adj, sunRel]

#print axioms Paper7Cleared.sun_root_arm_adj_iff

theorem sun_arm_root_adj_iff (b : ℕ) (L : Fin b → List ℕ) (i k : Fin b)
    (j : Fin (L k).length) (a : Fin ((L k).get j)) :
    (sunGraph b L).Adj (Sum.inr ⟨k, j, a⟩) (Sum.inl i) ↔ k = i ∧ a.val = 0 := by
  rw [(sunGraph b L).adj_comm]
  exact sun_root_arm_adj_iff b L i k j a

#print axioms Paper7Cleared.sun_arm_root_adj_iff

theorem sun_arm_adj_iff (b : ℕ) (L : Fin b → List ℕ) (k k' : Fin b)
    (j : Fin (L k).length) (j' : Fin (L k').length)
    (a : Fin ((L k).get j)) (a' : Fin ((L k').get j')) :
    (sunGraph b L).Adj (Sum.inr ⟨k, j, a⟩) (Sum.inr ⟨k', j', a'⟩) ↔
      k = k' ∧ j.val = j'.val ∧ (a.val + 1 = a'.val ∨ a'.val + 1 = a.val) := by
  change (Sum.inr ⟨k, j, a⟩ ≠ (Sum.inr ⟨k', j', a'⟩ : SunV b L) ∧
    ((k = k' ∧ j.val = j'.val ∧ a'.val = a.val + 1) ∨
      (k' = k ∧ j'.val = j.val ∧ a.val = a'.val + 1))) ↔ _
  constructor
  · rintro ⟨_hne, h | h⟩
    · exact ⟨h.1, h.2.1, Or.inl h.2.2.symm⟩
    · exact ⟨h.1.symm, h.2.1.symm, Or.inr h.2.2.symm⟩
  · rintro ⟨hk, hj, ha⟩
    refine ⟨?_, ?_⟩
    · intro hv
      have hpos := congrArg (fun v : SunV b L =>
        match v with
        | Sum.inl _ => 0
        | Sum.inr z => z.2.2.val) hv
      change a.val = a'.val at hpos
      omega
    · rcases ha with h | h
      · exact Or.inl ⟨hk, hj, h.symm⟩
      · exact Or.inr ⟨hk.symm, hj.symm, h.symm⟩

#print axioms Paper7Cleared.sun_arm_adj_iff

theorem sun_same_arm_vertex_eq_iff (b : ℕ) (L : Fin b → List ℕ) (k : Fin b)
    (j : Fin (L k).length) (a a' : Fin ((L k).get j)) :
    (Sum.inr ⟨k, j, a⟩ : SunV b L) = Sum.inr ⟨k, j, a'⟩ ↔ a = a' := by
  constructor
  · intro h
    apply Fin.ext
    exact congrArg (fun v : SunV b L =>
      match v with
      | Sum.inl _ => 0
      | Sum.inr z => z.2.2.val) h
  · rintro rfl
    rfl

#print axioms Paper7Cleared.sun_same_arm_vertex_eq_iff

end Paper7Cleared
