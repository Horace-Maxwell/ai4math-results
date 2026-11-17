import Research.TaskH.Seven.EqualityShortCycles

/-! O/M gives the lower bound for the original critical graph, without
assuming any short-cycle, rainbow, or separate incidence premise. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge _root_.TaskH.Seven.GoodCycles

variable {V : Type u} {G : SimpleGraph V}

theorem critical_nonempty (hcrit : IsCriticalPlus 7 G) : Nonempty V := by
  classical
  by_contra h
  have hn : ∀ x : V, False := fun x => h ⟨x⟩
  apply TaskH.critical_not_colorable hcrit
  refine ⟨SimpleGraph.Coloring.mk (fun x => False.elim (hn x)) ?_⟩
  intro x y _hxy
  exact False.elim (hn x)

theorem critical_modCycleCount_ge_2880 [Fintype V] (hcrit : IsCriticalPlus 7 G) :
    2880 ≤ modCycleCount 7 G := by
  classical
  let v : V := Classical.choice (critical_nonempty hcrit)
  obtain ⟨c⟩ := TaskH.critical_colorable_deletedVertex hcrit v
  let A : Finset (Equiv.Perm (Fin 7)) := Finset.univ
  let C := (Basics.modCycleEdgeSets_finite 7 G).toFinset
  let R : Equiv.Perm (Fin 7) → Finset (Sym2 V) → Prop := GoodCycleOrder c
  have hA : A.card = 5040 := by norm_num [A, Fintype.card_perm]
  have hrow : ∀ π ∈ A, 8 ≤ (C.filter (R π)).card := by
    intro π _
    exact good_mod_cycles_card_ge_eight (TaskH.critical_not_colorable hcrit) c π
  have hcol : ∀ s ∈ C, (A.filter (fun π => R π s)).card ≤ 14 := by
    intro s _
    exact goodCycleOrders_card_le_fourteen c s
  have hdouble : (∑ π ∈ A, (C.filter (R π)).card) =
      ∑ s ∈ C, (A.filter (fun π => R π s)).card := by
    exact FiniteBudget.relation_double_count A C R
  have hlow : 8 * A.card ≤ ∑ π ∈ A, (C.filter (R π)).card := by
    calc
      8 * A.card = ∑ _π ∈ A, 8 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hrow
  have hhigh : (∑ s ∈ C, (A.filter (fun π => R π s)).card) ≤ C.card * 14 := by
    calc
      _ ≤ ∑ _s ∈ C, 14 := Finset.sum_le_sum hcol
      _ = C.card * 14 := by simp
  have hC : C.card = modCycleCount 7 G := by
    dsimp only [C]
    rw [modCycleCount, Set.ncard_eq_toFinset_card]
  rw [hA, hdouble] at hlow
  rw [hC] at hhigh
  omega

end TaskH.Seven

#print axioms TaskH.Seven.critical_nonempty
#print axioms TaskH.Seven.critical_modCycleCount_ge_2880
