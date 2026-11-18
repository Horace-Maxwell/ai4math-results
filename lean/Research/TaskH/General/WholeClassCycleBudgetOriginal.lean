import Research.TaskH.General.OriginalCycleIncidence

/-! Double counting the ENTIRE old color class against ALL actual cycle edge sets.
The missing h cycles are the genuine E(v,a), not a selected rank-order image. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open SimpleGraph _root_.TaskH.Challenge
open scoped BigOperators
variable {k : ℕ} {V : Type u} {G : SimpleGraph V}

noncomputable def wholeDeletedColorClass [Fintype V] {v : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) (γ : Fin k) : Finset V := by
  classical
  exact Finset.univ.filter (fun z => ∃ hz : z ≠ v, c ⟨z, hz⟩ = γ)

theorem mem_wholeDeletedColorClass [Fintype V] {v : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) (γ : Fin k) (z : V) :
    z ∈ wholeDeletedColorClass c γ ↔ ∃ hz : z ≠ v, c ⟨z, hz⟩ = γ := by
  classical
  simp [wholeDeletedColorClass]

open scoped Classical in
/-- The actual rainbow theorem bounds each column of the full incidence relation. -/
theorem equality_whole_class_column_le_one [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) (γ : Fin k)
    {s : Finset (Sym2 V)} (hs : s ∈ ModCycleEdgeSets k G) :
    ((wholeDeletedColorClass c γ).filter (fun z => _root_.TaskH.CycleContains s z)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨hav, hca⟩ := (mem_wholeDeletedColorClass c γ a).mp (Finset.mem_filter.mp ha).1
  obtain ⟨hbv, hcb⟩ := (mem_wholeDeletedColorClass c γ b).mp (Finset.mem_filter.mp hb).1
  obtain ⟨x, p, hp, he, hdiv⟩ := Basics.mem_modCycleEdgeSets_iff.mp hs
  have hlen := GoodCycles.equality_shortCycles_from_critical_count hk hcrit hcount p hp hdiv
  have hap : a ∈ p.support := by
    apply (_root_.TaskH.cycleContains_edges_toFinset_iff p hp.not_nil a).mp
    rw [he]
    exact (Finset.mem_filter.mp ha).2
  have hbp : b ∈ p.support := by
    apply (_root_.TaskH.cycleContains_edges_toFinset_iff p hp.not_nil b).mp
    rw [he]
    exact (Finset.mem_filter.mp hb).2
  exact equality_original_cycle_support_rainbow hk hcrit hcount c p hp hlen
    hap hbp hav hbv (hca.trans hcb.symm)

open scoped Classical in
/-- Actual finite vertex incidence is the row cardinality in the original collection. -/
theorem original_incidence_row_card [Fintype V] (x : V) :
    (((Basics.modCycleEdgeSets_finite k G).toFinset).filter
      (fun s => _root_.TaskH.CycleContains s x)).card =
      (_root_.TaskH.modCyclesThrough k G x).ncard := by
  classical
  have he : _root_.TaskH.modCyclesThrough k G x =
      ((((Basics.modCycleEdgeSets_finite k G).toFinset).filter
        (fun s => _root_.TaskH.CycleContains s x) : Finset (Finset (Sym2 V))) :
          Set (Finset (Sym2 V))) := by
    ext s
    simp [_root_.TaskH.modCyclesThrough]
  rw [he, Set.ncard_coe_finset]

/-- Every old whole color class has total actual incidence at most the original bound. -/
theorem equality_whole_class_incidence_budget [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) (γ : Fin k) :
    ∑ z ∈ wholeDeletedColorClass c γ,
      (_root_.TaskH.modCyclesThrough k G z).ncard ≤ bound k := by
  classical
  let C := (Basics.modCycleEdgeSets_finite k G).toFinset
  let W := wholeDeletedColorClass c γ
  have hC : C.card = bound k := by
    calc
      C.card = (ModCycleEdgeSets k G).ncard :=
        (Set.ncard_eq_toFinset_card _ (Basics.modCycleEdgeSets_finite k G)).symm
      _ = bound k := hcount
  calc
    ∑ z ∈ W, (_root_.TaskH.modCyclesThrough k G z).ncard =
        ∑ z ∈ W, (C.filter (fun s => _root_.TaskH.CycleContains s z)).card := by
      apply Finset.sum_congr rfl
      intro z _
      exact (original_incidence_row_card z).symm
    _ = ∑ s ∈ C, (W.filter (fun z => _root_.TaskH.CycleContains s z)).card :=
      _root_.TaskH.FiniteBudget.relation_double_count W C
        (fun z s => _root_.TaskH.CycleContains s z)
    _ ≤ ∑ _s ∈ C, 1 := by
      apply Finset.sum_le_sum
      intro s hs
      exact equality_whole_class_column_le_one hk hcrit hcount c γ
        ((Basics.modCycleEdgeSets_finite k G).mem_toFinset.mp hs)
    _ = bound k := by simpa only [Finset.sum_const, smul_eq_mul, mul_one] using hC

/-- The ENTIRE singleton color class has an h-sized actual missing-cycle budget. -/
theorem equality_singleton_whole_class_missing_budget [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩) :
    (∑ z ∈ wholeDeletedColorClass c (c ⟨a, hva.ne.symm⟩),
      (_root_.TaskH.modCyclesThrough k G z).ncard) + (k - 1).factorial / 2 ≤ bound k := by
  classical
  let C := (Basics.modCycleEdgeSets_finite k G).toFinset
  let W := wholeDeletedColorClass c (c ⟨a, hva.ne.symm⟩)
  have hfA : (_root_.TaskH.modCyclesThroughAvoid k G v a).Finite :=
    (Basics.modCycleEdgeSets_finite k G).subset (fun _ hs => hs.1)
  let A := hfA.toFinset
  have hAC : A ⊆ C := by
    intro s hs
    exact (Basics.modCycleEdgeSets_finite k G).mem_toFinset.mpr
      (hfA.mem_toFinset.mp hs).1
  have hA : A.card = (_root_.TaskH.modCyclesThroughAvoid k G v a).ncard :=
    (Set.ncard_eq_toFinset_card _ hfA).symm
  have hC : C.card = bound k := by
    calc
      C.card = (ModCycleEdgeSets k G).ncard :=
        (Set.ncard_eq_toFinset_card _ (Basics.modCycleEdgeSets_finite k G)).symm
      _ = bound k := hcount
  have hcol : ∀ s ∈ C,
      (W.filter (fun z => _root_.TaskH.CycleContains s z)).card +
        (if s ∈ A then 1 else 0) ≤ 1 := by
    intro s hs
    by_cases hsa : s ∈ A
    · have hz : W.filter (fun z => _root_.TaskH.CycleContains s z) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨hzv, hzc⟩ := (mem_wholeDeletedColorClass c _ z).mp
          (Finset.mem_filter.mp hz).1
        exact (equality_all_edge_sets_retain_and_omit hk hcrit hcount hva hvb c
          haunique hbunique habcolor s (hfA.mem_toFinset.mp hsa)).2 z hzv hzc
          (Finset.mem_filter.mp hz).2
      rw [hz, Finset.card_empty, ite_eq_left hsa]
    · rw [ite_eq_right hsa, add_zero]
      exact equality_whole_class_column_le_one hk hcrit hcount c _
        ((Basics.modCycleEdgeSets_finite k G).mem_toFinset.mp hs)
  have hfilter : C.filter (fun s => s ∈ A) = A := by
    ext s
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hAC h, h⟩⟩
  have hind : (∑ s ∈ C, (if s ∈ A then 1 else 0)) = A.card := by
    rw [← Finset.card_filter, hfilter]
  have hdc := _root_.TaskH.FiniteBudget.relation_double_count W C
    (fun z s => _root_.TaskH.CycleContains s z)
  have hrows : (∑ z ∈ W, (C.filter (fun s => _root_.TaskH.CycleContains s z)).card) =
      ∑ z ∈ W, (_root_.TaskH.modCyclesThrough k G z).ncard := by
    apply Finset.sum_congr rfl
    intro z _
    exact original_incidence_row_card z
  have hconst : (∑ _s ∈ C, 1) = bound k := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using hC
  have hbudget : (∑ z ∈ W, (_root_.TaskH.modCyclesThrough k G z).ncard) +
      A.card ≤ bound k := by
    calc
      (∑ z ∈ W, (_root_.TaskH.modCyclesThrough k G z).ncard) + A.card =
          (∑ s ∈ C, (W.filter (fun z => _root_.TaskH.CycleContains s z)).card) +
            (∑ s ∈ C, (if s ∈ A then 1 else 0)) := by
        rw [← hrows, hdc, hind]
      _ = ∑ s ∈ C, ((W.filter (fun z => _root_.TaskH.CycleContains s z)).card +
          (if s ∈ A then 1 else 0)) := Finset.sum_add_distrib.symm
      _ ≤ ∑ _s ∈ C, 1 := Finset.sum_le_sum hcol
      _ = bound k := hconst
  have hlowA : (k - 1).factorial / 2 ≤ A.card := by
    rw [hA]
    exact equality_original_edge_cycle_lower hk hcrit hcount hva
  change (∑ z ∈ W, (_root_.TaskH.modCyclesThrough k G z).ncard) +
    (k - 1).factorial / 2 ≤ bound k
  exact (Nat.add_le_add_left hlowA _).trans hbudget
end TaskH.General
#print axioms TaskH.General.wholeDeletedColorClass
#print axioms TaskH.General.mem_wholeDeletedColorClass
#print axioms TaskH.General.equality_whole_class_column_le_one
#print axioms TaskH.General.original_incidence_row_card
#print axioms TaskH.General.equality_whole_class_incidence_budget
#print axioms TaskH.General.equality_singleton_whole_class_missing_budget
