import Research.TaskH.General.EdgeCyclesDistinct
import Research.TaskH.FiniteBudget

/-!
Conditional E for arbitrary k: every actual color order has a witness;
each actual unoriented cycle edge set admits at most 2*k orders. The
internal ShortCycles interface remains to be derived from original equality.
-/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

/-- The coloring is kept explicit so singleton constructions use the same
actual deleted-edge coloring, rather than an unrelated existential one. -/
theorem critical_coloring_factorial_incidence_bound [Fintype V]
    (hk : 3 ≤ k) (h : IsCriticalPlus k G) (hs : ShortCycles k G) {x y : V} (hxy : G.Adj x y)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin k)) :
    k.factorial ≤ (TaskH.modCyclesThroughAvoid k G x y).ncard * (2 * k) := by
  classical
  let A : Finset (Equiv.Perm (Fin k)) := Finset.univ
  let C := (Set.toFinite (TaskH.modCyclesThroughAvoid k G x y)).toFinset
  let R : Equiv.Perm (Fin k) → Finset (Sym2 V) → Prop :=
    fun π s => π ∈ basedCycleOrders (G := G) c x s
  have hA : A.card = k.factorial := by simp [A, Fintype.card_perm]
  have hrow : ∀ π ∈ A, 1 ≤ (C.filter (R π)).card := by
    intro π _hπ
    obtain ⟨p, hp, hlen, hf, hy⟩ := critical_edge_ordered_cycle hk h hs hxy c π
    have hm : p.edges.toFinset ∈ C.filter (R π) := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact (Set.toFinite _).mem_toFinset.mpr
          (mem_modCyclesThroughAvoid_of_cycle hp hlen hy)
      · apply (mem_basedCycleOrders c x p.edges.toFinset π).mpr
        exact ⟨p, hp, hlen, p.coe_edges_toFinset.symm, hf⟩
    have hpos := Finset.card_pos.mpr ⟨p.edges.toFinset, hm⟩
    omega
  have hcol : ∀ s ∈ C, (A.filter (fun π => R π s)).card ≤ 2 * k := by
    intro s _hs
    have he : A.filter (fun π => R π s) = basedCycleOrders (G := G) c x s := by
      ext π
      simp only [A, R, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he]
    exact basedCycleOrders_card_le_two_mul hk c x s
  have hdouble : (∑ π ∈ A, (C.filter (R π)).card) =
      ∑ s ∈ C, (A.filter (fun π => R π s)).card := by
    convert FiniteBudget.relation_double_count A C R using 1 <;>
      apply Finset.sum_congr rfl
    all_goals
      intro z _
      congr 1
      ext w
      simp only [Finset.mem_filter]
  have hlow : A.card ≤ ∑ π ∈ A, (C.filter (R π)).card := by
    calc
      A.card = ∑ _π ∈ A, 1 := by simp
      _ ≤ ∑ π ∈ A, (C.filter (R π)).card := Finset.sum_le_sum hrow
  have hhigh : (∑ s ∈ C, (A.filter (fun π => R π s)).card) ≤ C.card * (2 * k) := by
    calc
      _ ≤ ∑ _s ∈ C, 2 * k := Finset.sum_le_sum hcol
      _ = C.card * (2 * k) := by simp
  have hmid : (∑ π ∈ A, (C.filter (R π)).card) ≤
      ∑ s ∈ C, (A.filter (fun π => R π s)).card := le_of_eq hdouble
  have htotal : (∑ π ∈ A, (C.filter (R π)).card) ≤ C.card * (2 * k) :=
    Nat.le_trans hmid hhigh
  have hn : k.factorial ≤ C.card * (2 * k) := by
    rw [hA] at hlow
    exact Nat.le_trans hlow htotal
  have hC : C.card = (TaskH.modCyclesThroughAvoid k G x y).ncard :=
    (Set.ncard_eq_toFinset_card (TaskH.modCyclesThroughAvoid k G x y)
      (Set.toFinite (TaskH.modCyclesThroughAvoid k G x y))).symm
  simpa only [hC] using hn

/-- The usual (k-1)!/2 E bound follows by cancelling the positive factor k. -/
theorem critical_coloring_modCyclesThroughAvoid_lower [Fintype V]
    (hk : 3 ≤ k) (h : IsCriticalPlus k G) (hs : ShortCycles k G)
    {x y : V} (hxy : G.Adj x y)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin k)) :
    (k - 1).factorial / 2 ≤ (TaskH.modCyclesThroughAvoid k G x y).ncard := by
  have hn := critical_coloring_factorial_incidence_bound hk h hs hxy c
  have hfac : k.factorial = k * (k - 1).factorial := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
      Nat.factorial_succ (k - 1)
  have hprod : k * (k - 1).factorial ≤
      k * (2 * (TaskH.modCyclesThroughAvoid k G x y).ncard) := by
    calc
      k * (k - 1).factorial = k.factorial := hfac.symm
      _ ≤ (TaskH.modCyclesThroughAvoid k G x y).ncard * (2 * k) := hn
      _ = k * (2 * (TaskH.modCyclesThroughAvoid k G x y).ncard) := by ac_rfl
  have hcancel : (k - 1).factorial ≤
      2 * (TaskH.modCyclesThroughAvoid k G x y).ncard :=
    le_of_mul_le_mul_left hprod (by omega : 0 < k)
  omega

theorem critical_edge_modCyclesThroughAvoid_lower [Fintype V]
    (hk : 3 ≤ k) (h : IsCriticalPlus k G) (hs : ShortCycles k G)
    {x y : V} (hxy : G.Adj x y) :
    (k - 1).factorial / 2 ≤ (TaskH.modCyclesThroughAvoid k G x y).ncard := by
  obtain ⟨c⟩ := critical_colorable_deletedEdge h hxy
  exact critical_coloring_modCyclesThroughAvoid_lower hk h hs hxy c

end TaskH.General

#print axioms TaskH.General.critical_coloring_factorial_incidence_bound
#print axioms TaskH.General.critical_coloring_modCyclesThroughAvoid_lower
#print axioms TaskH.General.critical_edge_modCyclesThroughAvoid_lower
