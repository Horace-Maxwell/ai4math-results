import Research.TaskH.General.EqualityRainbowOriginal
import Research.TaskH.General.EdgeCyclesCount

/-!
Actual E and prescribed-color-order cycles directly from the original
criticality and exact cycle count. No internal ShortCycles/R hypothesis
is added to a final graph statement. The coloring argument retains the
chosen coloring of the whole edge-deleted graph for later singleton donors.
-/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_edge_ordered_cycle (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {x y : V} (hxy : G.Adj x y)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) :
    ∃ q : G.Walk x x, q.IsCycle ∧ q.length = k ∧
      Follows q (fun z => π (c z)) (finRotate k) ∧ y ∉ q.support := by
  exact critical_edge_ordered_cycle (by omega) hcrit
    (GoodCycles.equality_shortCycles_from_critical_count hk hcrit hcount) hxy c π

theorem equality_original_coloring_factorial_incidence_bound (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {x y : V} (hxy : G.Adj x y)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin k)) :
    k.factorial ≤ (TaskH.modCyclesThroughAvoid k G x y).ncard * (2 * k) := by
  exact critical_coloring_factorial_incidence_bound (by omega) hcrit
    (GoodCycles.equality_shortCycles_from_critical_count hk hcrit hcount) hxy c

theorem equality_original_coloring_edge_cycle_lower (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {x y : V} (hxy : G.Adj x y)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin k)) :
    (k - 1).factorial / 2 ≤ (TaskH.modCyclesThroughAvoid k G x y).ncard := by
  exact critical_coloring_modCyclesThroughAvoid_lower (by omega) hcrit
    (GoodCycles.equality_shortCycles_from_critical_count hk hcrit hcount) hxy c

theorem equality_original_edge_cycle_lower (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {x y : V} (hxy : G.Adj x y) :
    (k - 1).factorial / 2 ≤ (TaskH.modCyclesThroughAvoid k G x y).ncard := by
  exact critical_edge_modCyclesThroughAvoid_lower (by omega) hcrit
    (GoodCycles.equality_shortCycles_from_critical_count hk hcrit hcount) hxy

theorem equality_original_no_double_cycle (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {x : V} (p : G.Walk x x) (hp : p.IsCycle) : p.length ≠ 2 * k := by
  intro hlen
  have he := GoodCycles.equality_shortCycles_from_critical_count hk hcrit hcount p hp
    (by rw [hlen]; exact dvd_mul_left k 2)
  omega

end TaskH.General

#print axioms TaskH.General.equality_original_edge_ordered_cycle
#print axioms TaskH.General.equality_original_coloring_factorial_incidence_bound
#print axioms TaskH.General.equality_original_coloring_edge_cycle_lower
#print axioms TaskH.General.equality_original_edge_cycle_lower
#print axioms TaskH.General.equality_original_no_double_cycle
