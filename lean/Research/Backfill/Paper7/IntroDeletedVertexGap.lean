import Research.Backfill.Paper7.IntroPrincipalGapBudget
import Research.Backfill.Paper7.IntegerSpectrum

/-! Deleting one vertex of an integral graph permits only one root per open unit gap. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroCutGap
open BackfillPaper7.Challenge Paper7OddIntegral

def vertexDeletedGraph {V : Type} (G : SimpleGraph V) (v : V) :
    SimpleGraph {w : V // w ≠ v} := G.induce {w | w ≠ v}
#print axioms Paper7IntroCutGap.vertexDeletedGraph

theorem vertex_deleted_card_add_one {V : Type} [Fintype V] [DecidableEq V] (v : V) :
    Fintype.card {w : V // w ≠ v} + 1 = Fintype.card V := by
  let : Nonempty V := ⟨v⟩
  have hp : 0 < Fintype.card V := Fintype.card_pos
  rw [Fintype.card_subtype_compl (fun w : V => w = v), Fintype.card_subtype_eq]
  omega
#print axioms Paper7IntroCutGap.vertex_deleted_card_add_one

theorem integral_open_unit_gap_zero {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G) (m : ℤ) :
    openGapCount G (m : ℝ) ((m : ℝ) + 1) = 0 := by
  have hfilter : (spec G).filter (fun x : ℝ => (m : ℝ) < x ∧ x < (m : ℝ) + 1) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro x hx hgap
    rw [← integerSpectrum_cast G hI] at hx
    obtain ⟨z, _hz, rfl⟩ := Multiset.mem_map.mp hx
    have hl : m < z := by exact_mod_cast hgap.1
    have hu : z < m + 1 := by exact_mod_cast hgap.2
    omega
  change ((spec G).filter (fun x : ℝ => (m : ℝ) < x ∧ x < (m : ℝ) + 1)).card = 0
  rw [hfilter, Multiset.card_zero]
#print axioms Paper7IntroCutGap.integral_open_unit_gap_zero

theorem integral_vertex_deleted_open_unit_gap_le_one
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G) (v : V) (m : ℤ) :
    openGapCount (vertexDeletedGraph G v) (m : ℝ) ((m : ℝ) + 1) ≤ 1 := by
  have h := induced_open_gap_budget G (vertexDeletedGraph G v)
    (fun w : {w : V // w ≠ v} => w.val) Subtype.val_injective
    (by intro i j; rfl) 1 (vertex_deleted_card_add_one v)
    (m : ℝ) ((m : ℝ) + 1) (by linarith)
  rw [integral_open_unit_gap_zero G hI m, zero_add] at h
  exact h
#print axioms Paper7IntroCutGap.integral_vertex_deleted_open_unit_gap_le_one

theorem integral_vertex_deleted_gap_root_count_le_one
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (v : V) (m : ℤ) (x : ℝ) (hl : (m : ℝ) < x) (hu : x < (m : ℝ) + 1) :
    (spec (vertexDeletedGraph G v)).count x ≤ 1 := by
  have h := Multiset.count_le_card x
    ((spec (vertexDeletedGraph G v)).filter (fun y : ℝ => (m : ℝ) < y ∧ y < (m : ℝ) + 1))
  have hgap : (m : ℝ) < x ∧ x < (m : ℝ) + 1 := ⟨hl, hu⟩
  simp only [Multiset.count_filter, hgap] at h
  exact h.trans (integral_vertex_deleted_open_unit_gap_le_one G hI v m)
#print axioms Paper7IntroCutGap.integral_vertex_deleted_gap_root_count_le_one

theorem integral_vertex_deleted_repeated_root_integer
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (v : V) (x : ℝ) (hx : 2 ≤ (spec (vertexDeletedGraph G v)).count x) :
    ∃ z : ℤ, x = (z : ℝ) := by
  by_contra hn
  have hne : x ≠ (⌊x⌋ : ℝ) := by
    intro he
    exact hn ⟨⌊x⌋, he⟩
  have hl : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (Ne.symm hne)
  have h := integral_vertex_deleted_gap_root_count_le_one G hI v ⌊x⌋ x hl
    (Int.lt_floor_add_one x)
  omega
#print axioms Paper7IntroCutGap.integral_vertex_deleted_repeated_root_integer

end Paper7IntroCutGap
