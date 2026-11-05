import Research.Backfill.Paper7.IntroR3HighVertex
import Research.Backfill.Paper7.IntroDeletedDegreeRestoration
import Research.Backfill.Paper7.IntroDeletedHighBranch

/-! The high vertex is derived from the original graph, not supplied as a profile premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroHighVertex
open SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral
open Paper7IntroCutGap Paper7IntroHighBranch

theorem intro21_even_high_component_original_complement_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (i : C.supp) (hi : 5 ≤ G.degree i.val.val) (hiv : ¬G.Adj i.val.val v) :
    ∀ j : {x : {w : V // w ≠ v} // x ∉ C.supp}, G.degree j.val.val ≤ 5 ∧
      (¬G.Adj j.val.val v → G.degree j.val.val ≤ 4) := by
  have hrestore := deleted_component_original_degree_restore G v C i
  rw [ite_eq_right hiv, add_zero] at hrestore
  have hhigh : 5 ≤ ((vertexDeletedGraph G v).induce C.supp).degree i := by omega
  have hbound := intro21_even_high_component_complement_degree_le_four
    G b hG hI hn hb v C i hhigh
  intro j
  have hj := hbound j
  have he := deleted_complement_original_degree_restore G v C j
  constructor
  · split_ifs at he <;> omega
  · intro hjv
    rw [ite_eq_right hjv, add_zero] at he
    omega
#print axioms Paper7IntroHighVertex.intro21_even_high_component_original_complement_bound

theorem intro21_even_radius_three_high_vertex_reduction
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (hthree : (integerSpectrum G).count 3 = 1) :
    ∃ u : V, 5 ≤ G.degree u ∧
      ∀ (v : V) (huv : u ≠ v), ¬G.Adj u v →
        ∀ (C : (vertexDeletedGraph G v).ConnectedComponent)
          (_huC : (⟨u, huv⟩ : {w : V // w ≠ v}) ∈ C.supp),
          ∀ j : {x : {w : V // w ≠ v} // x ∉ C.supp}, G.degree j.val.val ≤ 5 ∧
            (¬G.Adj j.val.val v → G.degree j.val.val ≤ 4) := by
  obtain ⟨u, hu⟩ := intro21_even_radius_three_exists_degree_ge_five
    G b hG hI hn hb hthree
  refine ⟨u, hu, ?_⟩
  intro v huv hnot C huC
  exact intro21_even_high_component_original_complement_bound
    G b hG hI hn hb v C ⟨⟨u, huv⟩, huC⟩ hu hnot
#print axioms Paper7IntroHighVertex.intro21_even_radius_three_high_vertex_reduction

end Paper7IntroHighVertex
