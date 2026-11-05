import Research.Backfill.Paper7.SunPerron
import Research.Backfill.Paper7.AlgebraicContracts

/-! Actual Sun data for Schwenk's identity, for arbitrary pendant-path lists.
The unique-cycle and connectedness inputs below are existing proved helpers.
No restriction is imposed on the arm lengths, and b=3 is retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Paper7SunSchwenk
open SimpleGraph BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem sun_unicyclic (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) :
    IsUnicyclicWithCycle (sunGraph b L) b := by
  obtain ⟨s, hs, huniq⟩ := Paper7SunMoments.sun_cycle_unique_data b L hb
  refine ⟨Paper7Admissible.sun_connected b L hb, s, hs, ?_⟩
  intro ell t ht
  exact (huniq ell t ht).2
#print axioms Paper7SunSchwenk.sun_unicyclic

theorem cycle_vertex_has_neighbor (b : ℕ) (hb : 3 ≤ b) (i : Fin b) :
    ∃ j : Fin b, (SimpleGraph.cycleGraph b).Adj i j := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
  apply ((SimpleGraph.cycleGraph (n + 3)).degree_pos_iff_exists_adj i).mp
  rw [SimpleGraph.cycleGraph_degree_three_le]
  exact Nat.zero_lt_succ 1
#print axioms Paper7SunSchwenk.cycle_vertex_has_neighbor

theorem reference_cycle_support_eq (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (r : SunV b L) (c : (sunGraph b L).Walk r r) (hc : c.IsCycle)
    (hcover : ∀ i j : Fin b, (sunGraph b L).Adj (Sum.inl i) (Sum.inl j) →
      s(Sum.inl i, Sum.inl j) ∈ c.edges) :
    {z | z ∈ c.support} = sunCycleVertices b L := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Paper7SunMoments.sun_cycle_support_root c hc z hz
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hij⟩ := cycle_vertex_has_neighbor b hb i
    exact c.fst_mem_support_of_mem_edges
      (hcover i j ((Paper7Cleared.sun_cycle_adj_iff b L hb i j).mpr hij))
#print axioms Paper7SunSchwenk.reference_cycle_support_eq

/-- The supplied cycle edge belongs to an actual simple closed walk whose
support is precisely the complete set of cycle roots. -/
theorem sun_cycle_edge_witness (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (u v : Fin b) (huv : (SimpleGraph.cycleGraph b).Adj u v) :
    ∃ r : SunV b L, ∃ c : (sunGraph b L).Walk r r,
      c.IsCycle ∧ c.length = b ∧ s(Sum.inl u, Sum.inl v) ∈ c.edges ∧
        {z | z ∈ c.support} = sunCycleVertices b L := by
  obtain ⟨r, c, hc, hlen, hcover⟩ := Paper7SunMoments.sun_reference_cycle b L hb
  refine ⟨r, c, hc, hlen, ?_, reference_cycle_support_eq b L hb r c hc hcover⟩
  exact hcover u v ((Paper7Cleared.sun_cycle_adj_iff b L hb u v).mpr huv)
#print axioms Paper7SunSchwenk.sun_cycle_edge_witness

end Paper7SunSchwenk
