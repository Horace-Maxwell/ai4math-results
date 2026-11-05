import Research.Backfill.Paper7.HexagonPolynomial
import Research.Backfill.Paper7.SunCycleCount

set_option autoImplicit false

noncomputable section

namespace Paper7Hexagon

open SimpleGraph BackfillPaper7.Challenge

theorem hexagon_arm_length (a : ℕ) (k : Fin 6) (t : ℕ)
    (ht : t ∈ HexagonFamily a k) : t = 1 := by
  fin_cases k
  · simp [HexagonFamily] at ht
  · exact List.eq_of_mem_replicate ht
  · exact List.eq_of_mem_replicate ht
  · exact List.eq_of_mem_replicate ht
  · exact List.eq_of_mem_replicate ht
  · exact List.eq_of_mem_replicate ht
#print axioms Paper7Hexagon.hexagon_arm_length

/-- Connectedness of the actual frozen graph, including every dependent arm index. -/
theorem hexagon_connected (a : ℕ) : (sunGraph 6 (HexagonFamily a)).Connected := by
  have hcycle : (SimpleGraph.cycleGraph 6).Connected :=
    SimpleGraph.cycleGraph_connected
  have hr (k : Fin 6) :
      (sunGraph 6 (HexagonFamily a)).Reachable (Sum.inl 0) (Sum.inl k) := by
    exact SimpleGraph.Reachable.map
      (Paper7SunMoments.sunCycleHom 6 (HexagonFamily a) (by decide)) (hcycle 0 k)
  apply (SimpleGraph.connected_iff_exists_forall_reachable (sunGraph 6 (HexagonFamily a))).mpr
  refine ⟨Sum.inl 0, ?_⟩
  intro w
  cases w with
  | inl k => exact hr k
  | inr z =>
    rcases z with ⟨k, j, i⟩
    have hlen : ((HexagonFamily a k).get j) = 1 :=
      hexagon_arm_length a k _ (List.get_mem (HexagonFamily a k) j)
    have hi : i.val = 0 := by
      have hb := i.isLt
      omega
    have hadj : (sunGraph 6 (HexagonFamily a)).Adj (Sum.inl k) (Sum.inr ⟨k, j, i⟩) :=
      (Paper7Cleared.sun_root_arm_adj_iff 6 (HexagonFamily a) k k j i).mpr ⟨rfl, hi⟩
    exact (hr k).trans hadj.reachable
#print axioms Paper7Hexagon.hexagon_connected

theorem hexagon_unicyclic (a : ℕ) :
    IsUnicyclicWithCycle (sunGraph 6 (HexagonFamily a)) 6 := by
  obtain ⟨s, hs, huniq⟩ :=
    Paper7SunMoments.sun_cycle_unique_data 6 (HexagonFamily a) (by decide)
  refine ⟨hexagon_connected a, s, hs, ?_⟩
  intro ell t ht
  exact (huniq ell t ht).2
#print axioms Paper7Hexagon.hexagon_unicyclic

end Paper7Hexagon
