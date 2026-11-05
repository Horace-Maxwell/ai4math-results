import Research.Backfill.Paper7.VerasPolynomial
import Research.Backfill.Paper7.SunCycleCount

set_option autoImplicit false

noncomputable section

namespace Paper7Veras

open SimpleGraph BackfillPaper7.Challenge

theorem veras_arm_length (a : ℕ) (k : Fin 4) (t : ℕ)
    (ht : t ∈ VerasSquare a k) : t = 1 := by
  fin_cases k
  · simp [VerasSquare] at ht
  · exact List.eq_of_mem_replicate ht
  · exact List.eq_of_mem_replicate ht
  · exact List.eq_of_mem_replicate ht
#print axioms Paper7Veras.veras_arm_length

/-- Every actual arm vertex is joined directly to its cycle root, and the
original four cycle roots are connected by the embedded four-cycle. -/
theorem veras_connected (a : ℕ) : (sunGraph 4 (VerasSquare a)).Connected := by
  have hcycle : (SimpleGraph.cycleGraph 4).Connected :=
    SimpleGraph.cycleGraph_connected
  have hr (k : Fin 4) :
      (sunGraph 4 (VerasSquare a)).Reachable (Sum.inl 0) (Sum.inl k) := by
    exact SimpleGraph.Reachable.map
      (Paper7SunMoments.sunCycleHom 4 (VerasSquare a) (by decide)) (hcycle 0 k)
  apply (SimpleGraph.connected_iff_exists_forall_reachable (sunGraph 4 (VerasSquare a))).mpr
  refine ⟨Sum.inl 0, ?_⟩
  intro w
  cases w with
  | inl k => exact hr k
  | inr z =>
    rcases z with ⟨k, j, i⟩
    have hlen : ((VerasSquare a k).get j) = 1 :=
      veras_arm_length a k _ (List.get_mem (VerasSquare a k) j)
    have hi : i.val = 0 := by
      have hb := i.isLt
      omega
    have hadj : (sunGraph 4 (VerasSquare a)).Adj (Sum.inl k) (Sum.inr ⟨k, j, i⟩) :=
      (Paper7Cleared.sun_root_arm_adj_iff 4 (VerasSquare a) k k j i).mpr ⟨rfl, hi⟩
    exact (hr k).trans hadj.reachable
#print axioms Paper7Veras.veras_connected

theorem veras_unicyclic (a : ℕ) :
    IsUnicyclicWithCycle (sunGraph 4 (VerasSquare a)) 4 := by
  obtain ⟨s, hs, huniq⟩ :=
    Paper7SunMoments.sun_cycle_unique_data 4 (VerasSquare a) (by decide)
  refine ⟨veras_connected a, s, hs, ?_⟩
  intro ell t ht
  exact (huniq ell t ht).2
#print axioms Paper7Veras.veras_unicyclic

end Paper7Veras
