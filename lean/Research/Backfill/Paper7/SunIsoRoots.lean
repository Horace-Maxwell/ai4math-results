import Research.Backfill.Paper7.SunCycleCount

set_option autoImplicit false

noncomputable section

namespace Paper7Setup

open SimpleGraph BackfillPaper7.Challenge
open scoped Classical

/-- Every root lies on an actual simple cycle, including for a triangle and
when all arm lists are empty. -/
theorem sun_root_has_cycle (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) (k : Fin b) :
    ∃ c : (sunGraph b L).Walk (Sum.inl k) (Sum.inl k), c.IsCycle := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
  let c := cycleGraph.cycle n
  have hc : c.IsCycle := cycleGraph.isCycle_cycle
  have hh : c.IsHamiltonianCycle :=
    Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hc, by simp [c]⟩
  let d := c.rotate k (hh.mem_support k)
  let f := Paper7SunMoments.sunCycleHom (n + 3) L hb
  exact ⟨d.map f, (hc.rotate (hh.mem_support k)).map Sum.inl_injective⟩

#print axioms Paper7Setup.sun_root_has_cycle

theorem sun_iso_maps_root {b : ℕ} {L L' : Fin b → List ℕ} (hb : 3 ≤ b)
    (e : sunGraph b L ≃g sunGraph b L') (k : Fin b) :
    ∃ j : Fin b, e (Sum.inl k) = Sum.inl j := by
  obtain ⟨c, hc⟩ := sun_root_has_cycle b L hb k
  let d := c.map e.toHom
  have hd : d.IsCycle := hc.map e.injective
  exact Paper7SunMoments.sun_cycle_support_root d hd _ d.start_mem_support

#print axioms Paper7Setup.sun_iso_maps_root

def sunIsoRootMap {b : ℕ} {L L' : Fin b → List ℕ} (hb : 3 ≤ b)
    (e : sunGraph b L ≃g sunGraph b L') (k : Fin b) : Fin b :=
  Classical.choose (sun_iso_maps_root hb e k)

#print axioms Paper7Setup.sunIsoRootMap

theorem sunIsoRootMap_spec {b : ℕ} {L L' : Fin b → List ℕ} (hb : 3 ≤ b)
    (e : sunGraph b L ≃g sunGraph b L') (k : Fin b) :
    e (Sum.inl k) = Sum.inl (sunIsoRootMap hb e k) :=
  Classical.choose_spec (sun_iso_maps_root hb e k)

#print axioms Paper7Setup.sunIsoRootMap_spec

theorem sunIsoRootMap_bijective {b : ℕ} {L L' : Fin b → List ℕ} (hb : 3 ≤ b)
    (e : sunGraph b L ≃g sunGraph b L') : Function.Bijective (sunIsoRootMap hb e) := by
  constructor
  · intro i j hij
    apply Sum.inl_injective
    apply e.injective
    rw [sunIsoRootMap_spec hb e i, sunIsoRootMap_spec hb e j, hij]
  · intro j
    obtain ⟨i, hi⟩ := sun_iso_maps_root hb e.symm j
    refine ⟨i, ?_⟩
    apply Sum.inl_injective
    rw [← sunIsoRootMap_spec hb e i, ← hi, e.apply_symm_apply]

#print axioms Paper7Setup.sunIsoRootMap_bijective

def sunIsoRootEquiv {b : ℕ} {L L' : Fin b → List ℕ} (hb : 3 ≤ b)
    (e : sunGraph b L ≃g sunGraph b L') : Fin b ≃ Fin b :=
  Equiv.ofBijective (sunIsoRootMap hb e) (sunIsoRootMap_bijective hb e)

#print axioms Paper7Setup.sunIsoRootEquiv

theorem sunIsoRootEquiv_adj {b : ℕ} {L L' : Fin b → List ℕ} (hb : 3 ≤ b)
    (e : sunGraph b L ≃g sunGraph b L') (i j : Fin b) :
    (cycleGraph b).Adj (sunIsoRootEquiv hb e i) (sunIsoRootEquiv hb e j) ↔
      (cycleGraph b).Adj i j := by
  change (cycleGraph b).Adj (sunIsoRootMap hb e i) (sunIsoRootMap hb e j) ↔ _
  rw [← Paper7Cleared.sun_cycle_adj_iff b L' hb,
    ← sunIsoRootMap_spec hb e i, ← sunIsoRootMap_spec hb e j,
    e.map_adj_iff, Paper7Cleared.sun_cycle_adj_iff b L hb]

#print axioms Paper7Setup.sunIsoRootEquiv_adj

/-- Restriction to the intrinsic unique cycle gives a genuine cycle-graph
automorphism, rather than an assumed root-label permutation. -/
def sunIsoRootIso {b : ℕ} {L L' : Fin b → List ℕ} (hb : 3 ≤ b)
    (e : sunGraph b L ≃g sunGraph b L') : cycleGraph b ≃g cycleGraph b where
  toEquiv := sunIsoRootEquiv hb e
  map_rel_iff' := fun {i j} => sunIsoRootEquiv_adj hb e i j

#print axioms Paper7Setup.sunIsoRootIso

end Paper7Setup
