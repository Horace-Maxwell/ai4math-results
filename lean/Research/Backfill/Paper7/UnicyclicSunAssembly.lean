import Research.Backfill.Paper7.FiniteAttachmentLists
import Research.Backfill.Paper7.UnicyclicCoreCycle
import Research.Backfill.Paper7.UnicyclicComponentPaths

/-! Source-only complete conditional Sun assembly candidate. The existing
structural imports and the other modules in this package are all pending.
The outside-degree condition is confined to this helper; it is not added to
IntroUnicyclic21. No spectral exclusion of branching is asserted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7SunAssembly
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open scoped Classical

theorem unicyclic_off_cycle_degree_two_sun_iso {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (r : V) (w : G.Walk r r)
    (hw : w.IsCycle) (hlen : w.length = b)
    (hdeg : ∀ v, v ∉ w.support → G.degree v ≤ 2) :
    ∃ L : Fin b → List ℕ, Nonempty (G ≃g sunGraph b L) ∧
      ∀ (k : Fin b) (j : Fin (L k).length), 0 < (L k).get j := by
  let S : Set V := {v | v ∈ w.support}
  let H := deleteVertices G S
  let : Fintype H.ConnectedComponent := Fintype.ofFinite H.ConnectedComponent
  obtain ⟨core⟩ := unicyclic_core_iso_cycle G b hG r w hw hlen
  choose n hn e c _hcard hinside hboundary using
    (fun C : H.ConnectedComponent =>
      Paper7UnicyclicComponentPaths.unicyclic_component_path_coordinates
        G b hG r w hw hlen hdeg C)
  let root : H.ConnectedComponent → Fin b := fun C => core.symm (c C)
  let L : Fin b → List ℕ := attachmentLengths root n
  let blocks := attachmentBlockEquiv root n
  let outside : (Σ C : H.ConnectedComponent, Fin (n C)) ≃ {v // v ∉ S} :=
    (Equiv.sigmaCongrRight fun C => (e C).toEquiv).trans
      (Equiv.sigmaFiberEquiv H.connectedComponentMk)
  let packed : (Fin b ⊕ (Σ C : H.ConnectedComponent, Fin (n C))) ≃ V :=
    (Equiv.sumCongr core.toEquiv outside).trans (Equiv.Set.sumCompl S)
  let full : SunV b L ≃ V :=
    (Equiv.sumCongr (Equiv.refl (Fin b)) (attachmentArmEquiv root n)).trans packed
  have hcore (k l : Fin b) :
      G.Adj (core k).val (core l).val ↔ (cycleGraph b).Adj k l :=
    core.map_rel_iff
  have hmixed (C : H.ConnectedComponent) (i : Fin (n C)) (k : Fin b) :
      G.Adj (e C i).val.val (core k).val ↔ root C = k ∧ i.val = 0 := by
    rw [hboundary C i (core k)]
    constructor
    · rintro ⟨hi, hc⟩
      refine ⟨?_, hi⟩
      change core.symm (c C) = k
      rw [← hc]
      exact core.symm_apply_apply k
    · rintro ⟨hr, hi⟩
      refine ⟨hi, ?_⟩
      rw [← hr]
      exact core.apply_symm_apply (c C)
  have harms (C D : H.ConnectedComponent) (i : Fin (n C)) (j : Fin (n D)) :
      G.Adj (e C i).val.val (e D j).val.val ↔
        C = D ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    by_cases hCD : C = D
    · subst D
      constructor
      · intro h
        exact ⟨rfl, (hinside C i j).mp h⟩
      · rintro ⟨_, h⟩
        exact (hinside C i j).mpr h
    · constructor
      · intro h
        have hxD : (e C i).val ∈ D.supp :=
          D.mem_supp_of_adj_mem_supp (e D j).property (show H.Adj
            (e D j).val (e C i).val from h.symm)
        have heq : C = D :=
          ConnectedComponent.eq_of_common_vertex (e C i).property hxD
        exact (hCD heq).elim
      · rintro ⟨heq, _⟩
        exact (hCD heq).elim
  have hb : 3 ≤ b := Paper7Unicyclic.unicyclic_three_le hG
  have hadj : ∀ x y : SunV b L, G.Adj (full x) (full y) ↔ (sunGraph b L).Adj x y := by
    intro x y
    cases x with
    | inl k =>
      cases y with
      | inl l =>
        change G.Adj (core k).val (core l).val ↔
          (sunGraph b L).Adj (Sum.inl k) (Sum.inl l)
        rw [hcore, Paper7Cleared.sun_cycle_adj_iff b L hb]
      | inr q =>
        rcases q with ⟨l, j, i⟩
        change G.Adj (core k).val
          (e (blocks ⟨l, j⟩) (Fin.cast (attachmentLengths_get root n l j) i)).val.val ↔
            (sunGraph b L).Adj (Sum.inl k) (Sum.inr ⟨l, j, i⟩)
        rw [G.adj_comm, hmixed, attachmentBlock_root root n l j,
          Paper7Cleared.sun_root_arm_adj_iff]
        simp only [Fin.val_cast]
    | inr q =>
      rcases q with ⟨k, j, i⟩
      cases y with
      | inl l =>
        change G.Adj
          (e (blocks ⟨k, j⟩) (Fin.cast (attachmentLengths_get root n k j) i)).val.val
          (core l).val ↔ (sunGraph b L).Adj (Sum.inr ⟨k, j, i⟩) (Sum.inl l)
        rw [hmixed, attachmentBlock_root root n k j, Paper7Cleared.sun_arm_root_adj_iff]
        simp only [Fin.val_cast]
      | inr q' =>
        rcases q' with ⟨k', j', i'⟩
        change G.Adj
          (e (blocks ⟨k, j⟩) (Fin.cast (attachmentLengths_get root n k j) i)).val.val
          (e (blocks ⟨k', j'⟩) (Fin.cast (attachmentLengths_get root n k' j') i')).val.val ↔
            (sunGraph b L).Adj (Sum.inr ⟨k, j, i⟩) (Sum.inr ⟨k', j', i'⟩)
        rw [harms, attachmentBlock_eq_iff, Paper7Cleared.sun_arm_adj_iff]
        exact and_assoc
  let iso : sunGraph b L ≃g G :=
    { toEquiv := full
      map_rel_iff' := by
        intro x y
        exact hadj x y }
  refine ⟨L, ⟨iso.symm⟩, ?_⟩
  intro k j
  exact attachmentLengths_pos root n hn k j
#print axioms Paper7SunAssembly.unicyclic_off_cycle_degree_two_sun_iso

end Paper7SunAssembly
