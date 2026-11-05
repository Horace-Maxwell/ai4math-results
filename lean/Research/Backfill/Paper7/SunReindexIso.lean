import Research.Backfill.Paper7.SunGraphAdjacency

set_option autoImplicit false

noncomputable section

namespace Paper7Setup

open SimpleGraph BackfillPaper7.Challenge

def sunReindexEquiv (b : ℕ) (L : Fin b → List ℕ) (σ : Fin b ≃ Fin b) :
    SunV b (L ∘ σ) ≃ SunV b L :=
  Equiv.sumCongr σ (Equiv.sigmaCongrLeft
    (β := fun k : Fin b => Σ j : Fin (L k).length, Fin ((L k).get j)) σ)

#print axioms Paper7Setup.sunReindexEquiv

/-- Relabel roots by a genuine automorphism of the base circle, carrying
every complete arm with its root. Arm lengths may be zero. -/
def sunReindexIso (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (σ : cycleGraph b ≃g cycleGraph b) : sunGraph b (L ∘ σ) ≃g sunGraph b L where
  toEquiv := sunReindexEquiv b L σ.toEquiv
  map_rel_iff' := by
    intro x y
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        change (sunGraph b L).Adj (Sum.inl (σ i)) (Sum.inl (σ j)) ↔ _
        rw [Paper7Cleared.sun_cycle_adj_iff b L hb,
          Paper7Cleared.sun_cycle_adj_iff b (L ∘ σ) hb, σ.map_adj_iff]
      | inr z =>
        rcases z with ⟨k, j, a⟩
        change (sunGraph b L).Adj (Sum.inl (σ i)) (Sum.inr ⟨σ k, j, a⟩) ↔ _
        rw [Paper7Cleared.sun_root_arm_adj_iff, Paper7Cleared.sun_root_arm_adj_iff]
        exact and_congr σ.injective.eq_iff Iff.rfl
    | inr x =>
      rcases x with ⟨k, j, a⟩
      cases y with
      | inl i =>
        change (sunGraph b L).Adj (Sum.inr ⟨σ k, j, a⟩) (Sum.inl (σ i)) ↔ _
        rw [Paper7Cleared.sun_arm_root_adj_iff, Paper7Cleared.sun_arm_root_adj_iff]
        exact and_congr σ.injective.eq_iff Iff.rfl
      | inr y =>
        rcases y with ⟨k', j', a'⟩
        change (sunGraph b L).Adj (Sum.inr ⟨σ k, j, a⟩) (Sum.inr ⟨σ k', j', a'⟩) ↔ _
        rw [Paper7Cleared.sun_arm_adj_iff, Paper7Cleared.sun_arm_adj_iff]
        exact and_congr σ.injective.eq_iff Iff.rfl

#print axioms Paper7Setup.sunReindexIso

def sgReindexIso (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (σ : cycleGraph b ≃g cycleGraph b) :
    SG b (p ∘ σ) (q ∘ σ) ≃g SG b p q :=
  sunReindexIso b (pq b p q) hb σ

#print axioms Paper7Setup.sgReindexIso

end Paper7Setup
