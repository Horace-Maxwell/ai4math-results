import Research.Backfill.Paper3.Proof.TS.Connected

/-!
# Classification by 2-switch closure

If a family `R` of graphs on `Fin n` is closed under 2-switches up to isomorphism, then every
graph with the same degrees as some `R i₀` is isomorphic to a member of `R` (by the 2-switch
theorem). Closure only needs to be checked for switches in canonical form (`u₁` smallest).
-/

set_option autoImplicit false

namespace P3TS

open Finset BackfillPaper3.Challenge

section Transport

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {u₁ w₁ u₂ w₂ : V}

/-- An isomorphism carries 2-switches to 2-switches. -/
theorem IsSwitch.map (φ : G ≃g H) (hs : IsSwitch G u₁ w₁ u₂ w₂) :
    IsSwitch H (φ u₁) (φ w₁) (φ u₂) (φ w₂) where
  adj₁ := φ.map_adj_iff.2 hs.adj₁
  adj₂ := φ.map_adj_iff.2 hs.adj₂
  ne₁ := fun h => hs.ne₁ (φ.injective h)
  ne₂ := fun h => hs.ne₂ (φ.injective h)
  nadj₁ := fun h => hs.nadj₁ (φ.map_adj_iff.1 h)
  nadj₂ := fun h => hs.nadj₂ (φ.map_adj_iff.1 h)

theorem sym2_map_eq_iff {f : V → W} (hf : Function.Injective f) {a b c d : V} :
    s(f a, f b) = s(f c, f d) ↔ s(a, b) = s(c, d) := by
  rw [Sym2.eq_iff, Sym2.eq_iff, hf.eq_iff, hf.eq_iff, hf.eq_iff, hf.eq_iff]

/-- The 2-switch of an isomorphic copy is isomorphic (by the same map). -/
def twoSwitchIso (φ : G ≃g H) (u₁ w₁ u₂ w₂ : V) :
    twoSwitch G u₁ w₁ u₂ w₂ ≃g twoSwitch H (φ u₁) (φ w₁) (φ u₂) (φ w₂) where
  toEquiv := φ.toEquiv
  map_rel_iff' := by
    intro a b
    change (twoSwitch H (φ u₁) (φ w₁) (φ u₂) (φ w₂)).Adj (φ a) (φ b) ↔
      (twoSwitch G u₁ w₁ u₂ w₂).Adj a b
    rw [twoSwitch_adj, twoSwitch_adj, φ.map_adj_iff, sym2_map_eq_iff φ.injective,
      sym2_map_eq_iff φ.injective, sym2_map_eq_iff φ.injective, sym2_map_eq_iff φ.injective,
      φ.injective.ne_iff]

end Transport

section Canonical

variable {n k : ℕ}

/-- It suffices to check closure for 2-switches whose first vertex is the smallest. -/
theorem closed_of_canonical (R : Fin k → SimpleGraph (Fin n))
    (h : ∀ i (u₁ w₁ u₂ w₂ : Fin n), u₁ < w₁ → u₁ < u₂ → u₁ < w₂ →
      IsSwitch (R i) u₁ w₁ u₂ w₂ → ∃ j, Nonempty (twoSwitch (R i) u₁ w₁ u₂ w₂ ≃g R j)) :
    ∀ i (u₁ w₁ u₂ w₂ : Fin n), IsSwitch (R i) u₁ w₁ u₂ w₂ →
      ∃ j, Nonempty (twoSwitch (R i) u₁ w₁ u₂ w₂ ≃g R j) := by
  intro i u₁ w₁ u₂ w₂ hs
  have d1 := hs.u₁_ne_w₁
  have d2 := hs.u₁_ne_u₂
  have d3 := hs.ne₁
  have d4 := hs.ne₂
  have d5 := hs.w₁_ne_w₂
  have d6 := hs.u₂_ne_w₂
  rw [Ne, ← Fin.val_inj] at d1 d2 d3 d4 d5 d6
  by_cases hA : u₁ < w₁ ∧ u₁ < u₂ ∧ u₁ < w₂
  · exact h i u₁ w₁ u₂ w₂ hA.1 hA.2.1 hA.2.2 hs
  by_cases hB : w₁ < u₁ ∧ w₁ < w₂ ∧ w₁ < u₂
  · rw [twoSwitch_swap₁]
    exact h i w₁ u₁ w₂ u₂ hB.1 hB.2.1 hB.2.2 hs.swap₁
  by_cases hC : u₂ < w₂ ∧ u₂ < u₁ ∧ u₂ < w₁
  · rw [twoSwitch_swap₂]
    exact h i u₂ w₂ u₁ w₁ hC.1 hC.2.1 hC.2.2 hs.swap₂
  have hD : w₂ < u₂ ∧ w₂ < w₁ ∧ w₂ < u₁ := by
    simp only [Fin.lt_def] at hA hB hC ⊢
    omega
  rw [twoSwitch_swap₁, twoSwitch_swap₂]
  exact h i w₂ u₂ w₁ u₁ hD.1 hD.2.1 hD.2.2 hs.swap₁.swap₂

/-- Every graph reachable by 2-switches from a member of a family that is closed under 2-switches
(up to isomorphism) is isomorphic to a member. -/
theorem reach_classes (R : Fin k → SimpleGraph (Fin n))
    (hcl : ∀ i (u₁ w₁ u₂ w₂ : Fin n), IsSwitch (R i) u₁ w₁ u₂ w₂ →
      ∃ j, Nonempty (twoSwitch (R i) u₁ w₁ u₂ w₂ ≃g R j))
    {G H : SimpleGraph (Fin n)} (hGH : Reach G H) (i : Fin k) (hG : Nonempty (G ≃g R i)) :
    ∃ j, Nonempty (H ≃g R j) := by
  induction hGH with
  | refl => exact ⟨i, hG⟩
  | tail _ hst ih =>
    obtain ⟨j, ⟨φ⟩⟩ := ih
    obtain ⟨u₁, w₁, u₂, w₂, hs, rfl⟩ := isSwitch_of_step hst
    obtain ⟨j', ⟨ψ⟩⟩ := hcl j _ _ _ _ (hs.map φ)
    exact ⟨j', ⟨(twoSwitchIso φ u₁ w₁ u₂ w₂).trans ψ⟩⟩

/-- **Classification.** If `R` is closed under 2-switches (canonical form suffices), every graph
with the same degrees as `R i₀` is isomorphic to some `R j`. -/
theorem classify (R : Fin k → SimpleGraph (Fin n))
    (h : ∀ i (u₁ w₁ u₂ w₂ : Fin n), u₁ < w₁ → u₁ < u₂ → u₁ < w₂ →
      IsSwitch (R i) u₁ w₁ u₂ w₂ → ∃ j, Nonempty (twoSwitch (R i) u₁ w₁ u₂ w₂ ≃g R j))
    (i₀ : Fin k) (G : SimpleGraph (Fin n)) (hdeg : SameDeg (R i₀) G) :
    ∃ j, Nonempty (G ≃g R j) :=
  reach_classes R (closed_of_canonical R h)
    (reach_of_agree _ ∅ rfl (R i₀) G hdeg (fun s hs => absurd hs (notMem_empty s))) i₀
    ⟨SimpleGraph.Iso.refl⟩

end Canonical

end P3TS
