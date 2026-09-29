import Research.Backfill.Paper3.Proof.B.Switch

/-!
# `S_3` is the prism and `H_2` is `C_8`

Every labelling is reduced to one by an automorphism of `K_{d,d}` (resp. of `2 K_{2,2}`) that
moves the chosen vertices (`twoSwitchIso`); for that labelling an explicit bijection is checked
to be an isomorphism by `decide`.
-/

set_option autoImplicit false

namespace P3B

open SimpleGraph BackfillPaper3.Challenge

/-- `S_3` with labels `x₁ = 0, x₂ = 1, y₁ = 0, y₂ = 1` is the prism: the triangles
`{x₀, x₁, y₂}` and `{y₀, y₁, x₂}` with the matching `x₀y₁, x₁y₀, y₂x₂`. -/
noncomputable def sdPrismIso : Sd 3 0 1 0 1 ≃g prism where
  toEquiv := Equiv.ofBijective (Sum.elim ![(0, 0), (1, 0), (2, 1)] ![(1, 1), (0, 1), (2, 0)])
    (by decide)
  map_rel_iff' := fun {a b} => by
    revert a b
    decide

/-- `H_2` with all labels `0` is the 8-cycle `y₀ x₁ y₁ x₀ Y₀ X₁ Y₁ X₀`. -/
noncomputable def hdCycleIso : Hd 2 0 0 0 0 ≃g cycleGraph 8 where
  toEquiv := Equiv.ofBijective
    (fun p : Fin 2 × (Fin 2 ⊕ Fin 2) =>
      ![Sum.elim ![3, 1] ![0, 2], Sum.elim ![7, 5] ![4, 6]] p.1 p.2) (by decide)
  map_rel_iff' := fun {a b} => by
    revert a b
    decide

theorem s3PrismH2Cycle : S3PrismH2Cycle := by
  refine ⟨fun a₁ a₂ b₁ b₂ ha hb => ?_, fun a₁ b₁ a₂ b₂ => ?_⟩
  · obtain ⟨σ, hσ1, hσ2⟩ := exists_perm_pair ha (show (0 : Fin 3) ≠ 1 by decide)
    obtain ⟨τ, hτ1, hτ2⟩ := exists_perm_pair hb (show (0 : Fin 3) ≠ 1 by decide)
    obtain ⟨e⟩ := nonempty_twoSwitch_iso (kddIso σ τ) (u₁ := .inl a₁) (w₁ := .inr b₁)
      (u₂ := .inr b₂) (w₂ := .inl a₂) (u₁' := .inl 0) (w₁' := .inr 0) (u₂' := .inr 1)
      (w₂' := .inl 1)
      (by simp [kddIso, hσ1]) (by simp [kddIso, hτ1]) (by simp [kddIso, hτ2])
      (by simp [kddIso, hσ2])
    exact ⟨e.trans sdPrismIso⟩
  · let ψ : Fin 2 → (Kdd 2 ≃g Kdd 2) :=
      ![kddIso (Equiv.swap a₁ 0) (Equiv.swap b₁ 0), kddIso (Equiv.swap a₂ 0) (Equiv.swap b₂ 0)]
    obtain ⟨e⟩ := nonempty_twoSwitch_iso (copiesIso ψ) (u₁ := (0, .inl a₁)) (w₁ := (0, .inr b₁))
      (u₂ := (1, .inl a₂)) (w₂ := (1, .inr b₂)) (u₁' := (0, .inl 0)) (w₁' := (0, .inr 0))
      (u₂' := (1, .inl 0)) (w₂' := (1, .inr 0))
      (by simp [copiesIso, kddIso, ψ]) (by simp [copiesIso, kddIso, ψ])
      (by simp [copiesIso, kddIso, ψ]) (by simp [copiesIso, kddIso, ψ])
    exact ⟨e.trans hdCycleIso⟩

end P3B
