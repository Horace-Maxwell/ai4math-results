import Research.Backfill.Paper7.ChallengeV2

/-! Exact coordinate and orbit helpers for the first three conjuncts of
the frozen C61OrbitSix contract. The fourth, arbitrary-parameter spectral
classification conjunct is unresolved and is not claimed by this module.
This source has not been compiled. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7C61Orbit

open BackfillPaper7.Challenge

theorem c61_parameters : C61 = pq 6 C61P (fun _ => 0) := by
  funext k
  fin_cases k <;> rfl

#print axioms Paper7C61Orbit.c61_parameters

/-- The actual frozen permutation power is translation on all six indices. -/
theorem rotationPower_apply (c k : Fin 6) :
    ((finRotate 6) ^ c.val) k = k + c := by
  fin_cases c <;> fin_cases k <;> decide

#print axioms Paper7C61Orbit.rotationPower_apply

def rotationParameter (c : Fin 6) : Fin 6 → ℕ :=
  fun k => C61P (k + c)

#print axioms Paper7C61Orbit.rotationParameter

/-- The actual six entries are symmetric under reflection through index zero. -/
theorem c61P_neg (k : Fin 6) : C61P (-k) = C61P k := by
  fin_cases k <;> decide

#print axioms Paper7C61Orbit.c61P_neg

/-- The unique zero entry distinguishes all six rotations. -/
theorem c61P_zero_iff (k : Fin 6) : C61P k = 0 ↔ k = 0 := by
  fin_cases k <;> decide

#print axioms Paper7C61Orbit.c61P_zero_iff

theorem rotations_eq_image :
    C61Rotations = Finset.univ.image rotationParameter := by
  unfold C61Rotations
  apply Finset.image_congr
  intro c _hc
  funext k
  exact congrArg C61P (rotationPower_apply c k)

#print axioms Paper7C61Orbit.rotations_eq_image

theorem mem_rotations_iff (p : Fin 6 → ℕ) :
    p ∈ C61Rotations ↔ ∃ c : Fin 6, p = rotationParameter c := by
  rw [rotations_eq_image]
  constructor
  · intro hp
    obtain ⟨c, _hc, hcp⟩ := Finset.mem_image.mp hp
    exact ⟨c, hcp.symm⟩
  · rintro ⟨c, rfl⟩
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩

#print axioms Paper7C61Orbit.mem_rotations_iff

theorem rotationParameter_injective : Function.Injective rotationParameter := by
  intro a b hab
  have hcoord := congrFun hab (-a)
  change C61P (-a + a) = C61P (-a + b) at hcoord
  have hzero : C61P (-a + b) = 0 := by
    rw [← hcoord]
    simp [C61P]
  have hindex : -a + b = 0 := (c61P_zero_iff _).mp hzero
  have hcancel : -a + b = -a + a := by
    simpa only [neg_add_cancel] using hindex
  exact (add_left_cancel hcancel).symm

#print axioms Paper7C61Orbit.rotationParameter_injective

theorem rotations_card : C61Rotations.card = 6 := by
  rw [rotations_eq_image,
    Finset.card_image_of_injective _ rotationParameter_injective,
    Finset.card_univ, Fintype.card_fin]

#print axioms Paper7C61Orbit.rotations_card

/-- The frozen natural-number definition has exactly the two affine forms.
The natural shift is reduced modulo six; no bijectivity premise is added. -/
theorem isDihedral_six_affine (σ : Fin 6 → Fin 6) (hσ : IsDihedral 6 σ) :
    (∃ c : Fin 6, ∀ k, σ k = k + c) ∨
      (∃ c : Fin 6, ∀ k, σ k = c - k) := by
  obtain ⟨c, hr | hf⟩ := hσ
  · apply Or.inl
    refine ⟨⟨c % 6, Nat.mod_lt _ (by decide)⟩, ?_⟩
    intro k
    apply Fin.ext
    change (σ k).val = (k.val + c % 6) % 6
    rw [hr]
    simp only [Nat.add_mod, Nat.mod_mod]
  · apply Or.inr
    refine ⟨⟨c % 6, Nat.mod_lt _ (by decide)⟩, ?_⟩
    intro k
    apply eq_sub_iff_add_eq.mpr
    apply Fin.ext
    change ((σ k).val + k.val) % 6 = c % 6
    exact hf k

#print axioms Paper7C61Orbit.isDihedral_six_affine

theorem translation_isDihedral (c : Fin 6) :
    IsDihedral 6 (fun k : Fin 6 => k + c) := by
  refine ⟨c.val, Or.inl ?_⟩
  intro k
  exact Fin.val_add k c

#print axioms Paper7C61Orbit.translation_isDihedral

/-- Reflection creates no new parameter tuple because C61P is reflection
symmetric; both implications quantify over the original labeled functions. -/
theorem dihedral_orbit_iff (p : Fin 6 → ℕ) :
    (∃ σ : Fin 6 → Fin 6, IsDihedral 6 σ ∧ p = C61P ∘ σ) ↔
      p ∈ C61Rotations := by
  constructor
  · rintro ⟨σ, hσ, hp⟩
    rcases isDihedral_six_affine σ hσ with ⟨c, hc⟩ | ⟨c, hc⟩
    · apply (mem_rotations_iff p).mpr
      refine ⟨c, ?_⟩
      funext k
      rw [hp]
      change C61P (σ k) = C61P (k + c)
      rw [hc k]
    · apply (mem_rotations_iff p).mpr
      refine ⟨-c, ?_⟩
      funext k
      rw [hp]
      change C61P (σ k) = C61P (k + -c)
      rw [hc k]
      have hneg : c - k = -(k + -c) := by abel
      rw [hneg, c61P_neg]
  · intro hp
    obtain ⟨c, hc⟩ := (mem_rotations_iff p).mp hp
    exact ⟨fun k => k + c, translation_isDihedral c, hc⟩

#print axioms Paper7C61Orbit.dihedral_orbit_iff

/-- Only the first three conjuncts of C61OrbitSix. The arbitrary p,q
classification in its fourth conjunct is not asserted here. -/
theorem c61_orbit_first_three :
    C61 = pq 6 C61P (fun _ => 0) ∧
    (∀ p : Fin 6 → ℕ,
      (∃ σ : Fin 6 → Fin 6, IsDihedral 6 σ ∧ p = C61P ∘ σ) ↔
        p ∈ C61Rotations) ∧
    C61Rotations.card = 6 := by
  exact ⟨c61_parameters, dihedral_orbit_iff, rotations_card⟩

#print axioms Paper7C61Orbit.c61_orbit_first_three

end Paper7C61Orbit
