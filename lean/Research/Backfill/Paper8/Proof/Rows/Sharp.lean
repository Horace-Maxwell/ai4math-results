import Research.Backfill.Paper8.Proof.Rows.Members
import Research.Backfill.Paper8.Proof.Rows.Count

/-!
# Paper 8, rows: the bounds of Lemma 4.2 are attained (`Sharp_T15`, `Sharp_T18`)

`T(15)`: `R = t - 16`, `R(x²) = (x - 4)(x + 4)`, `U_15 = 0`, so a member of the leaf row of
`β = 15` has `G(±4) = ±4 + ε + Λ` and fails at the pair of `x - 4` iff
`(ε, Λ) ∈ {(1, -5), (1, 3), (-1, -3), (-1, 5)}`.
`T(18,0,0)`: `R = t² - 21t + 36`, `R(x²) = (x² + 3x - 6)(x² - 3x - 6)`, `U_18 = 0`, so
`G(θ) = θ + ε + Λ/(θ² - 18)`; on a root of `x² ± 3x - 6` (irrational, as `33` is not a square)
`G(θ) = 0` forces `(ε, Λ) = (-1, 6)` resp. `(1, -6)`, and both members do fail.
The polynomial identities follow the review scratch file `review-v2/Scratch/Sanity.lean`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge
open Polynomial hiding mirror

namespace P8Rows

theorem mem_Lset_one (β : ℕ) (Λ : ℤ) (h1 : |Λ| < β) (h2 : Even (Λ - β)) : Λ ∈ Lset β 1 :=
  ⟨fun _ => Λ, fun _ => ⟨h1.le, h2⟩, by simp, fun h => absurd h (by norm_num),
    fun _ => ⟨0, h1⟩⟩

theorem Ubeta_single {k : ℕ} (a : Fin k → ℕ) (β : ℕ)
    (h : (Bset (branchMS a)).filter (fun b => 1 ≤ b) = {β}) (t : ℝ) : Ubeta a β t = 0 := by
  unfold Ubeta Ufun
  rw [h, Finset.sum_singleton, sub_self]

/-! ### `T(15)` -/

section T15

theorem branchMS15 : branchMS (![15] : Fin 1 → ℕ) = {15} := by decide

theorem secular15 : secular {15} = X - C 16 := by
  have hB : Bset {15} = {15} := by decide
  have hk : kb {15} 15 = 1 := by decide
  apply Polynomial.funext
  intro r
  unfold secular
  rw [hB]
  simp [hk]
  ring

theorem R2_15 : R2 {15} = X ^ 2 - C 16 := by
  unfold R2
  rw [secular15]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub,
    Polynomial.expand_X, Polynomial.expand_C]
  norm_num

theorem orbit15 : IsOrbitFactor (branchMS (![15] : Fin 1 → ℕ)) (X - C 4) := by
  rw [branchMS15]
  refine ⟨Polynomial.monic_X_sub_C 4,
    Polynomial.irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C 4), ?_⟩
  rw [R2_15]
  refine ⟨X + C 4, ?_⟩
  rw [show (C 16 : ℚ[X]) = C 4 * C 4 by rw [← C_mul]; norm_num]
  ring

theorem noneven15 : ¬ IsEvenPoly (X - C (4 : ℚ)) := by
  unfold IsEvenPoly
  intro h
  have := congrArg (Polynomial.eval (1 : ℚ)) h
  simp at this
  norm_num at this

theorem isSecular15 (θ : ℝ) : IsSecular (branchMS (![15] : Fin 1 → ℕ)) θ ↔ θ ^ 2 = 16 := by
  unfold IsSecular
  rw [branchMS15, secular15]
  simp [sub_eq_zero, map_ofNat]

theorem G15 (ε Λ : ℤ) (s : TV (![15] : Fin 1 → ℕ) → ℝ)
    (hs : IsLeafRowMember (![15] : Fin 1 → ℕ) 15 ε Λ s) (θ : ℝ) (hθ : θ ^ 2 = 16) :
    Gs (![15] : Fin 1 → ℕ) s θ = θ + ε + Λ := by
  have hB : (15 : ℕ) ∈ Bset (branchMS (![15] : Fin 1 → ℕ)) := by decide
  rw [Gs_leaf _ 15 hB (by norm_num) ε Λ s hs θ ((isSecular15 θ).2 hθ),
    Ubeta_single _ 15 (by decide) _, hθ]
  norm_num

theorem fails15_iff (s : TV (![15] : Fin 1 → ℕ) → ℝ) :
    FailsAtPair (![15] : Fin 1 → ℕ) s (X - C 4) ↔
      Gs (![15] : Fin 1 → ℕ) s 4 = 0 ∨ Gs (![15] : Fin 1 → ℕ) s (-4) = 0 := by
  have hroot : ∀ θ : ℝ, θ ∈ (X - C (4 : ℚ)).rootSet ℝ ↔ θ = 4 := by
    intro θ
    rw [mem_rootSet_of_ne (X_sub_C_ne_zero 4)]
    simp [sub_eq_zero]
  constructor
  · rintro ⟨θ, hθ | hθ, hG⟩
    · rw [hroot] at hθ
      subst hθ
      exact Or.inl hG
    · rw [mem_rootSet_mirror, hroot] at hθ
      have : θ = -4 := by linarith
      subst this
      exact Or.inr hG
  · rintro (hG | hG)
    · exact ⟨4, Or.inl ((hroot 4).2 rfl), hG⟩
    · exact ⟨-4, Or.inr ((mem_rootSet_mirror _).2 ((hroot _).2 (by norm_num))), hG⟩

/-- The body of `Sharp_T15`. -/
theorem sharp_T15 (hStd : StdLeafSums) :
    IsOrbitFactor (branchMS (![15] : Fin 1 → ℕ)) (X - C 4) ∧ ¬ IsEvenPoly (X - C 4) ∧
    (∃ mem : ℤ → ℤ → TV (![15] : Fin 1 → ℕ) → ℝ,
      ∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset 15 1,
        IsLeafRowMember (![15] : Fin 1 → ℕ) 15 ε Λ (mem ε Λ)) ∧
    ∀ mem : ℤ → ℤ → TV (![15] : Fin 1 → ℕ) → ℝ,
      (∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset 15 1,
        IsLeafRowMember (![15] : Fin 1 → ℕ) 15 ε Λ (mem ε Λ)) →
      {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ Lset 15 1 ∧
        FailsAtPair (![15] : Fin 1 → ℕ) (mem p.1 p.2) (X - C 4)}.encard = 4 := by
  classical
  refine ⟨orbit15, noneven15, ?_, fun mem hmem => ?_⟩
  · have hex : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset 15 1,
        ∃ s, IsLeafRowMember (![15] : Fin 1 → ℕ) 15 ε Λ s := by
      intro ε hε Λ hΛ
      have hk : kb (branchMS (![15] : Fin 1 → ℕ)) 15 = 1 := by decide
      exact exists_leafRowMember _ hStd 15 ε hε Λ (by rw [hk]; exact hΛ)
    choose! mem hmem using hex
    exact ⟨mem, hmem⟩
  · have hmemL : ∀ Λ : ℤ, |Λ| < 15 → Even (Λ - 15) → Λ ∈ Lset 15 1 :=
      fun Λ h1 h2 => mem_Lset_one 15 Λ (by exact_mod_cast h1) (by exact_mod_cast h2)
    have hfails : ∀ ε Λ : ℤ, ε ∈ ({1, -1} : Set ℤ) → Λ ∈ Lset 15 1 →
        (FailsAtPair (![15] : Fin 1 → ℕ) (mem ε Λ) (X - C 4) ↔
          4 + ε + Λ = 0 ∨ -4 + ε + Λ = 0) := by
      intro ε Λ hε hΛ
      have hs := hmem ε hε Λ hΛ
      rw [fails15_iff, G15 ε Λ _ hs 4 (by norm_num), G15 ε Λ _ hs (-4) (by norm_num)]
      constructor
      · rintro (h | h)
        · left; exact_mod_cast h
        · right; exact_mod_cast h
      · rintro (h | h)
        · left; exact_mod_cast h
        · right; exact_mod_cast h
    have hset : {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ Lset 15 1 ∧
        FailsAtPair (![15] : Fin 1 → ℕ) (mem p.1 p.2) (X - C 4)} =
        ↑({(1, -5), (1, 3), (-1, -3), (-1, 5)} : Finset (ℤ × ℤ)) := by
      ext ⟨ε, Λ⟩
      simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨hε, hΛ, hfail⟩
        have h := (hfails ε Λ hε hΛ).1 hfail
        rcases mem_pm_iff.1 hε with rfl | rfl <;> omega
      · intro h
        have hε : ε ∈ ({1, -1} : Set ℤ) := by
          rw [mem_pm_iff]
          omega
        have hΛ : Λ ∈ Lset 15 1 := by
          refine hmemL Λ ?_ ?_
          · rw [abs_lt]
            omega
          · rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
            · exact ⟨-10, by norm_num⟩
            · exact ⟨-6, by norm_num⟩
            · exact ⟨-9, by norm_num⟩
            · exact ⟨-5, by norm_num⟩
        exact ⟨hε, hΛ, (hfails ε Λ hε hΛ).2 (by omega)⟩
    rw [hset, Set.encard_coe_eq_coe_finsetCard]
    rfl

end T15

/-! ### `T(18, 0, 0)` -/

section T18

theorem branchMS18 : branchMS (![18, 0, 0] : Fin 3 → ℕ) = {18, 0, 0} := by decide

theorem secular18 : secular {18, 0, 0} = X ^ 2 - C 21 * X + C 36 := by
  have hB : Bset {18, 0, 0} = {0, 18} := by decide
  have h0 : kb (18 ::ₘ 0 ::ₘ {0}) 0 = 2 := by decide
  have h18 : kb (18 ::ₘ 0 ::ₘ {0}) 18 = 1 := by decide
  have e18 : ({0, 18} : Finset ℕ).erase 18 = {0} := by decide
  have e0 : ({0, 18} : Finset ℕ).erase 0 = {18} := by decide
  apply Polynomial.funext
  intro r
  unfold secular
  rw [hB]
  simp [Finset.sum_insert, Finset.prod_insert, h0, h18, e0, e18]
  ring

theorem R2_18 : R2 {18, 0, 0} = (X ^ 2 + C 3 * X - C 6) * (X ^ 2 - C 3 * X - C 6) := by
  apply Polynomial.funext
  intro r
  unfold R2
  rw [secular18]
  simp [Polynomial.expand_eval]
  ring

theorem natDegree18 : (X ^ 2 + C 3 * X - C 6 : ℚ[X]).natDegree = 2 := by
  compute_degree!

theorem noneven18 : ¬ IsEvenPoly (X ^ 2 + C 3 * X - C 6 : ℚ[X]) := by
  unfold IsEvenPoly
  intro h
  have := congrArg (Polynomial.eval (1 : ℚ)) h
  simp at this
  norm_num at this

/-- `x² + 3x - 6` has no rational root (`(2x + 3)² = 33` and `33` is not a square). -/
theorem no_rat_root18 (q : ℚ) : q ^ 2 + 3 * q - 6 ≠ 0 := by
  intro hq
  have hqR : (q : ℝ) ^ 2 + 3 * q - 6 = 0 := by exact_mod_cast hq
  have hx : ((2 * q + 3 : ℚ) : ℝ) ^ 2 = ((33 : ℤ) : ℝ) := by
    push_cast
    linear_combination 4 * hqR
  have hv : ¬ ∃ y : ℤ, ((2 * q + 3 : ℚ) : ℝ) = y := by
    rintro ⟨y, hy⟩
    rw [hy] at hx
    have hy2 : y ^ 2 = 33 := by exact_mod_cast hx
    have h1 : y ≤ 6 := by nlinarith
    have h2 : -6 ≤ y := by nlinarith
    interval_cases y <;> norm_num at hy2
  exact (irrational_nrt_of_notint_nrt 2 33 hx hv two_pos) ⟨2 * q + 3, rfl⟩

theorem ne_rat18 (θ : ℝ) (hp : θ ^ 2 + 3 * θ - 6 = 0) (q : ℚ) : θ ≠ q := by
  rintro rfl
  exact no_rat_root18 q (by exact_mod_cast hp)

theorem orbit18 :
    IsOrbitFactor (branchMS (![18, 0, 0] : Fin 3 → ℕ)) (X ^ 2 + C 3 * X - C 6) := by
  rw [branchMS18]
  refine ⟨?_, ?_, ⟨X ^ 2 - C 3 * X - C 6, R2_18⟩⟩
  · monicity!
  · apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree18]
      decide
    · intro x hx
      apply no_rat_root18 x
      simpa using hx

theorem isSecular18 (θ : ℝ) :
    IsSecular (branchMS (![18, 0, 0] : Fin 3 → ℕ)) θ ↔ (θ ^ 2) ^ 2 - 21 * θ ^ 2 + 36 = 0 := by
  unfold IsSecular
  rw [branchMS18, secular18]
  simp [map_ofNat]

theorem G18 (ε Λ : ℤ) (s : TV (![18, 0, 0] : Fin 3 → ℕ) → ℝ)
    (hs : IsLeafRowMember (![18, 0, 0] : Fin 3 → ℕ) 18 ε Λ s) (θ : ℝ)
    (hθ : IsSecular (branchMS (![18, 0, 0] : Fin 3 → ℕ)) θ) :
    Gs (![18, 0, 0] : Fin 3 → ℕ) s θ = θ + ε + Λ / (θ ^ 2 - 18) := by
  have hB : (18 : ℕ) ∈ Bset (branchMS (![18, 0, 0] : Fin 3 → ℕ)) := by decide
  rw [Gs_leaf _ 18 hB (by norm_num) ε Λ s hs θ hθ, Ubeta_single _ 18 (by decide) _]
  push_cast
  ring

theorem rootSet18 (θ : ℝ) :
    θ ∈ (X ^ 2 + C 3 * X - C 6 : ℚ[X]).rootSet ℝ ↔ θ ^ 2 + 3 * θ - 6 = 0 := by
  have hne : (X ^ 2 + C 3 * X - C 6 : ℚ[X]) ≠ 0 := by
    intro h
    have := natDegree18
    rw [h, natDegree_zero] at this
    exact absurd this (by norm_num)
  rw [mem_rootSet_of_ne hne]
  simp

/-- A member of the leaf row of `18` fails at the pair of `x² + 3x - 6` iff
`(ε, Λ) = (-1, 6)` or `(1, -6)`. -/
theorem fails18_iff (ε Λ : ℤ) (s : TV (![18, 0, 0] : Fin 3 → ℕ) → ℝ)
    (hs : IsLeafRowMember (![18, 0, 0] : Fin 3 → ℕ) 18 ε Λ s) (hε : ε = 1 ∨ ε = -1) :
    FailsAtPair (![18, 0, 0] : Fin 3 → ℕ) s (X ^ 2 + C 3 * X - C 6) ↔
      (ε = -1 ∧ Λ = 6) ∨ (ε = 1 ∧ Λ = -6) := by
  constructor
  · rintro ⟨θ, hθ | hθ, hG⟩
    · rw [rootSet18] at hθ
      have hsec : IsSecular (branchMS (![18, 0, 0] : Fin 3 → ℕ)) θ := by
        rw [isSecular18]
        linear_combination (θ ^ 2 - 3 * θ - 6) * hθ
      rw [G18 ε Λ s hs θ hsec] at hG
      have hne : θ ^ 2 - 18 ≠ 0 := by
        intro h
        have : θ = -4 := by linarith
        subst this
        norm_num at hθ
      have h3 : (Λ : ℝ) / (θ ^ 2 - 18) * (θ ^ 2 - 18) = Λ := div_mul_cancel₀ _ hne
      have h2 : ((θ + ε) * (θ ^ 2 - 18) + Λ : ℝ) = 0 := by
        linear_combination (θ ^ 2 - 18) * hG - h3
      have h4 : -3 * (1 + (ε : ℝ)) * θ + (Λ - 18 - 12 * ε) = 0 := by
        linear_combination h2 - (θ + ε - 3) * hθ
      rcases hε with rfl | rfl
      · exfalso
        apply ne_rat18 θ hθ ((Λ - 30) / 6)
        push_cast at h4 ⊢
        linarith
      · left
        refine ⟨rfl, ?_⟩
        push_cast at h4
        have : (Λ : ℝ) = 6 := by linarith
        exact_mod_cast this
    · rw [mem_rootSet_mirror, rootSet18] at hθ
      have hq : θ ^ 2 - 3 * θ - 6 = 0 := by linear_combination hθ
      have hsec : IsSecular (branchMS (![18, 0, 0] : Fin 3 → ℕ)) θ := by
        rw [isSecular18]
        linear_combination (θ ^ 2 + 3 * θ - 6) * hq
      rw [G18 ε Λ s hs θ hsec] at hG
      have hne : θ ^ 2 - 18 ≠ 0 := by
        intro h
        have : θ = 4 := by linarith
        subst this
        norm_num at hq
      have h3 : (Λ : ℝ) / (θ ^ 2 - 18) * (θ ^ 2 - 18) = Λ := div_mul_cancel₀ _ hne
      have h2 : ((θ + ε) * (θ ^ 2 - 18) + Λ : ℝ) = 0 := by
        linear_combination (θ ^ 2 - 18) * hG - h3
      have h4 : 3 * ((ε : ℝ) - 1) * θ + (18 - 12 * ε + Λ) = 0 := by
        linear_combination h2 - (θ + ε + 3) * hq
      rcases hε with rfl | rfl
      · right
        refine ⟨rfl, ?_⟩
        push_cast at h4
        have : (Λ : ℝ) = -6 := by linarith
        exact_mod_cast this
      · exfalso
        apply ne_rat18 (-θ) hθ (-(30 + Λ) / 6)
        push_cast at h4 ⊢
        linarith
  · have hr : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · set θ := (-3 + Real.sqrt 33) / 2 with hθdef
      have hp : θ ^ 2 + 3 * θ - 6 = 0 := by
        rw [hθdef]
        linear_combination (1 / 4 : ℝ) * hr
      have hsec : IsSecular (branchMS (![18, 0, 0] : Fin 3 → ℕ)) θ := by
        rw [isSecular18]
        linear_combination (θ ^ 2 - 3 * θ - 6) * hp
      have hne : θ ^ 2 - 18 ≠ 0 := by
        intro h
        have : θ = -4 := by linarith
        rw [this] at hp
        norm_num at hp
      refine ⟨θ, Or.inl ((rootSet18 θ).2 hp), ?_⟩
      rw [G18 _ _ s hs θ hsec]
      have h6 : (6 : ℝ) / (θ ^ 2 - 18) = -(θ - 1) := by
        rw [div_eq_iff hne]
        linear_combination (θ - 4) * hp
      push_cast
      rw [h6]
      ring
    · set θ := (3 + Real.sqrt 33) / 2 with hθdef
      have hq : θ ^ 2 - 3 * θ - 6 = 0 := by
        rw [hθdef]
        linear_combination (1 / 4 : ℝ) * hr
      have hsec : IsSecular (branchMS (![18, 0, 0] : Fin 3 → ℕ)) θ := by
        rw [isSecular18]
        linear_combination (θ ^ 2 + 3 * θ - 6) * hq
      have hne : θ ^ 2 - 18 ≠ 0 := by
        intro h
        have : θ = 4 := by linarith
        rw [this] at hq
        norm_num at hq
      refine ⟨θ, Or.inr ((mem_rootSet_mirror θ).2 ((rootSet18 (-θ)).2 (by
        linear_combination hq))), ?_⟩
      rw [G18 _ _ s hs θ hsec]
      have h6 : (-6 : ℝ) / (θ ^ 2 - 18) = -(θ + 1) := by
        rw [div_eq_iff hne]
        linear_combination (θ + 4) * hq
      push_cast
      rw [h6]
      ring

/-- The body of `Sharp_T18`. -/
theorem sharp_T18 (hStd : StdLeafSums) :
    IsOrbitFactor (branchMS (![18, 0, 0] : Fin 3 → ℕ)) (X ^ 2 + C 3 * X - C 6) ∧
    ¬ IsEvenPoly (X ^ 2 + C 3 * X - C 6) ∧ (X ^ 2 + C 3 * X - C 6 : ℚ[X]).natDegree ≠ 1 ∧
    (∃ mem : ℤ → ℤ → TV (![18, 0, 0] : Fin 3 → ℕ) → ℝ,
      ∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset 18 1,
        IsLeafRowMember (![18, 0, 0] : Fin 3 → ℕ) 18 ε Λ (mem ε Λ)) ∧
    ∀ mem : ℤ → ℤ → TV (![18, 0, 0] : Fin 3 → ℕ) → ℝ,
      (∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset 18 1,
        IsLeafRowMember (![18, 0, 0] : Fin 3 → ℕ) 18 ε Λ (mem ε Λ)) →
      {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ Lset 18 1 ∧
        FailsAtPair (![18, 0, 0] : Fin 3 → ℕ) (mem p.1 p.2)
          (X ^ 2 + C 3 * X - C 6)}.encard = 2 := by
  classical
  refine ⟨orbit18, noneven18, by rw [natDegree18]; norm_num, ?_, fun mem hmem => ?_⟩
  · have hex : ∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset 18 1,
        ∃ s, IsLeafRowMember (![18, 0, 0] : Fin 3 → ℕ) 18 ε Λ s := by
      intro ε hε Λ hΛ
      have hk : kb (branchMS (![18, 0, 0] : Fin 3 → ℕ)) 18 = 1 := by decide
      exact exists_leafRowMember _ hStd 18 ε hε Λ (by rw [hk]; exact hΛ)
    choose! mem hmem using hex
    exact ⟨mem, hmem⟩
  · have hset : {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ Lset 18 1 ∧
        FailsAtPair (![18, 0, 0] : Fin 3 → ℕ) (mem p.1 p.2) (X ^ 2 + C 3 * X - C 6)} =
        {((-1 : ℤ), (6 : ℤ)), ((1 : ℤ), (-6 : ℤ))} := by
      ext ⟨ε, Λ⟩
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨hε, hΛ, hfail⟩
        exact (fails18_iff ε Λ _ (hmem ε hε Λ hΛ) (mem_pm_iff.1 hε)).1 hfail
      · intro h
        have hε : ε ∈ ({1, -1} : Set ℤ) := by
          rw [mem_pm_iff]
          omega
        have hΛ : Λ ∈ Lset 18 1 := by
          rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact mem_Lset_one 18 6 (by norm_num) ⟨-6, by norm_num⟩
          · exact mem_Lset_one 18 (-6) (by norm_num) ⟨-12, by norm_num⟩
        exact ⟨hε, hΛ, (fails18_iff ε Λ _ (hmem ε hε Λ hΛ) (mem_pm_iff.1 hε)).2 h⟩
    rw [hset, Set.encard_pair (by decide)]

end T18

end P8Rows
