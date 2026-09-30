import Research.Backfill.Paper8.Proof.Tests.Switch

/-!
# Paper 8, known-answer tests (agent `tests`): conditions (S), (L), (Z), failing, the two rows

Tests of `condS`, `condL`, `condZ`, `FailsAtOrbit`, `FailsAtPair`, `IsLeafRowMember` and
`IsBareRowMember`, each with instances that hold and instances that fail: the switchings of
Proposition 5.6, the all-ones switchings of `K_2 = T(0)`, `K_{1,2} = T(0,0)`, `T(2)` and `T(2,2)`,
the switching of Proposition 5.1(a) for `K_{1,2}`, and two further switchings `sL3` of `T(3)` and
`sB` of `T(2,0,0)`.
-/

set_option autoImplicit false

open BackfillPaper8 BackfillPaper8.Challenge Matrix
open Polynomial hiding mirror

namespace P8Tests

/-! ## Three more switchings -/

/-- `T(3)`: `s_c = σ_1 = 1`, leaves `+1, +1, -1`, so `λ_1 = 1` (the member `s_{1,1}` of the leaf
row of `β = 3`, next to `sw56c = s_{1,-1}`). -/
def sL3 : TV (![3] : Fin 1 → ℕ) → ℝ :=
  mkSw ![3] 1 (fun _ => 1) (fun _ j => if j.val = 2 then -1 else 1)

/-- `K_{1,2} = T(0,0)`, Proposition 5.1(a) with `k_0 = 2`: `s_c = 1`, `-1` on the leaf `v_1`. -/
def s00 : TV (![0, 0] : Fin 2 → ℕ) → ℝ :=
  mkSw ![0, 0] 1 (fun i => if i = 0 then -1 else 1) (fun _ _ => 1)

/-- `T(2,0,0)`: `s_c = 1`; `σ_1 = 1` and leaves `+1, -1` (leaf sum `λ°_1 = 0`) on the branch of
size 2; `σ_2 = -1`, `σ_3 = 1` on the two bare branches: the member `s_{1,1}` of the bare row. -/
def sB : TV (![2, 0, 0] : Fin 3 → ℕ) → ℝ :=
  mkSw ![2, 0, 0] 1 (fun i => if i = 1 then -1 else 1) (fun _ j => if j.val = 0 then 1 else -1)

theorem isSwitching_56c : IsSwitching sw56c :=
  isSwitching_mkSw _ (Or.inl rfl) (fun _ => Or.inl rfl) (fun _ j => ite_pm (j.val = 0))

theorem isSwitching_sL3 : IsSwitching sL3 :=
  isSwitching_mkSw _ (Or.inl rfl) (fun _ => Or.inl rfl) (fun _ j => ite_mp (j.val = 2))

theorem isSwitching_s00 : IsSwitching s00 :=
  isSwitching_mkSw _ (Or.inl rfl) (fun i => ite_mp (i = 0)) (fun _ _ => Or.inl rfl)

theorem isSwitching_sB : IsSwitching sB :=
  isSwitching_mkSw _ (Or.inl rfl) (fun i => ite_mp (i = 1)) (fun _ j => ite_pm (j.val = 0))

theorem lam_sL3 : lam (![3] : Fin 1 → ℕ) sL3 0 = 1 := by
  simp only [lam, sL3, mkSw]
  rw [Fin.sum_univ_eq_sum_range (fun n => if n = 2 then (-1 : ℝ) else 1)]
  norm_num [Finset.sum_range_succ]

-- `G(θ) = (A_3 + S_3 θ)/(t - 3) = (2 + θ)/(θ² - 3)` for `sL3`: `G(2) = 4`, `G(-2) = 0`
theorem Gs_sL3 (θ : ℝ) : Gs (![3] : Fin 1 → ℕ) sL3 θ = (2 + θ) / (θ ^ 2 - 3) := by
  rw [Gs_T3, Ab_T3, Sb_T3, lam_sL3]
  simp only [sc, sig, sL3, mkSw]
  norm_num

theorem isSecular_T3 (θ : ℝ) : IsSecular (branchMS (![3] : Fin 1 → ℕ)) θ ↔ θ ^ 2 = 4 := by
  unfold IsSecular
  rw [show branchMS (![3] : Fin 1 → ℕ) = {3} by decide, test_secular_3]
  simp [sub_eq_zero, map_ofNat]

theorem mem_rootSet_X_sub_C (c : ℚ) (θ : ℝ) : θ ∈ (X - C c).rootSet ℝ ↔ θ = c := by
  rw [mem_rootSet_of_ne (X_sub_C_ne_zero c)]
  simp [sub_eq_zero, eq_ratCast]

theorem mem_rootSet_X_add_C (c : ℚ) (θ : ℝ) : θ ∈ (X + C c).rootSet ℝ ↔ θ = -c := by
  rw [mem_rootSet_of_ne (X_add_C_ne_zero c)]
  simp [eq_neg_iff_add_eq_zero, eq_ratCast]

/-! ## `condS` -/

-- Prop 5.6(c), proof: (S) holds for `sw56c` ("G = θ ≠ 0" at the secular `θ = ±2`)
theorem test_condS_56c : condS (![3] : Fin 1 → ℕ) sw56c := by
  intro θ hθ
  rw [isSecular_T3] at hθ
  rw [Gs_56c, hθ]
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    norm_num at hθ
  norm_num [hθ0]

-- Prop 5.6(a), (b), proofs: (S) holds for `sw56a` (`G ∈ {3, -1}` at `θ = ±2`) and for `sw56b`
-- (`G = 4, -2, 1, 1` at `θ = 1, -1, 2, -2`)
theorem test_condS_56a : condS (![2, 2] : Fin 2 → ℕ) sw56a := by
  intro θ hθ
  rw [test_isSecular_22] at hθ
  have h : (θ - 2) * (θ + 2) = 0 := by linear_combination hθ
  rcases mul_eq_zero.1 h with h | h
  · rw [show θ = 2 by linarith, test_Gs_56a.1]
    norm_num
  · rw [show θ = -2 by linarith, test_Gs_56a.2]
    norm_num

theorem test_condS_56b : condS (![2, 0, 0] : Fin 3 → ℕ) sw56b := by
  intro θ hθ
  rw [test_isSecular_200] at hθ
  rcases hθ with hθ | hθ
  · have h : (θ - 1) * (θ + 1) = 0 := by linear_combination hθ
    rcases mul_eq_zero.1 h with h | h
    · rw [show θ = 1 by linarith, test_Gs_56b.1]
      norm_num
    · rw [show θ = -1 by linarith, test_Gs_56b.2.1]
      norm_num
  · have h : (θ - 2) * (θ + 2) = 0 := by linear_combination hθ
    rcases mul_eq_zero.1 h with h | h
    · rw [show θ = 2 by linarith, test_Gs_56b.2.2.1]
      norm_num
    · rw [show θ = -2 by linarith, test_Gs_56b.2.2.2]
      norm_num

-- FALSE: (S) fails for `sL3`: `G(-2) = 0`
theorem test_not_condS_sL3 : ¬ condS (![3] : Fin 1 → ℕ) sL3 := by
  intro h
  apply h (-2) ((isSecular_T3 _).2 (by norm_num))
  rw [Gs_sL3]
  norm_num

-- FALSE: `K_2 = T(0)` is excluded from Theorem 1: `R = t - 1`, and for the all-ones switching
-- `G(θ) = (A_0 + S_0 θ)/t = (1 + θ)/θ²` vanishes at the secular `θ = -1`
theorem test_not_condS_K2 : ¬ condS (![0] : Fin 1 → ℕ) (fun _ => 1) := by
  intro h
  have hk : kb (branchMS (![0] : Fin 1 → ℕ)) 0 = 1 := by decide
  have hI : Ib (![0] : Fin 1 → ℕ) 0 = {0} := by decide
  have hB : Bset (branchMS (![0] : Fin 1 → ℕ)) = {0} := by decide
  have hlam : lam (![0] : Fin 1 → ℕ) (fun _ => 1) 0 = 0 := by
    simp only [lam]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  apply h (-1)
  · unfold IsSecular
    rw [secular_of_Bset_eq_singleton hB, hk]
    simp
  · unfold Gs
    rw [hB, Finset.sum_singleton]
    simp only [Challenge.Ab, Sb, Lamb, hI, hk, Finset.sum_singleton, hlam, sc, sig]
    norm_num

/-! ## `condL` -/

-- Prop 5.6(a), proof: "For (L), at θ = ±√2 the numbers 1 + 2/θ and 1 - 2/θ differ"
theorem test_condL_56a : condL (![2, 2] : Fin 2 → ℕ) sw56a := by
  intro b hb _ _ θ hθ
  rw [Bset_22, Finset.mem_singleton] at hb
  subst hb
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    norm_num at hθ
  refine ⟨0, by decide, 1, by decide, ?_⟩
  rw [test_lam_56a.1, test_lam_56a.2, ← sub_ne_zero]
  simp only [sig, sw56a, mkSw]
  rw [show (1 + 2 / θ) - (1 + -2 / θ) = 4 / θ by ring]
  exact div_ne_zero (by norm_num) hθ0

-- FALSE: for the all-ones switching of `T(2,2)` both numbers are `1 + 2/θ`
theorem test_not_condL_22 : ¬ condL (![2, 2] : Fin 2 → ℕ) (fun _ => 1) := by
  intro h
  have hlam : ∀ i : Fin 2, lam (![2, 2] : Fin 2 → ℕ) (fun _ => 1) i = 2 := by
    intro i
    simp only [lam]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    fin_cases i <;> norm_num
  obtain ⟨i, -, i', -, hne⟩ :=
    h 2 (by decide) (by norm_num) (by decide) (Real.sqrt 2) (by norm_num)
  apply hne
  rw [hlam i, hlam i']
  rfl

/-! ## `condZ` -/

-- Prop 5.6(a), proof: "(Z): k_0 = 0 and the leaf signs are constant on each branch, with
-- ∑ ε_i = 0 ≠ 1 = s_c"
theorem test_condZ_56a : condZ (![2, 2] : Fin 2 → ℕ) sw56a := by
  intro _
  have hk : kb (branchMS (![2, 2] : Fin 2 → ℕ)) 0 = 0 := by decide
  refine ⟨fun h => by omega, fun _ => Or.inr ?_⟩
  rw [Fin.sum_univ_two, test_lam_56a.1, test_lam_56a.2]
  simp only [sc, sw56a, mkSw]
  norm_num

-- Prop 5.6(b), (c), proofs: "(L) is void, and (Z) holds because the leaves of v have both signs"
-- (for `T(2,0,0)`, `k_0 = 2`; for `T(3)`, `k_0 = 0`)
theorem test_condL_56b : condL (![2, 0, 0] : Fin 3 → ℕ) sw56b := by
  intro b hb hb1 hb2
  exfalso
  rw [Bset_200] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · omega
  · exact absurd hb2 (by decide)

theorem test_condZ_56b : condZ (![2, 0, 0] : Fin 3 → ℕ) sw56b := by
  intro _
  refine ⟨fun _ => Or.inl ⟨0, by decide, ⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩,
    fun h => absurd h (by decide)⟩
  simp only [sw56b, mkSw]
  norm_num

theorem test_condL_56c : condL (![3] : Fin 1 → ℕ) sw56c := by
  intro b hb _ hb2
  rw [Bset_3, Finset.mem_singleton] at hb
  subst hb
  exact absurd hb2 (by decide)

theorem test_condZ_56c : condZ (![3] : Fin 1 → ℕ) sw56c := by
  intro _
  refine ⟨fun h => absurd h (by decide), fun _ => Or.inl ⟨0, ⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩⟩
  simp only [sw56c, mkSw]
  norm_num

-- Prop 5.1(a), `k_0 = 2`: (Z) holds for `s00` (`σ_1 = -1 ≠ 1 = σ_2` on `I_0`)
theorem test_condZ_s00 : condZ (![0, 0] : Fin 2 → ℕ) s00 := by
  intro _
  refine ⟨fun _ => Or.inr ⟨0, by decide, 1, by decide, ?_⟩, fun h => absurd h (by decide)⟩
  simp only [sig, s00, mkSw]
  norm_num

-- FALSE: the all-ones switching of `K_{1,2} = T(0,0)`: `0` is an eigenvalue (`e_{v_1} - e_{v_2}`),
-- `k_0 = 2`, no branch has two leaves, and `σ_1 = σ_2`
theorem test_not_condZ_00 : ¬ condZ (![0, 0] : Fin 2 → ℕ) (fun _ => 1) := by
  intro h
  have hz : ∀ i : Fin 2, (![0, 0] : Fin 2 → ℕ) i = 0 := by decide
  have hker : ∃ x : TV (![0, 0] : Fin 2 → ℕ) → ℝ, x ≠ 0 ∧ adjT (![0, 0] : Fin 2 → ℕ) *ᵥ x = 0 := by
    refine ⟨mkSw _ 0 ![1, -1] (fun _ _ => 0), ?_, ?_⟩
    · intro h0
      have := congrFun h0 (some ⟨0, none⟩)
      simp only [mkSw_v] at this
      norm_num at this
    · rw [adjT_mulVec_mkSw, zero_eq_mkSw, mkSw_eq_iff]
      refine ⟨by simp [Fin.sum_univ_two], fun i => by simp, fun i j => ?_⟩
      exfalso
      have h1 := j.isLt
      have h2 := hz i
      omega
  obtain ⟨h1, -⟩ := h hker
  rcases h1 (by decide) with ⟨i, hi, -⟩ | ⟨i, -, i', -, hne⟩
  · have := hz i
    omega
  · exact hne rfl

-- FALSE: the all-ones switching of `T(2)` (`k_0 = 0`): `e_{ℓ_1} - e_{ℓ_2} ∈ ker A`, the leaves have
-- one sign, and `s_c = 1 = ε_1 = λ_1/a_1`
theorem test_not_condZ_2 : ¬ condZ (![2] : Fin 1 → ℕ) (fun _ => 1) := by
  intro h
  have hsum : ∀ i : Fin 1,
      ∑ j : Fin ((![2] : Fin 1 → ℕ) i), (if j.val = 0 then (1 : ℝ) else -1) = 0 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun n => if n = 0 then (1 : ℝ) else -1)]
    norm_num [Finset.sum_range_succ]
  have hker : ∃ x : TV (![2] : Fin 1 → ℕ) → ℝ, x ≠ 0 ∧ adjT (![2] : Fin 1 → ℕ) *ᵥ x = 0 := by
    refine ⟨mkSw _ 0 (fun _ => 0) (fun _ j => if j.val = 0 then 1 else -1), ?_, ?_⟩
    · intro h0
      have := congrFun h0 (some ⟨0, some ⟨0, by decide⟩⟩)
      simp only [mkSw_l] at this
      norm_num at this
    · rw [adjT_mulVec_mkSw, zero_eq_mkSw, mkSw_eq_iff]
      refine ⟨by simp, fun i => ?_, fun i j => rfl⟩
      rw [hsum i, add_zero]
  obtain ⟨-, h2⟩ := h hker
  rcases h2 (by decide) with ⟨i, j, j', hne⟩ | hne
  · exact hne rfl
  · apply hne
    rw [Fin.sum_univ_one]
    simp only [sc, lam]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num

/-! ## `FailsAtOrbit`, `FailsAtPair` -/

-- Section 3, "s fails at an orbit O if G_s(θ) = 0 for some θ ∈ O": `sL3` fails at the orbit
-- `{-2}` of `x + 2` but not at the orbit `{2}` of `x - 2`, and so it fails at their pair
theorem test_failsAtOrbit_sL3 : FailsAtOrbit (![3] : Fin 1 → ℕ) sL3 (X + C 2) := by
  refine ⟨-2, (mem_rootSet_X_add_C 2 _).2 (by norm_num), ?_⟩
  rw [Gs_sL3]
  norm_num

theorem test_not_failsAtOrbit_sL3 : ¬ FailsAtOrbit (![3] : Fin 1 → ℕ) sL3 (X - C 2) := by
  rintro ⟨θ, hθ, hG⟩
  rw [mem_rootSet_X_sub_C] at hθ
  rw [hθ, Gs_sL3] at hG
  norm_num at hG

theorem test_failsAtPair_sL3 : FailsAtPair (![3] : Fin 1 → ℕ) sL3 (X - C 2) := by
  refine ⟨-2, Or.inr ?_, ?_⟩
  · rw [P8Orb.mirror_X_sub_C, mem_rootSet_X_add_C]
    norm_num
  · rw [Gs_sL3]
    norm_num

-- Prop 5.6(c): `sw56c` fails at neither orbit of the integer pair `x ∓ 2` of `T(3)` (`G(±2) = ±2`)
theorem test_not_failsAtPair_56c : ¬ FailsAtPair (![3] : Fin 1 → ℕ) sw56c (X - C 2) := by
  rintro ⟨θ, hθ | hθ, hG⟩
  · rw [mem_rootSet_X_sub_C] at hθ
    rw [hθ, Gs_56c] at hG
    norm_num at hG
  · rw [P8Orb.mirror_X_sub_C, mem_rootSet_X_add_C] at hθ
    rw [hθ, Gs_56c] at hG
    norm_num at hG

/-! ## `IsLeafRowMember` (Lemma 4.2) -/

-- Lemma 4.2 for `T(3)`, `β = 3` (`ℒ_3(1) = {±1}`): `sw56c` is the member `s_{1,-1}`
theorem test_leafRow_56c : IsLeafRowMember (![3] : Fin 1 → ℕ) 3 1 (-1) sw56c := by
  refine ⟨isSwitching_56c, by simp only [sc, sw56c, mkSw]; norm_num, fun i => rfl,
    fun i _ h2 => absurd (by revert i; decide) h2, ?_, fun h => absurd h (by decide),
    fun _ => ⟨0, by decide, ?_⟩⟩
  · rw [Ib_3, Finset.sum_singleton, lam_56c]
    norm_num
  · rw [lam_56c]
    norm_num

-- ... and `sL3` is the member `s_{1,1}`
theorem test_leafRow_sL3 : IsLeafRowMember (![3] : Fin 1 → ℕ) 3 1 1 sL3 := by
  refine ⟨isSwitching_sL3, by simp only [sc, sL3, mkSw]; norm_num, fun i => rfl,
    fun i _ h2 => absurd (by revert i; decide) h2, ?_, fun h => absurd h (by decide),
    fun _ => ⟨0, by decide, ?_⟩⟩
  · rw [Ib_3, Finset.sum_singleton, lam_sL3]
    norm_num
  · rw [lam_sL3]
    norm_num

-- FALSE: `sL3` is not `s_{-1,1}` (`s_c = 1`) and not `s_{1,-1}` (`Λ = λ_1 = 1`)
theorem test_not_leafRow_sL3 : ¬ IsLeafRowMember (![3] : Fin 1 → ℕ) 3 (-1) 1 sL3 ∧
    ¬ IsLeafRowMember (![3] : Fin 1 → ℕ) 3 1 (-1) sL3 := by
  constructor
  · rintro ⟨-, h, -⟩
    simp only [sc, sL3, mkSw] at h
    norm_num at h
  · rintro ⟨-, -, -, -, h, -⟩
    rw [Ib_3, Finset.sum_singleton, lam_sL3] at h
    norm_num at h

-- FALSE: `sw56a` is in no leaf row of `β = 2` of `T(2,2)`: its leaf sums `2, -2` on `I_2` all have
-- `|λ_i| = 2`, while a member needs `|λ_i| < 2` for some `i ∈ I_2` (as `0 ∉ ℒ_2(2)`)
theorem test_not_leafRow_56a (ε Λ : ℤ) : ¬ IsLeafRowMember (![2, 2] : Fin 2 → ℕ) 2 ε Λ sw56a := by
  rintro ⟨-, -, -, -, -, -, h⟩
  obtain ⟨i, -, hi⟩ := h le_rfl
  have habs : ∀ i : Fin 2, |lam (![2, 2] : Fin 2 → ℕ) sw56a i| = 2 := by
    rw [Fin.forall_fin_two, test_lam_56a.1, test_lam_56a.2]
    norm_num
  rw [habs i] at hi
  norm_num at hi

/-! ## `IsBareRowMember` (Lemma 4.3) -/

theorem filter_sB : (Ib (![2, 0, 0] : Fin 3 → ℕ) 0).filter
    (fun i => sig (![2, 0, 0] : Fin 3 → ℕ) sB i = -1) = {1} := by
  rw [Ib_200_0]
  ext i
  rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]
  simp only [sig, sB, mkSw]
  fin_cases i <;> norm_num

-- Lemma 4.3 for `T(2,0,0)` (`k_0 = 2`): `sB` is the member `s_{1,1}` of the bare row
theorem test_bareRow_sB : IsBareRowMember (![2, 0, 0] : Fin 3 → ℕ) 1 1 sB := by
  have hstd : lamStd (![2, 0, 0] : Fin 3 → ℕ) 0 = 0 := by decide
  refine ⟨isSwitching_sB, by simp only [sc, sB, mkSw]; norm_num, fun i hi => ?_, ?_⟩
  · obtain rfl : i = 0 := by
      revert i
      decide
    refine ⟨by simp only [sig, sB, mkSw]; norm_num, ?_⟩
    rw [hstd]
    simp only [lam, sB, mkSw]
    rw [Fin.sum_univ_eq_sum_range (fun n => if n = 0 then (1 : ℝ) else -1)]
    norm_num [Finset.sum_range_succ]
  · rw [filter_sB, Finset.card_singleton]

-- FALSE: the count `m` is the number of bare branches with `σ_i = -1`: `sB` is not `s_{1,2}`;
-- and `sB` is not `s_{-1,1}`
theorem test_not_bareRow_sB : ¬ IsBareRowMember (![2, 0, 0] : Fin 3 → ℕ) 1 2 sB ∧
    ¬ IsBareRowMember (![2, 0, 0] : Fin 3 → ℕ) (-1) 1 sB := by
  constructor
  · rintro ⟨-, -, -, h⟩
    rw [filter_sB, Finset.card_singleton] at h
    omega
  · rintro ⟨-, h, -⟩
    simp only [sc, sB, mkSw] at h
    norm_num at h

-- FALSE: `sw56b` has `σ_1 = -1` on the branch of size 2, so it is in no bare row
theorem test_not_bareRow_56b (ε : ℤ) (mm : ℕ) :
    ¬ IsBareRowMember (![2, 0, 0] : Fin 3 → ℕ) ε mm sw56b := by
  rintro ⟨-, -, h, -⟩
  have := (h 0 (by decide)).1
  rw [test_sc_sig_56b.2.1] at this
  norm_num at this

end P8Tests
