import Research.Backfill.Paper8.Proof.Tests.Counts
import Research.Backfill.Paper8.Proof.Real.Lset

/-!
# Paper 8, known-answer tests (agent `tests`): criteria (a′), (b′) and the region `ℛ`

Tests of `CritAat`, `CritA`, `CritB`, `InRegion` and `regionR`. The three exceptions of
Proposition 5.5 lie in `ℛ` and satisfy neither (a′) nor (b′); `(2)` and `(2,0)` lie in `ℛ` and
satisfy (a′) resp. (b′); `(13)`, `(2,2,2)` and `(2,0,0,0,0)` are not in `ℛ`, each for a different
reason. The sizes `|ℒ_β(k)|` come from Lemma 4.1 (`P8Real.lemma_4_1`), the pair counts from
`Research.Backfill.Paper8.Proof.Tests.Poly`, and `M(B)`, `ν(B)`, `k_b`, `b*` are evaluated by `decide`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge

namespace P8Tests

theorem ncard_Lset_of_two_le {β k : ℕ} (hβ : 2 ≤ β) (hk : 1 ≤ k) :
    (Lset β k).ncard = k * β - 1 - (if β = 2 ∧ k = 2 then 1 else 0) :=
  ((P8Real.lemma_4_1 β k (by omega) hk).1 hβ).2

-- Lemma 4.1: `|ℒ_β(k)| = kβ - 1 - [β = k = 2]`
theorem ncard_Lset_2_1 : (Lset 2 1).ncard = 1 := by
  rw [ncard_Lset_of_two_le le_rfl le_rfl]
  decide

theorem ncard_Lset_2_2 : (Lset 2 2).ncard = 2 := by
  rw [ncard_Lset_of_two_le le_rfl (by norm_num)]
  decide

theorem ncard_Lset_2_3 : (Lset 2 3).ncard = 5 := by
  rw [ncard_Lset_of_two_le le_rfl (by norm_num)]
  decide

theorem ncard_Lset_3_1 : (Lset 3 1).ncard = 2 := by
  rw [ncard_Lset_of_two_le (by norm_num) le_rfl]
  decide

/-! ## Proposition 5.5: `(2,2)`, `(2,0,0)` and `(3)` satisfy neither (a′) nor (b′) -/

-- `(2,2)`: `B = {2}`, `|ℒ_2(2)| = 2 < 2 N_I + N_II + 1 = 3`; (b′) needs `k_0 ≥ 1`, but `k_0 = 0`
theorem test_not_critA_22 : ¬ CritA {2, 2} := by
  rintro ⟨β, hβ, -, h⟩
  rw [show Bset {2, 2} = {2} by decide, Finset.mem_singleton] at hβ
  subst hβ
  have h1 := test_NI_22
  have h2 : (Lset 2 (kb {2, 2} 2)).ncard = 2 := by
    rw [show kb {2, 2} 2 = 2 by decide, ncard_Lset_2_2]
  unfold CritAat at h
  omega

theorem test_not_critB_22 : ¬ CritB {2, 2} := fun h => absurd h.1 (by decide)

-- `(2,0,0)`: `B = {0, 2}`, `|ℒ_2(1)| = 1 < 2 N_I + N_II + 1 = 5`; `k_0 = 2` and
-- `2(k_0 + 1) = 6 ≤ 4 N_I + 2 N_II + N_ei = 8`
theorem test_not_critA_200 : ¬ CritA {2, 0, 0} := by
  rintro ⟨β, hβ, hβ1, h⟩
  rw [show Bset {2, 0, 0} = {0, 2} by decide] at hβ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
  rcases hβ with rfl | rfl
  · omega
  · have h1 := test_NI_200
    have h2 : (Lset 2 (kb {2, 0, 0} 2)).ncard = 1 := by
      rw [show kb {2, 0, 0} 2 = 1 by decide, ncard_Lset_2_1]
    unfold CritAat at h
    omega

theorem test_not_critB_200 : ¬ CritB {2, 0, 0} := by
  rintro ⟨-, h⟩
  have h1 := test_NI_200
  have h2 : kb {2, 0, 0} 0 = 2 := by decide
  omega

-- `(3)`: `B = {3}`, `|ℒ_3(1)| = 2 < 2 N_I + N_II + 1 = 3`; `k_0 = 0`
theorem test_not_critA_3 : ¬ CritA {3} := by
  rintro ⟨β, hβ, -, h⟩
  rw [show Bset {3} = {3} by decide, Finset.mem_singleton] at hβ
  subst hβ
  have h1 := test_NI_3
  have h2 : (Lset 3 (kb {3} 3)).ncard = 2 := by
    rw [show kb {3} 3 = 1 by decide, ncard_Lset_3_1]
  unfold CritAat at h
  omega

theorem test_not_critB_3 : ¬ CritB {3} := fun h => absurd h.1 (by decide)

-- review T3: "¬ CritA ∧ ¬ CritB for each of (2,2), (2,0,0), (3)"
theorem test_exception_22 : ¬ CritA {2, 2} ∧ ¬ CritB {2, 2} :=
  ⟨test_not_critA_22, test_not_critB_22⟩

theorem test_exception_200 : ¬ CritA {2, 0, 0} ∧ ¬ CritB {2, 0, 0} :=
  ⟨test_not_critA_200, test_not_critB_200⟩

theorem test_exception_3 : ¬ CritA {3} ∧ ¬ CritB {3} :=
  ⟨test_not_critA_3, test_not_critB_3⟩

/-! ## Members of `ℛ` that satisfy (a′) or (b′) -/

-- `(2)`: `R = t - 3`, `N_I = N_II = 0` and `|ℒ_2(1)| = 1 ≥ 2 N_I + N_II + 1`: (a′) at `β = 2`
theorem test_CritAat_2 : CritAat {2} 2 := by
  have h1 := test_NI_2
  have h2 := test_NII_2
  have h3 : (Lset 2 (kb {2} 2)).ncard = 1 := by
    rw [show kb {2} 2 = 1 by decide, ncard_Lset_2_1]
  unfold CritAat
  omega

theorem test_critA_2 : CritA {2} := ⟨2, by decide, by norm_num, test_CritAat_2⟩

theorem test_crit_2 : CritA {2} ∨ CritB {2} := Or.inl test_critA_2

-- FALSE instance of `CritAat`: `(3)` at `β = 3`
theorem test_not_CritAat_3 : ¬ CritAat {3} 3 :=
  fun h => test_not_critA_3 ⟨3, by decide, by norm_num, h⟩

-- `(2,0)`: `R = t² - 4t + 2`, `N_I = N_II = N_ei = 0`, `k_0 = 1`: (b′), `0 < 2(k_0 + 1) = 4`
theorem test_critB_20 : CritB {2, 0} := by
  have h1 := test_NI_20
  have h2 := test_NII_20
  have h3 := test_Nei_20
  have h4 : kb {2, 0} 0 = 1 := by decide
  refine ⟨by omega, ?_⟩
  omega

/-! ## `InRegion`, `regionR` (Lemma 5.4) -/

-- `(2)`: `b* = 2`, `|ℒ_2(1)| = 1 ≤ M({2}) = 2`, `k_0 = 0`
theorem test_region_2 : InRegion {2} := by
  refine ⟨by decide, by decide, fun β hβ _ => ?_, by decide⟩
  rw [show Bset {2} = {2} by decide, Finset.mem_singleton] at hβ
  subst hβ
  have h3 : (Lset 2 (kb {2} 2)).ncard = 1 := by
    rw [show kb {2} 2 = 1 by decide, ncard_Lset_2_1]
  have h4 : MB (Bset {2}) (bstar {2}) = 2 := by decide
  omega

-- `(2,0)`: `|ℒ_2(1)| = 1 ≤ M({0,2}) = 4`, and `2(k_0 + 1) = 4 ≤ 3ν + r = 8`
theorem test_region_20 : InRegion {2, 0} := by
  refine ⟨by decide, by decide, fun β hβ hβ1 => ?_, by decide⟩
  rw [show Bset {2, 0} = {0, 2} by decide] at hβ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
  rcases hβ with rfl | rfl
  · omega
  · have h3 : (Lset 2 (kb {2, 0} 2)).ncard = 1 := by
      rw [show kb {2, 0} 2 = 1 by decide, ncard_Lset_2_1]
    have h4 : MB (Bset {2, 0}) (bstar {2, 0}) = 4 := by decide
    omega

-- review T3: "InRegion {2,2}"; first review §5d: the three exceptions lie in `ℛ`
theorem test_region_22 : InRegion {2, 2} := by
  refine ⟨by decide, by decide, fun β hβ _ => ?_, by decide⟩
  rw [show Bset {2, 2} = {2} by decide, Finset.mem_singleton] at hβ
  subst hβ
  have h3 : (Lset 2 (kb {2, 2} 2)).ncard = 2 := by
    rw [show kb {2, 2} 2 = 2 by decide, ncard_Lset_2_2]
  have h4 : MB (Bset {2, 2}) (bstar {2, 2}) = 2 := by decide
  omega

theorem test_region_200 : InRegion {2, 0, 0} := by
  refine ⟨by decide, by decide, fun β hβ hβ1 => ?_, by decide⟩
  rw [show Bset {2, 0, 0} = {0, 2} by decide] at hβ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
  rcases hβ with rfl | rfl
  · omega
  · have h3 : (Lset 2 (kb {2, 0, 0} 2)).ncard = 1 := by
      rw [show kb {2, 0, 0} 2 = 1 by decide, ncard_Lset_2_1]
    have h4 : MB (Bset {2, 0, 0}) (bstar {2, 0, 0}) = 4 := by decide
    omega

theorem test_region_3 : InRegion {3} := by
  refine ⟨by decide, by decide, fun β hβ _ => ?_, by decide⟩
  rw [show Bset {3} = {3} by decide, Finset.mem_singleton] at hβ
  subst hβ
  have h3 : (Lset 3 (kb {3} 3)).ncard = 2 := by
    rw [show kb {3} 3 = 1 by decide, ncard_Lset_3_1]
  have h4 : MB (Bset {3}) (bstar {3}) = 2 := by decide
  omega

-- FALSE instances. review T3: "¬ InRegion {13}" (`b* = 13 > 12`)
theorem test_not_region_13 : ¬ InRegion {13} := fun h => absurd h.2.1 (by decide)

-- `(2,2,2)`: `2 ≤ b* ≤ 12`, but `|ℒ_2(3)| = 5 > M({2}) = 2`
theorem test_not_region_222 : ¬ InRegion {2, 2, 2} := by
  intro h
  have h1 := h.2.2.1 2 (by decide) (by norm_num)
  have h3 : (Lset 2 (kb {2, 2, 2} 2)).ncard = 5 := by
    rw [show kb {2, 2, 2} 2 = 3 by decide, ncard_Lset_2_3]
  have h4 : MB (Bset {2, 2, 2}) (bstar {2, 2, 2}) = 2 := by decide
  omega

-- `(2,0,0,0,0)`: the first condition holds, but `2(k_0 + 1) = 10 > 3ν + r = 8`
theorem test_not_region_20000 : ¬ InRegion {2, 0, 0, 0, 0} :=
  fun h => absurd (h.2.2.2 (by decide)) (by decide)

-- `regionR` is the set of these multisets
theorem test_regionR :
    {2, 2} ∈ regionR ∧ {2, 0, 0} ∈ regionR ∧ {3} ∈ regionR ∧ {2} ∈ regionR ∧
      ({13} : Multiset ℕ) ∉ regionR ∧ ({2, 2, 2} : Multiset ℕ) ∉ regionR :=
  ⟨test_region_22, test_region_200, test_region_3, test_region_2, test_not_region_13,
    test_not_region_222⟩

end P8Tests
