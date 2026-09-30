import Research.Backfill.Paper8.Proof.Tests.Cond

/-!
# Paper 8, known-answer tests (agent `tests`): main eigenvalues, `ℚ(t)`, and the tree `T(2,0,0)`

Tests of `AllEigenvaluesMain` on `K_1`, `K_2 = T(0)` (every switching fails, which is why `K_2` is
excluded from Theorem 1) and `K_{1,2} = T(0,0)` (Proposition 5.1(a) holds, the all-ones switching
fails); of `QAdj` (Lemma 3.3(a), (b)); and of `treeT`: `T(2,0,0)` is a tree of diameter `3`, and
`T(3) = K_{1,4}` has diameter `2`. Eigenvectors are handled with the `mkSw` calculus of
`Research.Backfill.Paper8.Proof.Tests.Vec`; the diameters with Mathlib's `edist` lemmas and `decide` on adjacency.
-/

set_option autoImplicit false

open BackfillPaper8 BackfillPaper8.Challenge Matrix SimpleGraph
open Polynomial hiding mirror

namespace P8Tests

/-- A leaf sum over a bare branch is `0`. -/
theorem sum_leaves_eq_zero {k : ℕ} (a : Fin k → ℕ) (i : Fin k) (hi : a i = 0)
    (f : Fin (a i) → ℝ) : ∑ j, f j = 0 := by
  have : IsEmpty (Fin (a i)) := by
    rw [hi]
    infer_instance
  exact Fintype.sum_empty f

/-! ## `AllEigenvaluesMain` -/

-- the small trees used below: `T()` (`k = 0`) is `K_1`; `T(0)` is `K_2` (two adjacent vertices);
-- `T(0,0)` is `K_{1,2}` (the centre is adjacent to both leaves, which are not adjacent)
theorem test_small_trees :
    Fintype.card (TV (![] : Fin 0 → ℕ)) = 1 ∧ Fintype.card (TV (![0] : Fin 1 → ℕ)) = 2 ∧
    (treeT (![0] : Fin 1 → ℕ)).Adj none (some ⟨0, none⟩) ∧
    Fintype.card (TV (![0, 0] : Fin 2 → ℕ)) = 3 ∧
    (treeT (![0, 0] : Fin 2 → ℕ)).Adj none (some ⟨1, none⟩) ∧
    ¬ (treeT (![0, 0] : Fin 2 → ℕ)).Adj (some ⟨0, none⟩) (some ⟨1, none⟩) := by
  decide

-- Theorem 1, proof: "The tree K_1 is trivial, since the switching (1) is good": `T()` (`k = 0`)
-- is `K_1`, `A = 0`, and its only eigenvalue `0` has the eigenvector `(1)`
theorem test_allMain_K1 : AllEigenvaluesMain (adjT (![] : Fin 0 → ℕ)) := by
  have hA : ∀ y : TV (![] : Fin 0 → ℕ) → ℝ, adjT (![] : Fin 0 → ℕ) *ᵥ y = 0 := by
    intro y
    rw [eq_mkSw _ y, adjT_mulVec_mkSw, zero_eq_mkSw, mkSw_eq_iff]
    exact ⟨by simp, fun i => i.elim0, fun i => i.elim0⟩
  intro θ hθ
  obtain ⟨x, hx0, hx⟩ := (P8Basic.isEigenvalue_iff _ _).1 hθ
  have hθ0 : θ = 0 := by
    rw [hA] at hx
    rcases smul_eq_zero.1 hx.symm with h | h
    · exact h
    · exact absurd h hx0
  refine ⟨hθ, fun _ => 1, (P8Basic.mem_eigenspace_iff _ _ _).2 ?_, ?_⟩
  · rw [hA, hθ0, zero_smul]
  · simp

-- `K_2 = T(0)` is excluded from Theorem 1: for EVERY switching `s`, `D_s A D_s` has the eigenvalue
-- `-s_c s_{v_1}` with eigenvector `(1, -1)`, and each of its eigenvectors has coordinate sum `0`
theorem test_not_allMain_K2 (s : TV (![0] : Fin 1 → ℕ) → ℝ) (hs : IsSwitching s) :
    ¬ AllEigenvaluesMain (switchMatrix (adjT (![0] : Fin 1 → ℕ)) s) := by
  have hz : ∀ i : Fin 1, (![0] : Fin 1 → ℕ) i = 0 := by decide
  have hp2 : (s none * s (some ⟨0, none⟩)) * (s none * s (some ⟨0, none⟩)) = 1 := by
    rcases hs none with h | h <;> rcases hs (some ⟨0, none⟩) with h' | h' <;> rw [h, h'] <;>
      norm_num
  intro hall
  have hev : IsEigenvalue (switchMatrix (adjT (![0] : Fin 1 → ℕ)) s)
      (-(s none * s (some ⟨0, none⟩))) := by
    rw [P8Basic.isEigenvalue_iff]
    refine ⟨mkSw _ 1 (fun _ => -1) (fun _ _ => 0), ?_, ?_⟩
    · intro h0
      have := congrFun h0 none
      simp only [mkSw_none] at this
      norm_num at this
    · rw [eq_mkSw _ s, switch_mulVec_mkSw, smul_mkSw, mkSw_eq_iff]
      refine ⟨?_, fun i => ?_, fun i j => ?_⟩
      · simp only [mkSw_none, mkSw_v, Fin.sum_univ_one]
        ring
      · obtain rfl : i = 0 := Subsingleton.elim _ _
        simp only [mkSw_none, mkSw_v, mul_zero, Finset.sum_const_zero, add_zero]
        ring
      · exfalso
        have h1 := j.isLt
        have h2 := hz i
        omega
  obtain ⟨-, x, hx, hsum⟩ := hall _ hev
  rw [P8Basic.mem_eigenspace_iff] at hx
  have hc := congrFun hx none
  rw [switchMatrix_mulVec_apply, P8Basic.mulVec_c, Fin.sum_univ_one, Pi.smul_apply,
    smul_eq_mul] at hc
  apply hsum
  rw [P8Basic.sum_TV, Fin.sum_univ_one, sum_leaves_eq_zero _ 0 (hz 0), add_zero]
  linear_combination (s none * s (some ⟨0, none⟩)) * hc - (x none + x (some ⟨0, none⟩)) * hp2

/-- `D_s A D_s` on `K_{1,2} = T(0,0)` for the switching `s00` of Proposition 5.1(a). -/
theorem switch_s00_mulVec (c : ℝ) (m : Fin 2 → ℝ)
    (l : (i : Fin 2) → Fin ((![0, 0] : Fin 2 → ℕ) i) → ℝ) :
    switchMatrix (adjT (![0, 0] : Fin 2 → ℕ)) s00 *ᵥ mkSw _ c m l =
      mkSw _ (-m 0 + m 1) ![-c, c] (fun _ _ => 0) := by
  have hz : ∀ i : Fin 2, (![0, 0] : Fin 2 → ℕ) i = 0 := by decide
  rw [s00, switch_mulVec_mkSw, mkSw_eq_iff]
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simp [Fin.sum_univ_two]
  · rw [sum_leaves_eq_zero _ i (hz i)]
    fin_cases i <;> simp
  · exfalso
    have h1 := j.isLt
    have h2 := hz i
    omega

/-- `A` on `K_{1,2} = T(0,0)`, i.e. `D_s A D_s` for the all-ones switching. -/
theorem switch_ones00_mulVec (c : ℝ) (m : Fin 2 → ℝ)
    (l : (i : Fin 2) → Fin ((![0, 0] : Fin 2 → ℕ) i) → ℝ) :
    switchMatrix (adjT (![0, 0] : Fin 2 → ℕ)) (fun _ => 1) *ᵥ mkSw _ c m l =
      mkSw _ (m 0 + m 1) ![c, c] (fun _ _ => 0) := by
  have hz : ∀ i : Fin 2, (![0, 0] : Fin 2 → ℕ) i = 0 := by decide
  rw [ones_eq_mkSw, switch_mulVec_mkSw, mkSw_eq_iff]
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simp [Fin.sum_univ_two]
  · rw [sum_leaves_eq_zero _ i (hz i)]
    fin_cases i <;> simp
  · exfalso
    have h1 := j.isLt
    have h2 := hz i
    omega

-- Prop 5.1(a) for `k_0 = 2` (`K_{1,2}`, `-1` on one leaf): every eigenvalue is main (`±√2` with
-- eigenvectors `(θ, -1, 1)` on `(c, v_1, v_2)`, `0` with `(0, 1, 1)`)
theorem test_allMain_s00 :
    AllEigenvaluesMain (switchMatrix (adjT (![0, 0] : Fin 2 → ℕ)) s00) := by
  have hz : ∀ i : Fin 2, (![0, 0] : Fin 2 → ℕ) i = 0 := by decide
  intro θ hθ
  refine ⟨hθ, ?_⟩
  obtain ⟨x, hx0, hx⟩ := (P8Basic.isEigenvalue_iff _ _).1 hθ
  rw [eq_mkSw _ x, switch_s00_mulVec, smul_mkSw, mkSw_eq_iff] at hx
  obtain ⟨hc, hm, -⟩ := hx
  have h0 : -x none = θ * x (some ⟨0, none⟩) := hm 0
  have h1 : x none = θ * x (some ⟨1, none⟩) := hm 1
  by_cases hθ0 : θ = 0
  · subst hθ0
    refine ⟨mkSw _ 0 (fun _ => 1) (fun _ _ => 0), ?_, ?_⟩
    · rw [P8Basic.mem_eigenspace_iff, switch_s00_mulVec, smul_mkSw, mkSw_eq_iff]
      refine ⟨by norm_num, fun i => ?_, fun i j => ?_⟩
      · fin_cases i <;> simp
      · exfalso
        have h1 := j.isLt
        have h2 := hz i
        omega
    · rw [sum_mkSw, Fin.sum_univ_two, sum_leaves_eq_zero _ 0 (hz 0),
        sum_leaves_eq_zero _ 1 (hz 1)]
      norm_num
  · have hxc : x none ≠ 0 := by
      intro hxc0
      apply hx0
      rw [eq_mkSw _ x, zero_eq_mkSw, mkSw_eq_iff]
      refine ⟨hxc0, fun i => ?_, fun i j => ?_⟩
      · fin_cases i
        · have : θ * x (some ⟨0, none⟩) = 0 := by linarith
          exact (mul_eq_zero.1 this).resolve_left hθ0
        · have : θ * x (some ⟨1, none⟩) = 0 := by linarith
          exact (mul_eq_zero.1 this).resolve_left hθ0
      · exfalso
        have h1 := j.isLt
        have h2 := hz i
        omega
    have hθ2 : θ ^ 2 = 2 := by
      have : (θ ^ 2 - 2) * x none = 0 := by linear_combination (-θ) * hc + h0 - h1
      linarith [(mul_eq_zero.1 this).resolve_right hxc]
    refine ⟨mkSw _ θ ![-1, 1] (fun _ _ => 0), ?_, ?_⟩
    · rw [P8Basic.mem_eigenspace_iff, switch_s00_mulVec, smul_mkSw, mkSw_eq_iff]
      refine ⟨?_, fun i => ?_, fun i j => ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
      · fin_cases i <;> simp
      · exfalso
        have h1 := j.isLt
        have h2 := hz i
        omega
    · rw [sum_mkSw, Fin.sum_univ_two, sum_leaves_eq_zero _ 0 (hz 0),
        sum_leaves_eq_zero _ 1 (hz 1)]
      simpa using hθ0

-- FALSE: for the all-ones switching of `K_{1,2}` the eigenvalue `0` (eigenvector `(0, 1, -1)`)
-- is not main: every kernel vector has `x_c = 0` and `x_{v_1} + x_{v_2} = 0`
theorem test_not_allMain_00 :
    ¬ AllEigenvaluesMain (switchMatrix (adjT (![0, 0] : Fin 2 → ℕ)) (fun _ => 1)) := by
  have hz : ∀ i : Fin 2, (![0, 0] : Fin 2 → ℕ) i = 0 := by decide
  intro hall
  have hev : IsEigenvalue (switchMatrix (adjT (![0, 0] : Fin 2 → ℕ)) (fun _ => 1)) 0 := by
    rw [P8Basic.isEigenvalue_iff]
    refine ⟨mkSw _ 0 ![1, -1] (fun _ _ => 0), ?_, ?_⟩
    · intro h0
      have := congrFun h0 (some ⟨0, none⟩)
      simp only [mkSw_v] at this
      norm_num at this
    · rw [switch_ones00_mulVec, smul_mkSw, mkSw_eq_iff]
      refine ⟨by norm_num, fun i => ?_, fun i j => ?_⟩
      · fin_cases i <;> simp
      · exfalso
        have h1 := j.isLt
        have h2 := hz i
        omega
  obtain ⟨-, x, hx, hsum⟩ := hall 0 hev
  rw [P8Basic.mem_eigenspace_iff, eq_mkSw _ x, switch_ones00_mulVec, smul_mkSw,
    mkSw_eq_iff] at hx
  obtain ⟨hc, hm, -⟩ := hx
  have h0 : x none = 0 * x (some ⟨0, none⟩) := hm 0
  apply hsum
  rw [eq_mkSw _ x, sum_mkSw, Fin.sum_univ_two, sum_leaves_eq_zero _ 0 (hz 0),
    sum_leaves_eq_zero _ 1 (hz 1)]
  linarith

/-! ## `QAdj` (`ℚ(t) ⊆ ℝ`) -/

-- Lemma 3.3(a) for the even orbit `{±√2}` of `T(1)` (`R = t - 2`): `θ = √2 ∉ ℚ(θ²) = ℚ(2) = ℚ`
theorem test_QAdj_sqrt2 : Real.sqrt 2 ∉ QAdj 2 := by
  have hb : QAdj (2 : ℝ) = ⊥ := by
    rw [QAdj, IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot]
    exact ⟨2, by norm_num⟩
  rw [hb, IntermediateField.mem_bot]
  rintro ⟨q, hq⟩
  exact irrational_sqrt_two ⟨q, hq⟩

-- review T3: `3 ∈ QAdj 9` (rational numbers lie in every `ℚ(t)`)
theorem test_QAdj_3_9 : (3 : ℝ) ∈ QAdj 9 := by
  have : (3 : ℝ) = algebraMap ℚ ℝ 3 := by norm_num
  rw [this]
  exact IntermediateField.algebraMap_mem _ _

-- Lemma 3.3(b) for the irrational pair of `T(3,0,0,0)`: a root `θ` of `x² - x - 3` lies in
-- `ℚ(θ²)`, as `θ = θ² - 3`
theorem test_QAdj_pair_3000 (θ : ℝ) (h : θ ^ 2 - θ - 3 = 0) : θ ∈ QAdj (θ ^ 2) := by
  have h3 : (3 : ℝ) ∈ QAdj (θ ^ 2) := by
    have : (3 : ℝ) = algebraMap ℚ ℝ 3 := by norm_num
    rw [this]
    exact IntermediateField.algebraMap_mem _ _
  have h2 : θ ^ 2 - 3 ∈ QAdj (θ ^ 2) :=
    sub_mem (IntermediateField.mem_adjoin_simple_self ℚ (θ ^ 2)) h3
  convert h2 using 1
  linarith

/-! ## `treeT`: `T(2,0,0) = D(2,2)` is a tree of diameter 3, `T(3) = K_{1,4}` has diameter 2 -/

-- review T3: "(treeT ![2,0,0]).IsTree with ediam = 3"
theorem test_isTree_200 : (treeT (![2, 0, 0] : Fin 3 → ℕ)).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨⟨fun x y => ?_⟩, ?_⟩
  · have h : ∀ z : TV (![2, 0, 0] : Fin 3 → ℕ),
        (treeT (![2, 0, 0] : Fin 3 → ℕ)).Reachable none z := by
      intro z
      rcases z with _ | ⟨i, _ | j⟩
      · exact Reachable.refl _
      · exact (P8Basic.adj_c_v _ i).reachable
      · exact (P8Basic.adj_c_v _ i).reachable.trans ((P8Basic.adj_v_l _ i i j).2 rfl).reachable
    exact (h x).symm.trans (h y)
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
    decide

/-- The nearer of the two centres `c`, `v_1` of the double star `T(2,0,0)`. -/
def near200 : TV (![2, 0, 0] : Fin 3 → ℕ) → TV (![2, 0, 0] : Fin 3 → ℕ)
  | some ⟨i, some _⟩ => some ⟨i, none⟩
  | _ => none

theorem test_ediam_200 : (treeT (![2, 0, 0] : Fin 3 → ℕ)).ediam = 3 := by
  have h1 : ∀ u, (treeT (![2, 0, 0] : Fin 3 → ℕ)).edist u (near200 u) ≤ 1 := by
    intro u
    rw [edist_le_one_iff_adj_or_eq]
    revert u
    decide
  have h2 : ∀ u v, (treeT (![2, 0, 0] : Fin 3 → ℕ)).edist (near200 u) (near200 v) ≤ 1 := by
    intro u v
    rw [edist_le_one_iff_adj_or_eq]
    revert u v
    decide
  apply le_antisymm
  · rw [ediam_le_iff]
    intro u v
    calc (treeT (![2, 0, 0] : Fin 3 → ℕ)).edist u v
        ≤ (treeT (![2, 0, 0] : Fin 3 → ℕ)).edist u (near200 u) +
          (treeT (![2, 0, 0] : Fin 3 → ℕ)).edist (near200 u) v :=
          SimpleGraph.edist_triangle
      _ ≤ (treeT (![2, 0, 0] : Fin 3 → ℕ)).edist u (near200 u) +
          ((treeT (![2, 0, 0] : Fin 3 → ℕ)).edist (near200 u) (near200 v) +
            (treeT (![2, 0, 0] : Fin 3 → ℕ)).edist (near200 v) v) := by
          gcongr
          exact SimpleGraph.edist_triangle
      _ ≤ 1 + (1 + 1) := by
          gcongr
          · exact h1 u
          · exact h2 u v
          · rw [edist_comm]
            exact h1 v
      _ = 3 := by norm_num
  · -- a leaf of `v_1` and the leaf neighbour `v_2` of `c` are at distance 3
    have hlt : 2 < (treeT (![2, 0, 0] : Fin 3 → ℕ)).edist (some ⟨0, some ⟨0, by decide⟩⟩)
        (some ⟨1, none⟩) := by
      rw [two_lt_edist_iff]
      refine ⟨by decide, by decide, ?_⟩
      rw [Set.eq_empty_iff_forall_notMem]
      intro w hw
      rw [mem_commonNeighbors] at hw
      revert w
      decide
    exact le_trans (by norm_num) ((Order.add_one_le_of_lt hlt).trans edist_le_ediam)

-- Prop 5.6(c): `T(3) = K_{1,4}` (a star, centre `v_1`) has diameter 2
theorem test_ediam_3 : (treeT (![3] : Fin 1 → ℕ)).ediam = 2 := by
  have h1 : ∀ u, (treeT (![3] : Fin 1 → ℕ)).edist u (some ⟨0, none⟩) ≤ 1 := by
    intro u
    rw [edist_le_one_iff_adj_or_eq]
    revert u
    decide
  apply le_antisymm
  · rw [ediam_le_iff]
    intro u v
    calc (treeT (![3] : Fin 1 → ℕ)).edist u v
        ≤ (treeT (![3] : Fin 1 → ℕ)).edist u (some ⟨0, none⟩) +
          (treeT (![3] : Fin 1 → ℕ)).edist (some ⟨0, none⟩) v := SimpleGraph.edist_triangle
      _ ≤ 1 + 1 := by
          gcongr
          · exact h1 u
          · rw [edist_comm]
            exact h1 v
      _ = 2 := by norm_num
  · have hlt : 1 < (treeT (![3] : Fin 1 → ℕ)).edist none (some ⟨0, some ⟨0, by decide⟩⟩) := by
      rw [← not_le, edist_le_one_iff_adj_or_eq]
      decide
    exact le_trans (by norm_num) ((Order.add_one_le_of_lt hlt).trans edist_le_ediam)

end P8Tests
