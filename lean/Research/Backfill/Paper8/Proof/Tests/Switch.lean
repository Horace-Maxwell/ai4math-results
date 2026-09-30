import Research.Backfill.Paper8.Proof.Tests.Poly
import Research.Backfill.Paper8.Proof.Tests.Vec

/-!
# Paper 8, known-answer tests (agent `tests`): the data of a switching of `T(a)`

Tests of `adjT`, `secVec`, `sc`, `sig`, `lam`, `Sb`, `Lamb`, `Ab`, `Gs`, `Ps`, `Ufun`, `Ubeta`,
`sw56a` and `sw56b`, computed from the definitions (`Bset`, `Ib`, `k_b`, `λ°` by `decide`) on the
trees and switchings of Proposition 5.6 and on `T(3,1)`. The values of `G_s` are those of the
proof of Proposition 5.6; `secVec` is checked to be an eigenvector at a secular `θ` and not at
another `θ`. Comments use the paper's names: `none` is the centre `c`, `some ⟨i, none⟩` is
`v_{i+1}` and `some ⟨i, some j⟩` a leaf of `v_{i+1}` (Lean indices start at `0`).
-/

set_option autoImplicit false

open BackfillPaper8 BackfillPaper8.Challenge Matrix
open Polynomial hiding mirror

namespace P8Tests

/-! ## `adjT`: the adjacency matrix of `T(2,0,0) = D(2,2)` -/

-- Prop 5.6(b), `T(2,0,0)`: `c ~ v_2`, and `v_1 ~` its second leaf (in both orders)
theorem test_adjT_200 :
    adjT (![2, 0, 0] : Fin 3 → ℕ) none (some ⟨1, none⟩) = 1 ∧
    adjT (![2, 0, 0] : Fin 3 → ℕ) (some ⟨0, none⟩) (some ⟨0, some ⟨1, by decide⟩⟩) = 1 ∧
    adjT (![2, 0, 0] : Fin 3 → ℕ) (some ⟨0, some ⟨1, by decide⟩⟩) (some ⟨0, none⟩) = 1 := by
  have h1 : (treeT (![2, 0, 0] : Fin 3 → ℕ)).Adj none (some ⟨1, none⟩) := by decide
  have h2 : (treeT (![2, 0, 0] : Fin 3 → ℕ)).Adj (some ⟨0, none⟩)
      (some ⟨0, some ⟨1, by decide⟩⟩) := by decide
  have h3 : (treeT (![2, 0, 0] : Fin 3 → ℕ)).Adj (some ⟨0, some ⟨1, by decide⟩⟩)
      (some ⟨0, none⟩) := by decide
  simp only [P8Basic.adjT_apply, h1, h2, h3, ite_true, and_self]

-- FALSE adjacencies: `v_2 ≁ v_3`, `c ≁ c`, `c ≁ ℓ`
theorem test_adjT_200_zero :
    adjT (![2, 0, 0] : Fin 3 → ℕ) (some ⟨1, none⟩) (some ⟨2, none⟩) = 0 ∧
    adjT (![2, 0, 0] : Fin 3 → ℕ) none none = 0 ∧
    adjT (![2, 0, 0] : Fin 3 → ℕ) none (some ⟨0, some ⟨0, by decide⟩⟩) = 0 := by
  have h1 : ¬ (treeT (![2, 0, 0] : Fin 3 → ℕ)).Adj (some ⟨1, none⟩) (some ⟨2, none⟩) := by decide
  have h2 : ¬ (treeT (![2, 0, 0] : Fin 3 → ℕ)).Adj none none := by decide
  have h3 : ¬ (treeT (![2, 0, 0] : Fin 3 → ℕ)).Adj none (some ⟨0, some ⟨0, by decide⟩⟩) := by
    decide
  simp only [P8Basic.adjT_apply, h1, h2, h3, ite_false, and_self]

-- the row sums of `A` are the degrees: `3` at `c` and at `v_1`, `1` at `v_2`
theorem test_adjT_degrees_200 :
    (adjT (![2, 0, 0] : Fin 3 → ℕ) *ᵥ fun _ => (1 : ℝ)) none = 3 ∧
    (adjT (![2, 0, 0] : Fin 3 → ℕ) *ᵥ fun _ => (1 : ℝ)) (some ⟨0, none⟩) = 3 ∧
    (adjT (![2, 0, 0] : Fin 3 → ℕ) *ᵥ fun _ => (1 : ℝ)) (some ⟨1, none⟩) = 1 := by
  rw [ones_eq_mkSw, adjT_mulVec_mkSw]
  norm_num [Fin.sum_univ_three]

/-! ## `secVec`: the eigenvector `x^θ` of Lemma 3.1(i) -/

-- Lemma 3.1(i): `x_c = 1`, `x_{v_i} = θ/(θ² - a_i)`, `x_ℓ = 1/(θ² - a_i)`; `T(3)`, `θ = 2`
theorem test_secVec_3 :
    secVec (![3] : Fin 1 → ℕ) 2 none = 1 ∧ secVec (![3] : Fin 1 → ℕ) 2 (some ⟨0, none⟩) = 2 ∧
    ∀ j, secVec (![3] : Fin 1 → ℕ) 2 (some ⟨0, some j⟩) = 1 := by
  refine ⟨by simp [secVec], by norm_num [secVec], fun j => by norm_num [secVec]⟩

theorem secVec_eq_mkSw {k : ℕ} (a : Fin k → ℕ) (θ : ℝ) :
    secVec a θ = mkSw a 1 (fun i => θ / (θ ^ 2 - a i)) (fun i _ => 1 / (θ ^ 2 - a i)) := by
  funext v
  rcases v with _ | ⟨i, _ | j⟩ <;> rfl

-- Lemma 3.1(i): `x^θ` is an eigenvector of `A(T(3))` for the secular `θ = 2` (`R = t - 4`)
theorem test_secVec_eigen_3 :
    adjT (![3] : Fin 1 → ℕ) *ᵥ secVec (![3] : Fin 1 → ℕ) 2 =
      (2 : ℝ) • secVec (![3] : Fin 1 → ℕ) 2 := by
  rw [secVec_eq_mkSw, adjT_mulVec_mkSw, smul_mkSw, mkSw_eq_iff]
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩ <;> norm_num

-- FALSE instance: at the non-secular `θ = 1` it is not an eigenvector (`(A x)_c = -1/2 ≠ x_c`)
theorem test_secVec_not_eigen_3 :
    adjT (![3] : Fin 1 → ℕ) *ᵥ secVec (![3] : Fin 1 → ℕ) 1 ≠
      (1 : ℝ) • secVec (![3] : Fin 1 → ℕ) 1 := by
  rw [secVec_eq_mkSw, adjT_mulVec_mkSw, smul_mkSw, Ne, mkSw_eq_iff]
  rintro ⟨h, -, -⟩
  norm_num at h

/-! ## The switchings of Proposition 5.6 -/

theorem isSwitching_mkSw {k : ℕ} (a : Fin k → ℕ) {c : ℝ} {m : Fin k → ℝ}
    {l : (i : Fin k) → Fin (a i) → ℝ} (hc : c = 1 ∨ c = -1) (hm : ∀ i, m i = 1 ∨ m i = -1)
    (hl : ∀ i j, l i j = 1 ∨ l i j = -1) : IsSwitching (mkSw a c m l) := by
  intro v
  rcases v with _ | ⟨i, _ | j⟩
  · exact hc
  · exact hm i
  · exact hl i j

theorem ite_pm (p : Prop) [Decidable p] :
    (if p then (1 : ℝ) else -1) = 1 ∨ (if p then (1 : ℝ) else -1) = -1 := by
  split_ifs <;> simp

theorem ite_mp (p : Prop) [Decidable p] :
    (if p then (-1 : ℝ) else 1) = 1 ∨ (if p then (-1 : ℝ) else 1) = -1 := by
  split_ifs <;> simp

-- Prop 5.6(a): "s_c = σ_1 = σ_2 = 1; the leaves of v_1 get +1, +1 and those of v_2 get -1, -1"
theorem test_sw56a :
    sw56a none = 1 ∧ sw56a (some ⟨0, none⟩) = 1 ∧ sw56a (some ⟨1, none⟩) = 1 ∧
    (∀ j, sw56a (some ⟨0, some j⟩) = 1) ∧ (∀ j, sw56a (some ⟨1, some j⟩) = -1) := by
  refine ⟨rfl, rfl, rfl, fun j => ?_, fun j => ?_⟩ <;> simp only [sw56a, mkSw] <;> norm_num

theorem test_isSwitching_56a : IsSwitching sw56a :=
  isSwitching_mkSw _ (Or.inl rfl) (fun _ => Or.inl rfl) (fun i _ => ite_pm (i = 0))

-- Prop 5.6(b): "s_c = 1; +1 on the two leaf neighbours of c; -1 on the third neighbour v of c,
-- and +1, -1 on the two leaves of v" (`v = v_1`, the leaf neighbours are `v_2`, `v_3`)
theorem test_sw56b :
    sw56b none = 1 ∧ sw56b (some ⟨0, none⟩) = -1 ∧ sw56b (some ⟨1, none⟩) = 1 ∧
    sw56b (some ⟨2, none⟩) = 1 ∧ sw56b (some ⟨0, some ⟨0, by decide⟩⟩) = 1 ∧
    sw56b (some ⟨0, some ⟨1, by decide⟩⟩) = -1 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [sw56b, mkSw] <;> norm_num

theorem test_isSwitching_56b : IsSwitching sw56b :=
  isSwitching_mkSw _ (Or.inl rfl) (fun i => ite_mp (i = 0)) (fun _ j => ite_pm (j.val = 0))

-- FALSE instance: `sw56b` is not the all-ones switching (it is `-1` at `v_1`)
theorem test_sw56b_ne_one : sw56b ≠ fun _ => 1 := by
  intro h
  have := congrFun h (some ⟨0, none⟩)
  simp only [sw56b, mkSw] at this
  norm_num at this

/-! ## `sc`, `sig`, `lam`, `Sb`, `Lamb`, `Ab`, `Gs`, `Ps` -/

theorem Bset_3 : Bset (branchMS (![3] : Fin 1 → ℕ)) = {3} := by decide
theorem Bset_22 : Bset (branchMS (![2, 2] : Fin 2 → ℕ)) = {2} := by decide
theorem Bset_200 : Bset (branchMS (![2, 0, 0] : Fin 3 → ℕ)) = {0, 2} := by decide
theorem Ib_3 : Ib (![3] : Fin 1 → ℕ) 3 = {0} := by decide
theorem Ib_22 : Ib (![2, 2] : Fin 2 → ℕ) 2 = {0, 1} := by decide
theorem Ib_200_0 : Ib (![2, 0, 0] : Fin 3 → ℕ) 0 = {1, 2} := by decide
theorem Ib_200_2 : Ib (![2, 0, 0] : Fin 3 → ℕ) 2 = {0} := by decide

-- Prop 5.6, proof: the secular eigenvalues are `±2` for `T(2,2)` and `T(3)` (`R = t - 4`) and
-- `±1, ±2` for `T(2,0,0)` (`R = (t - 1)(t - 4)`)
theorem test_isSecular_22 (θ : ℝ) :
    IsSecular (branchMS (![2, 2] : Fin 2 → ℕ)) θ ↔ θ ^ 2 = 4 := by
  unfold IsSecular
  rw [show branchMS (![2, 2] : Fin 2 → ℕ) = {2, 2} by decide, test_secular_22]
  simp [sub_eq_zero, map_ofNat]

theorem test_isSecular_200 (θ : ℝ) :
    IsSecular (branchMS (![2, 0, 0] : Fin 3 → ℕ)) θ ↔ θ ^ 2 = 1 ∨ θ ^ 2 = 4 := by
  unfold IsSecular
  rw [show branchMS (![2, 0, 0] : Fin 3 → ℕ) = {2, 0, 0} by decide, test_secular_200]
  simp [sub_eq_zero, map_ofNat]

/-! ### `T(2,2)`, `sw56a` -/

-- Prop 5.6(a): leaf sums `λ_1 = 2`, `λ_2 = -2`
theorem test_lam_56a : lam (![2, 2] : Fin 2 → ℕ) sw56a 0 = 2 ∧
    lam (![2, 2] : Fin 2 → ℕ) sw56a 1 = -2 := by
  constructor <;>
  · simp only [lam, sw56a, mkSw]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num

-- `S_2 = σ_1 + σ_2 = 2`, `Λ_2 = 0`, `A_2 = s_c k_2 + Λ_2 = 2`
theorem test_data_56a :
    sc (![2, 2] : Fin 2 → ℕ) sw56a = 1 ∧ Sb (![2, 2] : Fin 2 → ℕ) sw56a 2 = 2 ∧
    Lamb (![2, 2] : Fin 2 → ℕ) sw56a 2 = 0 ∧ Challenge.Ab (![2, 2] : Fin 2 → ℕ) sw56a 2 = 2 := by
  have hk : kb (branchMS (![2, 2] : Fin 2 → ℕ)) 2 = 2 := by decide
  have hL : Lamb (![2, 2] : Fin 2 → ℕ) sw56a 2 = 0 := by
    unfold Lamb
    rw [Ib_22, Finset.sum_pair (by decide), test_lam_56a.1, test_lam_56a.2]
    norm_num
  refine ⟨rfl, ?_, hL, ?_⟩
  · unfold Sb
    rw [Ib_22, Finset.sum_pair (by decide)]
    simp only [sig, sw56a, mkSw]
    norm_num
  · unfold Challenge.Ab
    rw [hL, hk]
    simp only [sc, sw56a, mkSw]
    norm_num

-- Prop 5.6(a), proof: "G = (2 + 2θ)/2 = 1 + θ ∈ {3, -1}" (`G = (A_2 + S_2 θ)/(t - 2)`, `t = 4`)
theorem Gs_56a (θ : ℝ) : Gs (![2, 2] : Fin 2 → ℕ) sw56a θ = (2 + 2 * θ) / (θ ^ 2 - 2) := by
  unfold Gs
  rw [Bset_22, Finset.sum_singleton, test_data_56a.2.2.2, test_data_56a.2.1]
  norm_num

theorem test_Gs_56a : Gs (![2, 2] : Fin 2 → ℕ) sw56a 2 = 3 ∧
    Gs (![2, 2] : Fin 2 → ℕ) sw56a (-2) = -1 := by
  rw [Gs_56a, Gs_56a]
  norm_num

/-! ### `T(2,0,0)`, `sw56b` -/

-- Prop 5.6(b): `s_c = 1`, `σ = (-1, 1, 1)`, all leaf sums `0`
theorem test_sc_sig_56b :
    sc (![2, 0, 0] : Fin 3 → ℕ) sw56b = 1 ∧ sig (![2, 0, 0] : Fin 3 → ℕ) sw56b 0 = -1 ∧
    sig (![2, 0, 0] : Fin 3 → ℕ) sw56b 1 = 1 ∧ sig (![2, 0, 0] : Fin 3 → ℕ) sw56b 2 = 1 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp only [sig, sw56b, mkSw] <;> norm_num

theorem test_lam_56b (i : Fin 3) : lam (![2, 0, 0] : Fin 3 → ℕ) sw56b i = 0 := by
  simp only [lam, sw56b, mkSw]
  rw [Fin.sum_univ_eq_sum_range (fun n => if n = 0 then (1 : ℝ) else -1)]
  fin_cases i <;> simp [Finset.sum_range_succ]

-- `S_0 = σ_2 + σ_3 = 2`, `S_2 = σ_1 = -1`, `Λ_0 = Λ_2 = 0`, `A_0 = s_c k_0 = 2`, `A_2 = 1`
theorem test_Sb_56b : Sb (![2, 0, 0] : Fin 3 → ℕ) sw56b 0 = 2 ∧
    Sb (![2, 0, 0] : Fin 3 → ℕ) sw56b 2 = -1 := by
  unfold Sb
  rw [Ib_200_0, Ib_200_2, Finset.sum_pair (by decide), Finset.sum_singleton]
  simp only [sig, sw56b, mkSw]
  norm_num

theorem test_Lamb_56b : Lamb (![2, 0, 0] : Fin 3 → ℕ) sw56b 0 = 0 ∧
    Lamb (![2, 0, 0] : Fin 3 → ℕ) sw56b 2 = 0 := by
  unfold Lamb
  simp [test_lam_56b]

theorem test_Ab_56b : Challenge.Ab (![2, 0, 0] : Fin 3 → ℕ) sw56b 0 = 2 ∧
    Challenge.Ab (![2, 0, 0] : Fin 3 → ℕ) sw56b 2 = 1 := by
  have h0 : kb (branchMS (![2, 0, 0] : Fin 3 → ℕ)) 0 = 2 := by decide
  have h2 : kb (branchMS (![2, 0, 0] : Fin 3 → ℕ)) 2 = 1 := by decide
  unfold Challenge.Ab
  rw [h0, h2, test_Lamb_56b.1, test_Lamb_56b.2, test_sc_sig_56b.1]
  norm_num

-- Prop 5.6(b), proof: "G = (2 + 2θ)/t + (1 - θ)/(t - 2)"
theorem Gs_56b (θ : ℝ) :
    Gs (![2, 0, 0] : Fin 3 → ℕ) sw56b θ = (2 + 2 * θ) / θ ^ 2 + (1 - θ) / (θ ^ 2 - 2) := by
  unfold Gs
  rw [Bset_200, Finset.sum_pair (by norm_num), test_Ab_56b.1, test_Ab_56b.2, test_Sb_56b.1,
    test_Sb_56b.2]
  push_cast
  ring

-- "... takes the values 4, -2, 1, 1 at θ = 1, -1, 2, -2" (the secular values: `R = (t-1)(t-4)`)
theorem test_Gs_56b :
    Gs (![2, 0, 0] : Fin 3 → ℕ) sw56b 1 = 4 ∧ Gs (![2, 0, 0] : Fin 3 → ℕ) sw56b (-1) = -2 ∧
    Gs (![2, 0, 0] : Fin 3 → ℕ) sw56b 2 = 1 ∧ Gs (![2, 0, 0] : Fin 3 → ℕ) sw56b (-2) = 1 := by
  simp only [Gs_56b]
  norm_num

-- Lemma 3.4: `P_s(t) = ∑_b A_b/(t - b) = 2/t + 1/(t - 2)` for `sw56b`
theorem test_Ps_56b (t : ℝ) : Ps (![2, 0, 0] : Fin 3 → ℕ) sw56b t = 2 / t + 1 / (t - 2) := by
  unfold Ps
  rw [Bset_200, Finset.sum_pair (by norm_num), test_Ab_56b.1, test_Ab_56b.2]
  push_cast
  ring

-- FALSE instance: `S_b` is summed over `I_b` only (`S_0 ≠ S_2`, and `S_0 ≠ ∑_i σ_i = 1`)
theorem test_Sb_56b_ne : Sb (![2, 0, 0] : Fin 3 → ℕ) sw56b 0 ≠ Sb (![2, 0, 0] : Fin 3 → ℕ) sw56b 2 ∧
    Sb (![2, 0, 0] : Fin 3 → ℕ) sw56b 0 ≠ ∑ i, sig (![2, 0, 0] : Fin 3 → ℕ) sw56b i := by
  rw [test_Sb_56b.1, test_Sb_56b.2, Fin.sum_univ_three, test_sc_sig_56b.2.1, test_sc_sig_56b.2.2.1,
    test_sc_sig_56b.2.2.2]
  norm_num

/-! ### `T(3)`, `sw56c` -/

theorem lam_56c : lam (![3] : Fin 1 → ℕ) sw56c 0 = -1 := by
  simp only [lam, sw56c, mkSw]
  rw [Fin.sum_univ_eq_sum_range (fun n => if n = 0 then (1 : ℝ) else -1)]
  norm_num [Finset.sum_range_succ]

theorem Gs_T3 (s : TV (![3] : Fin 1 → ℕ) → ℝ) (θ : ℝ) :
    Gs (![3] : Fin 1 → ℕ) s θ =
      (Challenge.Ab (![3] : Fin 1 → ℕ) s 3 + Sb (![3] : Fin 1 → ℕ) s 3 * θ) / (θ ^ 2 - 3) := by
  unfold Gs
  rw [Bset_3, Finset.sum_singleton]
  norm_num

theorem Ab_T3 (s : TV (![3] : Fin 1 → ℕ) → ℝ) :
    Challenge.Ab (![3] : Fin 1 → ℕ) s 3 = sc (![3] : Fin 1 → ℕ) s + lam (![3] : Fin 1 → ℕ) s 0 := by
  have hk : kb (branchMS (![3] : Fin 1 → ℕ)) 3 = 1 := by decide
  unfold Challenge.Ab Lamb
  rw [hk, Ib_3, Finset.sum_singleton]
  norm_num

theorem Sb_T3 (s : TV (![3] : Fin 1 → ℕ) → ℝ) :
    Sb (![3] : Fin 1 → ℕ) s 3 = sig (![3] : Fin 1 → ℕ) s 0 := by
  unfold Sb
  rw [Ib_3, Finset.sum_singleton]

-- Prop 5.6(c): `λ_1 = 1 - 1 - 1 = -1`, so `A_3 = s_c + λ_1 = 0`, `S_3 = σ_1 = 1`, `Λ_3 = -1`
theorem test_data_56c :
    lam (![3] : Fin 1 → ℕ) sw56c 0 = -1 ∧ Lamb (![3] : Fin 1 → ℕ) sw56c 3 = -1 ∧
    Challenge.Ab (![3] : Fin 1 → ℕ) sw56c 3 = 0 ∧ Sb (![3] : Fin 1 → ℕ) sw56c 3 = 1 := by
  refine ⟨lam_56c, ?_, ?_, ?_⟩
  · unfold Lamb
    rw [Ib_3, Finset.sum_singleton, lam_56c]
  · rw [Ab_T3, lam_56c]
    simp only [sc, sw56c, mkSw]
    norm_num
  · rw [Sb_T3]
    rfl

-- Prop 5.6(c), proof: "G = θ/(t - 3) = θ"
theorem Gs_56c (θ : ℝ) : Gs (![3] : Fin 1 → ℕ) sw56c θ = θ / (θ ^ 2 - 3) := by
  rw [Gs_T3, test_data_56c.2.2.1, test_data_56c.2.2.2]
  ring

-- review T3: "Gs ![3] sw56c θ = θ at θ = ±2"
theorem test_Gs_56c : Gs (![3] : Fin 1 → ℕ) sw56c 2 = 2 ∧
    Gs (![3] : Fin 1 → ℕ) sw56c (-2) = -2 := by
  rw [Gs_56c, Gs_56c]
  norm_num

-- Lemma 3.4 for `sw56c` (`σ_1 = 1`): `P_s = A_3/(t - 3) = 0`, and `G(θ) = σθ + P_s(t)` at `θ = ±2`
theorem test_Ps_56c (t : ℝ) : Ps (![3] : Fin 1 → ℕ) sw56c t = 0 := by
  unfold Ps
  rw [Bset_3, Finset.sum_singleton, test_data_56c.2.2.1, zero_div]

theorem test_lemma34_56c :
    Gs (![3] : Fin 1 → ℕ) sw56c 2 = 1 * 2 + Ps (![3] : Fin 1 → ℕ) sw56c (2 ^ 2) ∧
    Gs (![3] : Fin 1 → ℕ) sw56c (-2) = 1 * (-2) + Ps (![3] : Fin 1 → ℕ) sw56c ((-2) ^ 2) := by
  rw [test_Ps_56c, test_Ps_56c, test_Gs_56c.1, test_Gs_56c.2]
  norm_num

-- `secVec` and `G`: in the proof of Lemma 3.2,
-- `s · x^θ = s_c + ∑_i (σ_i θ + λ_i)/(t - a_i) = G_s(θ)` when `F(t) = 1`; for `T(3)`, `sw56c`,
-- `θ = 2` both sides are `2`
theorem test_secVec_dot_56c :
    secVec (![3] : Fin 1 → ℕ) 2 ⬝ᵥ sw56c = Gs (![3] : Fin 1 → ℕ) sw56c 2 := by
  rw [test_Gs_56c.1, dotProduct, secVec_eq_mkSw]
  have hs : sw56c =
      mkSw (![3] : Fin 1 → ℕ) 1 (fun _ => 1) (fun _ j => if j.val = 0 then 1 else -1) := rfl
  rw [hs, P8Basic.sum_TV]
  simp only [mkSw_none, mkSw_v, mkSw_l, Fin.sum_univ_one]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun n => if n = 0 then (1 : ℝ) else -1)]
  norm_num [Finset.sum_range_succ]

/-! ## `Ufun`, `Ubeta` (Section 4) -/

-- `T(3,1)`: `k_3 = k_1 = 1`, so `λ° = (-1, -1)` and `U(t) = -1/(t - 1) - 1/(t - 3)`; `U(5) = -3/4`
theorem test_Ufun_31 : Ufun (![3, 1] : Fin 2 → ℕ) 5 = -3 / 4 := by
  unfold Ufun
  rw [show (Bset (branchMS (![3, 1] : Fin 2 → ℕ))).filter (fun b => 1 ≤ b) = {1, 3} by decide,
    Finset.sum_pair (by norm_num), show LamStdB (![3, 1] : Fin 2 → ℕ) 1 = -1 by decide,
    show LamStdB (![3, 1] : Fin 2 → ℕ) 3 = -1 by decide]
  norm_num

-- `U_β(t) = U(t) - Λ°_β/(t - β)`: `U_3(5) = -1/4`, `U_1(5) = -1/2`
theorem test_Ubeta_31 : Ubeta (![3, 1] : Fin 2 → ℕ) 3 5 = -1 / 4 ∧
    Ubeta (![3, 1] : Fin 2 → ℕ) 1 5 = -1 / 2 := by
  unfold Ubeta
  rw [test_Ufun_31, show LamStdB (![3, 1] : Fin 2 → ℕ) 1 = -1 by decide,
    show LamStdB (![3, 1] : Fin 2 → ℕ) 3 = -1 by decide]
  norm_num

-- `T(2,2)`: `λ° = (0, -2)` ("0, -2, 0, -2, … along I_b"), `U(t) = -2/(t - 2)`, `U_2 = 0`
theorem test_Ufun_22 (t : ℝ) : Ufun (![2, 2] : Fin 2 → ℕ) t = -2 / (t - 2) := by
  unfold Ufun
  rw [show (Bset (branchMS (![2, 2] : Fin 2 → ℕ))).filter (fun b => 1 ≤ b) = {2} by decide,
    Finset.sum_singleton, show LamStdB (![2, 2] : Fin 2 → ℕ) 2 = -2 by decide]
  norm_num

theorem test_Ubeta_22 (t : ℝ) : Ubeta (![2, 2] : Fin 2 → ℕ) 2 t = 0 := by
  unfold Ubeta
  rw [test_Ufun_22, show LamStdB (![2, 2] : Fin 2 → ℕ) 2 = -2 by decide]
  norm_num

-- Lemma 4.2, (4.1): `sw56c` is the member `s_{1,-1}` of the leaf row of `β = 3` of `T(3)`, and
-- `G(θ) = θ + ε + U_3(t) + Λ/(t - 3)` at the secular `θ = 2` (`U_3 = 0`)
theorem test_leafG_56c :
    Gs (![3] : Fin 1 → ℕ) sw56c 2 =
      2 + (1 : ℤ) + Ubeta (![3] : Fin 1 → ℕ) 3 (2 ^ 2) +
        ((-1 : ℤ) : ℝ) / (2 ^ 2 - ((3 : ℕ) : ℝ)) := by
  have hU : Ubeta (![3] : Fin 1 → ℕ) 3 (2 ^ 2) = 0 := by
    unfold Ubeta Ufun
    rw [show (Bset (branchMS (![3] : Fin 1 → ℕ))).filter (fun b => 1 ≤ b) = {3} by decide,
      Finset.sum_singleton, sub_self]
  rw [hU, test_Gs_56c.1]
  norm_num

end P8Tests
