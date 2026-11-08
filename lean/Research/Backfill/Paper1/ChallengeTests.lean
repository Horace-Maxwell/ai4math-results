import Research.Backfill.Paper1.Challenge

/-!
# Known-answer tests for the custom definitions of `Challenge.lean` (addendum 1, item 2)

Every custom definition is tested on small cases, reproducing numbers printed in the paper
wherever the paper prints one (the location is given in each comment), and at least one instance
that must come out false. Proofs use `norm_num`/`simp`/`decide` only.
-/

set_option autoImplicit false

namespace BackfillPaper1.ChallengeTests

open BackfillPaper1.Challenge Finset

/-! ### `tEntry`: the matrices `T_1` (Section 9) and `T_2` (Section 11) -/

-- Section 9: `T_1(p) = [[-R, R], [R, 1]]`, `R = p - 1`.
example (x : ℝ) : tEntry 1 x 0 0 = -(x - 1) ∧ tEntry 1 x 0 1 = x - 1 ∧
    tEntry 1 x 1 0 = x - 1 ∧ tEntry 1 x 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [tEntry]

-- Section 11: `T_2(p) = [[0, -pR, pR], [-pR, R², R], [pR, R, 1]]`.
example (x : ℝ) : tEntry 2 x 0 0 = 0 ∧ tEntry 2 x 0 1 = -(x * (x - 1)) ∧
    tEntry 2 x 0 2 = x * (x - 1) ∧ tEntry 2 x 1 1 = (x - 1) ^ 2 ∧ tEntry 2 x 1 2 = x - 1 ∧
    tEntry 2 x 2 0 = x * (x - 1) ∧ tEntry 2 x 2 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [tEntry]

-- Row sums `T_k(x) 1 = x^k e_k` (Section 2, [JY, (2.5)]) for `k = 2`, `x = 5`.
example : tMulVec 2 5 (fun _ => 1) 0 = 0 ∧ tMulVec 2 5 (fun _ => 1) 1 = 0 ∧
    tMulVec 2 5 (fun _ => 1) 2 = 25 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [tMulVec, tEntry, Finset.sum_range_succ]

-- false instance: `t_00` of `T_2` is not `1`
example : tEntry 2 5 0 0 ≠ 1 := by norm_num [tEntry]

/-! ### `tMulVec`, `l1`, `dNorm`, `sAlt`: Section 11 lists `M g_k` for `p = 3` -/

-- proof of Lemma 29: `Mg_1 = (12,-8,5)`, `Mg_2 = (-12,-4,7)`, `Mg_3 = (0,-12,3)`, `Mg_4 = (0,0,9)`
example : tMulVec 2 3 sAlt 0 = 12 ∧ tMulVec 2 3 sAlt 1 = -8 ∧ tMulVec 2 3 sAlt 2 = 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [tMulVec, tEntry, sAlt, Finset.sum_range_succ]

example : tMulVec 2 3 g2 0 = -12 ∧ tMulVec 2 3 g2 1 = -4 ∧ tMulVec 2 3 g2 2 = 7 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [tMulVec, tEntry, g2, Finset.sum_range_succ]

example : tMulVec 2 3 g3 0 = 0 ∧ tMulVec 2 3 g3 1 = -12 ∧ tMulVec 2 3 g3 2 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [tMulVec, tEntry, g3, Finset.sum_range_succ]

example : tMulVec 2 3 g4 0 = 0 ∧ tMulVec 2 3 g4 1 = 0 ∧ tMulVec 2 3 g4 2 = 9 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [tMulVec, tEntry, g4, Finset.sum_range_succ]

-- Remark 17: `‖N y‖₁ = d_2(3) - 2 = 23` for `y = (1, 1, -1)`, and `d_2(3) = 25`
example : l1 2 (tMulVec 2 3 g2) = 23 := by
  norm_num [l1, tMulVec, tEntry, g2, Finset.sum_range_succ]

example : dNorm 2 3 = 25 := by
  norm_num [dNorm, l1, tMulVec, tEntry, sAlt, Finset.sum_range_succ]

-- `d_0 = 1` (Section 2 convention)
example (x : ℝ) : dNorm 0 x = 1 := by norm_num [dNorm, l1, tMulVec, tEntry, sAlt]

example : sAlt 0 = 1 ∧ sAlt 3 = -1 := by norm_num [sAlt]

-- false instance
example : dNorm 2 3 ≠ 23 := by
  norm_num [dNorm, l1, tMulVec, tEntry, sAlt, Finset.sum_range_succ]

/-! ### `dClosed`, `deltaK` (Section 8: `d_1 = 3x-4`, `δ_1 = x-2`, `d_2 = 5x²-8x+4`,
`δ_2 = x²-2x+2`) -/

example (x : ℝ) : dClosed 1 x = 3 * x - 4 := by
  simp [dClosed]; ring

example (x : ℝ) : dClosed 2 x = 5 * x ^ 2 - 8 * x + 4 := by
  simp [dClosed, Finset.sum_range_succ]; ring

example (x : ℝ) (hx : x + 1 ≠ 0) : deltaK 1 x = x - 2 := by
  rw [deltaK, div_eq_iff hx]; ring

example (x : ℝ) (hx : x + 1 ≠ 0) : deltaK 2 x = x ^ 2 - 2 * x + 2 := by
  rw [deltaK, div_eq_iff hx]; ring

-- the numbers behind Remark 16: `d_3(3) = 101`, `δ_3(3) = 13`, `d_3(5) = 611`, `δ_3(5) = 83`
example : dClosed 3 3 = 101 ∧ deltaK 3 3 = 13 ∧ dClosed 3 5 = 611 ∧ deltaK 3 5 = 83 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [dClosed, deltaK, Finset.sum_range_succ]

-- Remark 16: `½[135 + 11·101] - 3·13 = 584`, `½[375 + 5·611] - 83 = 1632`
example : ((135 : ℝ) + (3 * 5 - 4) * dClosed 3 3) / 2 - (5 - 2) * deltaK 3 3 = 584 := by
  norm_num [dClosed, deltaK, Finset.sum_range_succ]

example : ((375 : ℝ) + (3 * 3 - 4) * dClosed 3 5) / 2 - (3 - 2) * deltaK 3 5 = 1632 := by
  norm_num [dClosed, deltaK, Finset.sum_range_succ]

-- false instance
example : dClosed 2 3 ≠ 24 := by norm_num [dClosed, Finset.sum_range_succ]

/-! ### `z` (path, Section 3) and `mu`, `cc`, `muInf` (Sections 4, 9)
Remark 17: for `x = 3`, `y = (1, 1, -1)`: `z_1 = -1`, `z_0 = 1/3`, `z_{-1} = 7/9`.
Section 9: `μ_∞ = 1/2`, `c_0 = 4/3` for `x = 3`; `μ_0 = 1/3`, `μ_1 = 5/9`. -/

example : z 3 2 g2 1 = -1 ∧ z 3 2 g2 0 = 1 / 3 ∧ z 3 2 g2 (-1) = 7 / 9 := by
  refine ⟨?_, ?_, ?_⟩
  · show zRev 3 2 g2 0 = -1
    norm_num [zRev, g2]
  · show zRev 3 2 g2 1 = 1 / 3
    norm_num [zRev, g2]
  · show zRev 3 2 g2 2 = 7 / 9
    norm_num [zRev, g2]

example : mu 3 (-1) = 1 ∧ mu 3 0 = 1 / 3 ∧ mu 3 1 = 5 / 9 ∧ cc 3 0 = 4 / 3 ∧ muInf 3 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show muSeq 3 0 = 1
    norm_num [muSeq]
  · show muSeq 3 1 = 1 / 3
    norm_num [muSeq]
  · show muSeq 3 2 = 5 / 9
    norm_num [muSeq]
  · show (3 - 1) * (1 + muSeq 3 0) / 3 = 4 / 3
    norm_num [muSeq]
  · norm_num [muInf]

-- false instance
example : z 3 2 g2 (-1) ≠ 1 := by
  show zRev 3 2 g2 2 ≠ 1
  norm_num [zRev, g2]

/-! ### `NA` (Remark 17: `NA(y) = {0}` for `y = (1, 1, -1)`; `NA ⊆ {0, 1}` here) -/

example : 0 ∈ NA 2 g2 ∧ 1 ∉ NA 2 g2 := by
  refine ⟨?_, ?_⟩ <;> rw [NA, Finset.mem_filter] <;> norm_num [g2]

/-! ### `hcell` (Lemma 10 case analysis; Section 10: `h_μ(A, PA/μ) = 0`) -/

-- `0 ≤ B ≤ A`: `h = -2(P-μ)B`;  `B > A`: `h = 2(μB - PA)`;  `-PA ≤ B < 0`: `h = 0`;
-- `B < -PA`: `h = 2μ(|B| - PA)`;  and `h_μ(A, PA/μ) = 0`.
example : hcell 4 (1 / 2) 3 1 = -7 ∧ hcell 4 (1 / 2) 1 3 = -5 ∧ hcell 4 (1 / 2) 1 (-2) = 0 ∧
    hcell 4 (1 / 2) 1 (-6) = 2 ∧ hcell 4 (1 / 2) 1 8 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [hcell, abs_of_nonneg, abs_of_nonpos]

example : hcell 4 (1 / 2) 1 (-6) ≠ 0 := by norm_num [hcell, abs_of_nonneg, abs_of_nonpos]

/-! ### `triple`, `l1Mat`, `divMat` (Proposition 6 with the numbers of Remark 16, `n = 15`) -/

-- `E(ICG_15({3,5})) = 4φ(15) = 32` and `E(ICG_15({5})) = 2p(q-1) = 20` (p = 5, q = 3)
example : l1Mat 1 1 (triple 1 1 5 3 (divMat 5 3 {5, 3})) = 32 := by
  norm_num [l1Mat, triple, divMat, tEntry, Finset.sum_range_succ]

example : l1Mat 1 1 (triple 1 1 5 3 (divMat 5 3 {5})) = 20 := by
  norm_num [l1Mat, triple, divMat, tEntry, Finset.sum_range_succ]

-- `K_15 = ICG_15({1,3,5})` has energy `2(pq-1) = 28`
example : l1Mat 1 1 (triple 1 1 5 3 (divMat 5 3 {1, 5, 3})) = 28 := by
  norm_num [l1Mat, triple, divMat, tEntry, Finset.sum_range_succ]

-- false instance
example : l1Mat 1 1 (triple 1 1 5 3 (divMat 5 3 {5})) ≠ 32 := by
  norm_num [l1Mat, triple, divMat, tEntry, Finset.sum_range_succ]

-- `triple` is the Mathlib matrix product `M Y Nᵀ` (checked for `a = b = 1`)
example (p q : ℝ) (Y : ℕ → ℕ → ℝ) (u v : Fin 2) :
    triple 1 1 p q Y u v =
      ((Matrix.of fun i j : Fin 2 => tEntry 1 p i j) * (Matrix.of fun i j : Fin 2 => Y i j) *
        Matrix.transpose (Matrix.of fun i j : Fin 2 => tEntry 1 q i j)) u v := by
  fin_cases u <;> fin_cases v <;>
    simp [triple, Matrix.mul_apply, Fin.sum_univ_two, Finset.sum_range_succ] <;> ring

/-! ### `Gval`, `Theta`, `Yminus`, `Yplus` (Remark 17 / Theorem 25 at `p = 5`, `q = 3`,
`(a, b) = (2, 2)`): `G(s_2 yᵀ) = 23 d_2(5) = 2047`, `Θ = 25·89 - 10·17 = 2055 = G + 4(p-3)`,
`G(Y⁻) = G(Y⁺) = Θ`. -/

example : Theta 2 2 5 3 = 2055 := by
  norm_num [Theta, dNorm, deltaK, l1, tMulVec, tEntry, sAlt, Finset.sum_range_succ]

example : Gval 2 2 5 3 (fun i j => sAlt i * g2 j) = 2047 := by
  norm_num [Gval, triple, tEntry, sAlt, g2, Finset.sum_range_succ]

example : Gval 2 2 5 3 Yminus = 2055 := by
  norm_num [Gval, triple, tEntry, sAlt, Yminus, Finset.sum_range_succ]

example : Gval 2 2 5 3 (Yplus 2 2) = 2055 := by
  norm_num [Gval, triple, tEntry, sAlt, Yplus, Finset.sum_range_succ]

-- false instance: `s_2 s_2ᵀ` (violates `y_{ab} = -1`) exceeds `Θ`
example : Gval 2 2 5 3 (fun i j => sAlt i * sAlt j) ≠ 2055 := by
  norm_num [Gval, triple, tEntry, sAlt, Finset.sum_range_succ]

example : Yplus 2 2 2 2 = -1 ∧ Yplus 2 2 0 0 = 1 ∧ Yminus 2 2 = -1 := by
  norm_num [Yplus, Yminus, sAlt]

/-! ### `DeltaC`, `rowAbsSum`, `psi`, `gPlus` (Section 11, (Deltas), `p = 5`, `R = 4`):
`Δ(g_2) = 2(R-1)² = 18`, `Δ(g_3) = 2(R²+1) = 34`, `Δ(g_4) = 4R² = 64`; `ω = (2pR, 2pR, p²)`;
Lemma 28 (a): `ψ_μ(s_2, m s_2) = 2(P-μ) m d_2(p)`; `g₊ = g_3` for `a = 2`. -/

example : DeltaC 2 5 g2 = 18 ∧ DeltaC 2 5 g3 = 34 ∧ DeltaC 2 5 g4 = 64 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [DeltaC, dNorm, l1, tMulVec, tEntry, sAlt, g2, g3, g4, Finset.sum_range_succ]

example : rowAbsSum 2 5 0 = 40 ∧ rowAbsSum 2 5 1 = 40 ∧ rowAbsSum 2 5 2 = 25 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [rowAbsSum, tEntry, Finset.sum_range_succ]

-- `P = q - 1 = 2`, `μ = 1/3`, `m = 1/2`, `d_2(5) = 89`: `2 (2 - 1/3) (1/2) 89 = 445/3`
example : psi 2 5 3 (1 / 3) sAlt (fun i => 1 / 2 * sAlt i) = 445 / 3 := by
  norm_num [psi, DeltaC, dNorm, l1, tMulVec, tEntry, sAlt, hcell, Finset.sum_range_succ,
    abs_of_nonneg, abs_of_nonpos]

example : ∀ i ≤ 2, gPlus 2 i = g3 i := by
  intro i hi; interval_cases i <;> norm_num [gPlus, g3, sAlt]

example : DeltaC 2 5 g2 ≠ 0 := by
  norm_num [DeltaC, dNorm, l1, tMulVec, tEntry, sAlt, g2, Finset.sum_range_succ]

/-! ### `etaMap`, `Dhat1`, `Dhat2`, `Ik`, `FamF` (Section 12) at `q = 3` -/

-- `η_n(μ_j) = μ_{j+n}`: `η_1(μ_0) = μ_1 = 5/9`
example : etaMap 3 1 (1 / 3) = 5 / 9 ∧ Dhat1 3 = 5 / 3 ∧ Dhat2 3 = 25 / 9 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [etaMap, Dhat1, Dhat2]

-- `I_0 = [μ_0, μ_∞] = [1/3, 1/2]` for `a` even; `I_1 = [μ_∞, μ_1] ∪ {1}`
example : Ik 2 0 3 (1 / 3) ∧ Ik 2 1 3 1 ∧ ¬ Ik 2 0 3 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [Ik, mu, muSeq, muInf]

-- `(1, μ_0, (P - μ_0)/x) = (1, 1/3, 5/9) ∈ 𝓕_2`; `(1, 1/3, 1/2) ∉ 𝓕_2`
example : FamF 2 3 (1, 1 / 3, 5 / 9) ∧ ¬ FamF 2 3 (1, 1 / 3, 1 / 2) := by
  refine ⟨?_, ?_⟩ <;> norm_num [FamF, mu, muSeq, muInf]

/-! ### Divisor sets, admissibility, primes -/

-- Section 1: for `n = p²q³` the checkerboard set is `{1, p², pq, q², p²q², pq³}` (`p = 5, q = 3`)
example : evenSet 5 3 2 3 = {1, 25, 15, 9, 225, 135} := by unfold evenSet; decide

-- Remark 16 / `check_lesander.log`: the maximisers for `135 = 5·3³` are `{3,5,27,45}`, `{1,9,15}`
example : oddSet 5 3 1 3 = {3, 5, 27, 45} ∧ (evenSet 5 3 1 3).erase (5 * 3 ^ 3) = {1, 9, 15} := by
  unfold oddSet evenSet; decide

-- admissibility; false instances: `n` itself is not admissible, the empty set is not admissible
example : IsConnSet 15 {3, 5} ∧ ¬ IsConnSet 15 {15} ∧ ¬ IsConnSet 15 ∅ := by
  unfold IsConnSet; decide

example : IsConnSet 225 {1, 3, 25, 75, 45} := by unfold IsConnSet; decide

example : DistinctOddPrimes 5 3 ∧ ¬ DistinctOddPrimes 3 3 ∧ ¬ DistinctOddPrimes 2 3 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ⟨2, by norm_num⟩, ⟨1, by norm_num⟩⟩,
    fun h => h.2.2.1 rfl, fun h => ?_⟩
  obtain ⟨k, hk⟩ := h.2.2.2.1
  omega

example : ParamXR 3 4 ∧ ¬ ParamXR 3 3 := by norm_num [ParamXR]

/-! ### The graph `icg` (adjacency relation) and `negPt`, sign predicates -/

-- `ICG_6({1})` is the unitary Cayley graph on `Z/6`, the 6-cycle: `0 ~ 1`, `0 ~ 5`, `0 ≁ 2`, `0 ≁ 3`
example : (icg 6 {1}).Adj 0 1 ∧ (icg 6 {1}).Adj 0 5 ∧ ¬ (icg 6 {1}).Adj 0 2 ∧
    ¬ (icg 6 {1}).Adj 0 3 := by
  simp only [icg, SimpleGraph.fromRel_adj, icgRel]; decide

-- loopless even when `n ∈ D`
example : ¬ (icg 6 {6}).Adj 2 2 := by simp [icg]

/-! ### `MaxEnergy`: vacuous for `n = 1` (no proper divisors; every theorem here has
`n ≥ 15`), false as soon as `S` contains a set that is not admissible. -/

example (V : ℝ) : MaxEnergy 1 V ∅ := by
  refine ⟨fun D hD => by simp at hD, fun D hD => ?_⟩
  exfalso
  obtain ⟨x, hx⟩ := hD.1
  have hx1 := hD.2 hx
  simp at hx1

example (V : ℝ) : ¬ MaxEnergy 15 V {{15}} := by
  intro h
  have h15 := (h.1 {15} rfl).2 (Finset.mem_singleton_self 15)
  simp at h15

/-! ### `graphEnergy` / `energy` (Mathlib eigenvalues): the empty connection set gives the
edgeless graph, energy `0` (triviality test); a graph with an edge has nonzero energy. -/

example (n : ℕ) : energy n ∅ = 0 := by
  have h0 : (icg n ∅).adjMatrix ℝ = 0 := by
    ext i j
    have hij : ¬ (icg n ∅).Adj i j := by simp [icg, icgRel]
    rw [SimpleGraph.adjMatrix_apply, ite_eq_right hij, Matrix.zero_apply]
  have hev := ((icg n ∅).isHermitian_adjMatrix ℝ).eigenvalues_eq_zero_iff.mpr h0
  unfold energy graphEnergy
  simp [hev]

example : energy 2 {1} ≠ 0 := by
  have hadj : (icg 2 {1}).Adj 0 1 := by
    simp only [icg, SimpleGraph.fromRel_adj, icgRel]; decide
  have hne : (icg 2 {1}).adjMatrix ℝ ≠ 0 := by
    intro h
    have h01 := congrFun (congrFun h 0) 1
    rw [SimpleGraph.adjMatrix_apply, ite_eq_left hadj] at h01
    exact one_ne_zero h01
  have hev : ((icg 2 {1}).isHermitian_adjMatrix ℝ).eigenvalues ≠ 0 :=
    fun h => hne (((icg 2 {1}).isHermitian_adjMatrix ℝ).eigenvalues_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hev
  unfold energy graphEnergy
  intro hsum
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => abs_nonneg (((icg 2 {1}).isHermitian_adjMatrix ℝ).eigenvalues j))).mp hsum i
    (Finset.mem_univ i)
  exact hi (abs_eq_zero.mp hz)

example : negPt (-3) = 3 ∧ negPt 2 = 0 := by norm_num [negPt]

example : IsSignVec 2 g2 ∧ ¬ IsPmAlt 2 g2 ∧ IsPmAlt 2 sAlt := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi; interval_cases i <;> norm_num [g2]
  · rintro (h | h)
    · have := h 1 (by norm_num); norm_num [g2, sAlt] at this
    · have := h 0 (by norm_num); norm_num [g2, sAlt] at this
  · left; intro i _; rfl

/-! ## Tests added in version 2 (review of 2026-09-27, items T1–T3 and §2) -/

/-! ### `triple` is Mathlib's `M * Y * Nᵀ` for ALL sizes (reviewer's lemma, D4/T3) -/

theorem triple_eq_matrix (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) (u : Fin (a + 1)) (v : Fin (b + 1)) :
    triple a b p q Y u v =
      ((Matrix.of fun i j : Fin (a + 1) => tEntry a p i j) *
        (Matrix.of fun (i : Fin (a + 1)) (j : Fin (b + 1)) => Y i j) *
        Matrix.transpose (Matrix.of fun i j : Fin (b + 1) => tEntry b q i j)) u v := by
  simp only [triple, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul,
    Finset.sum_range]
  exact Finset.sum_comm

/-! ### `zetaPath`, `psiCol` (T1): Remark 17's matrix `s_2 (1,1,-1)ᵀ`, `p = 5`, `q = 3`;
Lemma 28 (a) with `J = 0`: `ψ_0 = 2(P - μ) m d_2(p) = 2·1·(1/3)·89 = 178/3`; Lemma 24: `ψ_j(Y⁺) = 0`. -/

example : zetaPath 2 3 (fun i j => sAlt i * g2 j) 0 0 = 1 / 3 ∧
    zetaPath 2 3 (fun i j => sAlt i * g2 j) (-1) 1 = -7 / 9 := by
  refine ⟨?_, ?_⟩
  · show zRev 3 2 (fun l => sAlt 0 * g2 l) 1 = 1 / 3
    norm_num [zRev, sAlt, g2]
  · show zRev 3 2 (fun l => sAlt 1 * g2 l) 2 = -7 / 9
    norm_num [zRev, sAlt, g2]

example : psiCol 2 2 5 3 (fun i j => sAlt i * g2 j) 0 = 178 / 3 := by
  show psi 2 5 3 1 (fun i => sAlt i * g2 0) (fun i => zRev 3 2 (fun l => sAlt i * g2 l) 1) = 178 / 3
  norm_num [psi, DeltaC, dNorm, l1, tMulVec, tEntry, sAlt, g2, hcell, zRev, Finset.sum_range_succ,
    abs_of_nonneg, abs_of_nonpos]

example : psiCol 2 2 5 3 (Yplus 2 2) 0 = 0 := by
  show psi 2 5 3 1 (fun i => Yplus 2 2 i 0) (fun i => zRev 3 2 (fun l => Yplus 2 2 i l) 1) = 0
  norm_num [psi, DeltaC, dNorm, l1, tMulVec, tEntry, sAlt, Yplus, hcell, zRev, Finset.sum_range_succ,
    abs_of_nonneg, abs_of_nonpos]

-- false instance
example : psiCol 2 2 5 3 (fun i j => sAlt i * g2 j) 0 ≠ 0 := by
  show psi 2 5 3 1 (fun i => sAlt i * g2 0) (fun i => zRev 3 2 (fun l => sAlt i * g2 l) 1) ≠ 0
  norm_num [psi, DeltaC, dNorm, l1, tMulVec, tEntry, sAlt, g2, hcell, zRev, Finset.sum_range_succ,
    abs_of_nonneg, abs_of_nonpos]

/-! ### Sign predicates, `col`, regions (T2) -/

example : IsSignMat 2 2 (Yplus 2 2) := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [Yplus, sAlt]

example : ¬ IsSignMat 1 1 (fun _ _ => 0) := by
  intro h
  rcases h 0 (by norm_num) 0 (by norm_num) with h0 | h0 <;> norm_num at h0

example : IsPmCheckerboard 2 2 Yminus := Or.inr (fun _ _ _ _ => rfl)

example : ¬ IsPmCheckerboard 2 2 (Yplus 2 2) := by
  rintro (h | h)
  · have := h 2 (by norm_num) 2 (by norm_num); norm_num [Yplus, sAlt] at this
  · have := h 0 (by norm_num) 0 (by norm_num); norm_num [Yplus, sAlt] at this

example : MatEq 2 2 Yminus (fun i j => -(sAlt i * sAlt j)) := fun _ _ _ _ => rfl

example : ¬ MatEq 2 2 Yminus (Yplus 2 2) := by
  intro h
  have := h 0 (by norm_num) 0 (by norm_num)
  norm_num [Yminus, Yplus, sAlt] at this

example : col (fun i j => (i : ℝ) + 10 * j) 1 2 = 12 := by norm_num [col]

example : IsPm3 (fun i => -g3 i) g3 ∧ ¬ IsPm3 g2 g3 := by
  refine ⟨Or.inr fun _ _ => rfl, ?_⟩
  rintro (h | h)
  · have := h 1 (by norm_num); norm_num [g2, g3] at this
  · have := h 0 (by norm_num); norm_num [g2, g3] at this

example : Region1 5 3 ∧ Region2 3 5 ∧ Regions 7 3 ∧ ¬ Regions 3 3 ∧ ¬ Regions 5 2 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨rfl, by norm_num⟩, Or.inl ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · rintro (⟨h, _⟩ | ⟨_, h⟩) <;> norm_num at h
  · rintro (⟨_, h⟩ | ⟨h, _⟩) <;> norm_num at h

/-! ### `CondS` (false instance with `P_min = 0`; the positive instances are what the phase-2
certificates establish; the reviewer's exact-arithmetic evaluation found 0 failures, see
STATEMENTS.md) -/

example : ¬ CondS 3 5 0 := by
  intro h
  have hc : IsSignVec 3 (fun _ => 1) := fun _ _ => Or.inl rfl
  have hn : ¬ IsPmAlt 3 (fun _ => 1) := by
    rintro (h1 | h1)
    · have := h1 1 (by norm_num); norm_num [sAlt] at this
    · have := h1 0 (by norm_num); norm_num [sAlt] at this
  have h0 := h _ hc hn
  have hs : 0 ≤ ∑ i ∈ range (3 + 1), max 0 (rowAbsSum 3 5 i - 0 * |tMulVec 3 5 (fun _ => 1) i|) :=
    Finset.sum_nonneg (fun i _ => le_max_left _ _)
  rw [zero_mul] at h0
  linarith

-- `CondAll` is the conjunction of the three conditions
example (a : ℕ) (p q Pm : ℝ) : CondAll a p q Pm ↔ CondS a p Pm ∧ CondF a p q ∧ CondC a p q :=
  Iff.rfl

/-! ### `SignConclusion` needs the region: at `p = q = 3` (outside both regions) a third sign
matrix attains `Θ` (reviewer's matrix), so `SignConclusion 2 3 3` is false. -/

def Y3 : ℕ → ℕ → ℝ := fun i j =>
  if i = 0 then (if j = 2 then -1 else 1)
  else if i = 1 then (if j = 1 then -1 else 1) else (if j = 1 then 1 else -1)

example : Gval 2 2 3 3 Y3 = Theta 2 2 3 3 := by
  norm_num [Y3, Gval, Theta, triple, dNorm, deltaK, l1, tMulVec, tEntry, sAlt, Finset.sum_range_succ]

example : ¬ SignConclusion 2 3 3 := by
  intro h
  have hs : IsSignMat 2 2 Y3 := by
    intro i hi j hj
    interval_cases i <;> interval_cases j <;> norm_num [Y3]
  have hc : Y3 2 2 = -1 := by norm_num [Y3]
  have hG : Gval 2 2 3 3 Y3 = Theta 2 2 3 3 := by
    norm_num [Y3, Gval, Theta, triple, dNorm, deltaK, l1, tMulVec, tEntry, sAlt,
      Finset.sum_range_succ]
  rcases (h 2 (by norm_num) (by norm_num) Y3 hs hc).2.mp hG with hm | hp
  · have := hm 0 (by norm_num) 0 (by norm_num); norm_num [Y3, Yminus, sAlt] at this
  · have := hp 0 (by norm_num) 1 (by norm_num); norm_num [Y3, Yplus, sAlt] at this

/-! ### `IsMultSet`, `MultMaxEnergy` (Remark 16, §2 of the review) -/

example : IsMultSet 5 3 1 3 {1, 9} := ⟨{0}, {0, 2}, by decide, by decide, by decide⟩

-- the maximiser `{1}` of Remark 16 (i) is multiplicative
example : IsMultSet 5 3 1 1 {1} := ⟨{0}, {0}, by decide, by decide, by decide⟩

example : ¬ IsMultSet 5 3 1 3 {3, 5, 27, 45} := by
  rintro ⟨A, B, hA, hB, hD⟩
  have h3 : (3 : ℕ) ∈ (A ×ˢ B).image (fun ij => 5 ^ ij.1 * 3 ^ ij.2) := hD ▸ by decide
  have h5 : (5 : ℕ) ∈ (A ×ˢ B).image (fun ij => 5 ^ ij.1 * 3 ^ ij.2) := hD ▸ by decide
  have h1 : (1 : ℕ) ∉ (A ×ˢ B).image (fun ij => 5 ^ ij.1 * 3 ^ ij.2) := hD ▸ by decide
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists] at h3 h5 h1
  obtain ⟨i, j, ⟨hi, hj⟩, hij⟩ := h3
  obtain ⟨i', j', ⟨hi', hj'⟩, hij'⟩ := h5
  have hiA := hA hi; have hjB := hB hj; have hi'A := hA hi'; have hj'B := hB hj'
  simp only [Finset.mem_range] at hiA hjB hi'A hj'B
  interval_cases i <;> interval_cases j <;> norm_num at hij ;
    interval_cases i' <;> interval_cases j' <;> norm_num at hij' ;
      exact h1 ⟨0, 0, ⟨hi, hj'⟩, by norm_num⟩

-- false instance: for `n = 1` there is no admissible set, so no value is `Ẽ_max`
example (V : ℝ) : ¬ MultMaxEnergy 5 3 0 0 V := by
  rintro ⟨⟨D, hD, -, -⟩, -⟩
  obtain ⟨x, hx⟩ := hD.1
  have := hD.2 hx
  simp at this

/-! ### The claim abbreviations unfold to the expected instances -/

-- `EqualParityClaim 1 1` at `(p, q) = (5, 3)` is Remark 16 (i) for `n = 15`: value 32,
-- maximisers `{5, 3}` and `{1}`
example (h : EqualParityClaim 1 1) : MaxEnergy (5 ^ 1 * 3 ^ 1) 32 {{5, 3}, {1}} := by
  have h1 := h 5 3 ⟨by norm_num, by norm_num, by norm_num, ⟨2, by norm_num⟩, ⟨1, by norm_num⟩⟩
  have hV : ((((5 ^ 1 * 3 ^ 1 : ℕ) : ℝ) + dClosed 1 ((5 : ℕ) : ℝ) * dClosed 1 ((3 : ℕ) : ℝ)) / 2 -
      deltaK 1 ((5 : ℕ) : ℝ) * deltaK 1 ((3 : ℕ) : ℝ)) = 32 := by
    norm_num [dClosed, deltaK, Finset.sum_range_succ]
  have hO : oddSet 5 3 1 1 = {5, 3} := by unfold oddSet; decide
  have hE : (evenSet 5 3 1 1).erase (5 ^ 1 * 3 ^ 1) = {1} := by unfold evenSet; decide
  rw [hV, hO, hE] at h1
  exact h1

-- `SummaryOppositeParity` at `p = 5`, `q = 3`, `(a, b) = (2, 1)`: `n = 75`, value
-- `½[75 + d_2(5) d_1(3)] = ½[75 + 89·5] = 260`, unique maximiser `{p^i q^j : i + j even}`
example (h : SummaryOppositeParity) : MaxEnergy (5 ^ 2 * 3 ^ 1) 260 {evenSet 5 3 2 1} := by
  have h1 := h 5 3 2 1 ⟨by norm_num, by norm_num, by norm_num, ⟨2, by norm_num⟩, ⟨1, by norm_num⟩⟩
    (by norm_num) (by norm_num) ⟨1, by norm_num⟩
  have hV : ((((5 ^ 2 * 3 ^ 1 : ℕ) : ℝ) + dClosed 2 ((5 : ℕ) : ℝ) * dClosed 1 ((3 : ℕ) : ℝ)) / 2)
      = 260 := by
    norm_num [dClosed, Finset.sum_range_succ]
  rw [hV] at h1
  exact h1

-- `Section8OddSet` at `(5, 3)`, `(a, b) = (1, 1)`: `E(ICG_15({5, 3})) = 32 < 35`
example (h : Section8OddSet) : energy (5 ^ 1 * 3 ^ 1) {5, 3} = 32 := by
  have h1 := (h 5 3 1 1 ⟨by norm_num, by norm_num, by norm_num, ⟨2, by norm_num⟩, ⟨1, by norm_num⟩⟩
    (by norm_num) (by norm_num) ⟨1, by norm_num⟩).2.1
  have hO : oddSet 5 3 1 1 = {5, 3} := by unfold oddSet; decide
  rw [hO] at h1
  rw [h1]
  norm_num [dClosed, deltaK, Finset.sum_range_succ]

end BackfillPaper1.ChallengeTests
