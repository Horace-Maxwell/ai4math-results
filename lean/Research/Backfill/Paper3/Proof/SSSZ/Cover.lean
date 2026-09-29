import Research.Backfill.Paper3.Proof.SSSZ.Finner
import Research.Backfill.Paper3.Proof.SSSZ.Swap

/-!
# The biclique bound `P_G(q) ≤ P_d(q)^{n/(2d)}` for `d`-regular `G` and `0 ≤ q ≤ 1`

`P_d(q) = ∑_a C(d,a) (1 + q^a)^d = ∑_{T ⊆ N} (1 + q^{|T|})^d` for any `N` with `|N| = d`
(binomial theorem). Finner's inequality with the sets `N(v)` (each vertex lies in exactly `d`
of them) and `h_v(T) = (1 + q^{|T|})^d` gives `P_{G × K₂}(q) ≤ (P_d(q)^{1/d})^n`; with the
swapping inequality, `P_G(q)² ≤ (P_d(q)^{1/d})^n`, hence the bound.
-/

set_option autoImplicit false

open Finset BackfillPaper3.Challenge

namespace P3SSSZ

/-- `P_d(q)` as an explicit double sum. -/
theorem evalR_Pd (d : ℕ) (q : ℝ) :
    evalR (Pd d) q = ∑ a ∈ range (d + 1), ∑ b ∈ range (d + 1),
      ((d.choose a : ℝ) * (d.choose b : ℝ)) * q ^ (a * b) := by
  simp [evalR, Pd]

/-- `P_d(q) = ∑_a C(d,a) (1 + q^a)^d`. -/
theorem evalR_Pd_eq_sum (d : ℕ) (q : ℝ) :
    evalR (Pd d) q = ∑ a ∈ range (d + 1), (d.choose a : ℝ) * (1 + q ^ a) ^ d := by
  rw [evalR_Pd]
  refine sum_congr rfl fun a _ => ?_
  rw [add_comm (1 : ℝ) (q ^ a), add_pow, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [one_pow, mul_one, ← pow_mul]
  ring

/-- `∑_{T ⊆ N} (1 + q^{|T|})^d = P_d(q)` when `|N| = d`. -/
theorem sum_powerset_one_add_pow {α : Type*} (N : Finset α) (d : ℕ) (hN : #N = d) (q : ℝ) :
    ∑ T ∈ N.powerset, (1 + q ^ #T) ^ d = evalR (Pd d) q := by
  rw [sum_powerset_apply_card (fun k => (1 + q ^ k) ^ d), hN, evalR_Pd_eq_sum]
  simp only [nsmul_eq_mul]

theorem one_le_evalR_Pd (d : ℕ) {q : ℝ} (hq0 : 0 ≤ q) : 1 ≤ evalR (Pd d) q := by
  rw [← sum_powerset_one_add_pow (range d) d (card_range d) q]
  have h1 : (1 : ℝ) ≤ (1 + q ^ #(∅ : Finset ℕ)) ^ d := by
    rw [card_empty, pow_zero]
    exact one_le_pow₀ (by norm_num)
  exact h1.trans (single_le_sum (fun T _ => pow_nonneg (add_nonneg zero_le_one (pow_nonneg hq0 _)) _)
    (empty_mem_powerset _))

/-- `P_d(0) = 2^{d+1} - 1`. -/
theorem evalR_Pd_zero (d : ℕ) : evalR (Pd d) 0 = 2 ^ (d + 1) - 1 := by
  rw [evalR_Pd_eq_sum, sum_range_succ']
  have hs : ∑ a ∈ range d, (d.choose (a + 1) : ℝ) = 2 ^ d - 1 := by
    have h := Nat.sum_range_choose d
    rw [sum_range_succ', Nat.choose_zero_right] at h
    have h' : (∑ a ∈ range d, (d.choose (a + 1) : ℝ)) + 1 = 2 ^ d := by exact_mod_cast h
    linarith
  simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, zero_pow, add_zero, one_pow, mul_one,
    Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, hs]
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem evalR_edgePoly (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) :
    evalR (edgePoly G) q = ∑ A : Finset V, q ^ edgesIn G A := by
  simp [evalR, edgePoly]

/-- `P_G(0) = i_0(G)`, the number of independent sets. -/
theorem evalR_edgePoly_zero (G : SimpleGraph V) [DecidableRel G.Adj] :
    evalR (edgePoly G) 0 = iCount G 0 := by
  rw [evalR_edgePoly]
  simp only [zero_pow_eq, sum_boole, iCount, Nat.le_zero]

/-- Finner's inequality applied to the neighbourhoods of a `d`-regular graph. -/
theorem cover_le (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hd : d ≠ 0)
    (hG : G.IsRegularOfDegree d) {q : ℝ} (hq0 : 0 ≤ q) :
    ∑ A : Finset V, ∏ v, (1 + q ^ #(A ∩ G.neighborFinset v)) ≤
      (evalR (Pd d) q ^ ((d : ℝ)⁻¹)) ^ Fintype.card V := by
  have hdeg : ∀ l ∈ (univ : Finset V),
      #(univ.filter fun r => l ∈ G.neighborFinset r) = d := by
    intro l _
    have h : (univ.filter fun r => l ∈ G.neighborFinset r) = G.neighborFinset l := by
      ext r
      simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
    rw [h, G.card_neighborFinset_eq_degree, hG.degree_eq]
  have hF := finner (ι := V) d hd (univ : Finset V) (fun v => G.neighborFinset v)
    (fun _ => subset_univ _) hdeg (fun _ T => (1 + q ^ #T) ^ d)
    (fun _ _ => pow_nonneg (add_nonneg zero_le_one (pow_nonneg hq0 _)) _)
  have h1 : ∀ T : Finset V, ((1 + q ^ #T) ^ d) ^ ((d : ℝ)⁻¹) = 1 + q ^ #T :=
    fun T => Real.pow_rpow_inv_natCast (add_nonneg zero_le_one (pow_nonneg hq0 _)) hd
  have h2 : ∀ v, ∑ T ∈ (G.neighborFinset v).powerset, (1 + q ^ #T) ^ d = evalR (Pd d) q :=
    fun v => sum_powerset_one_add_pow _ d (by rw [G.card_neighborFinset_eq_degree, hG.degree_eq]) q
  simp only [powerset_univ, h1, h2, prod_const, card_univ] at hF
  exact hF

/-- **The biclique bound** for `d`-regular `G` and `0 ≤ q ≤ 1`. -/
theorem sssz_bound (d : ℕ) (hd : 1 ≤ d) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsRegularOfDegree d) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    evalR (edgePoly G) q ≤ evalR (Pd d) q ^ ((Fintype.card V : ℝ) / (2 * d)) := by
  have hd0 : d ≠ 0 := by omega
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hPd : 0 < evalR (Pd d) q := lt_of_lt_of_le one_pos (one_le_evalR_Pd d hq0)
  have hPG0 : 0 ≤ evalR (edgePoly G) q := by
    rw [evalR_edgePoly]
    exact sum_nonneg fun A _ => pow_nonneg hq0 _
  have hsq := swap G hq0 hq1
  rw [sum_pairs_psi, ← evalR_edgePoly] at hsq
  have hle := hsq.trans (cover_le G d hd0 hG hq0)
  have key : (evalR (Pd d) q ^ ((d : ℝ)⁻¹)) ^ Fintype.card V =
      (evalR (Pd d) q ^ ((Fintype.card V : ℝ) / (2 * d))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hPd.le, ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul hPd.le]
    congr 1
    field_simp
    push_cast
    ring
  rw [key] at hle
  exact (pow_le_pow_iff_left₀ hPG0 (Real.rpow_nonneg hPd.le _) two_ne_zero).mp hle

end P3SSSZ
