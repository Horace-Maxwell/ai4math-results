import Research.Backfill.Paper3.Proof.CD.Law
import Research.Backfill.Paper3.Proof.CD.Psi
import Research.Backfill.Paper3.Proof.CD.Gn

/-!
# Theorem D and Remark 11

Theorem D (`1/8 < γ < 1/2`): with `x = 2γd²` and a minimiser `q* > 1` of `ψ_x` over `[1, ∞)`,
Lemma 8(a) gives `U(mK) ≥ e^{m(ψ_x(q*) - β/4)}`, the Markov bound gives
`U(G_n) ≤ q*^{-mx} P_H(q*)^k P_d(q*)^r`, and Lemmas 6, 7 give `β = log(P_d(q*)²/P_H(q*)) > 0`;
for `m ≥ 3`, `k = ⌊m/2⌋ > m/4` closes the comparison. Remark 11 (`0 < γ < 1/8`) is the mirror
image with Lemma 8(b), a minimiser `q* < 1` over `(0, 1]`, and `D(q*) < 0`.
-/

set_option autoImplicit false

namespace P3CD

open Finset Filter SimpleGraph BackfillPaper3.Challenge P3Basic

/-- The comparison step: for `m ≥ 3`,
`q^{-mx} B^{⌊m/2⌋} A^{m mod 2} < exp(m (log A - x log q - log(A²/B)/4))` when `B < A²`. -/
theorem compare_step {q A B x : ℝ} (hq : 0 < q) (hA : 0 < A) (hB : 0 < B) (hAB : B < A ^ 2)
    {m : ℕ} (hm : 3 ≤ m) :
    q ^ (-((m : ℝ) * x)) * (B ^ (m / 2) * A ^ (m % 2)) <
      Real.exp (m * (Real.log A - x * Real.log q - Real.log (A ^ 2 / B) / 4)) := by
  have hβ : 0 < Real.log (A ^ 2 / B) := Real.log_pos ((one_lt_div hB).2 hAB)
  have hβeq : Real.log (A ^ 2 / B) = 2 * Real.log A - Real.log B := by
    rw [Real.log_div (by positivity) hB.ne', Real.log_pow]
    push_cast
    ring
  have hY : 0 < q ^ (-((m : ℝ) * x)) * (B ^ (m / 2) * A ^ (m % 2)) := by positivity
  rw [← Real.log_lt_iff_lt_exp hY, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hq, Real.log_pow, Real.log_pow]
  have hk : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) + ((m % 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod m 2).symm
  have h4 : (m : ℝ) < 4 * ((m / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : m < 4 * (m / 2))
  have hdiff : (m : ℝ) * (Real.log A - x * Real.log q - Real.log (A ^ 2 / B) / 4) -
      (-((m : ℝ) * x) * Real.log q +
        (((m / 2 : ℕ) : ℝ) * Real.log B + ((m % 2 : ℕ) : ℝ) * Real.log A)) =
      Real.log (A ^ 2 / B) * (4 * ((m / 2 : ℕ) : ℝ) - m) / 4 := by
    rw [hβeq, hk]
    ring
  have hpos : 0 < Real.log (A ^ 2 / B) * (4 * ((m / 2 : ℕ) : ℝ) - m) / 4 :=
    div_pos (mul_pos hβ (by linarith)) (by norm_num)
  linarith

theorem card_eq_KddUnion (m d : ℕ) :
    (Fintype.card (Fin m × (Fin d ⊕ Fin d)) : ℝ) = 2 * d * m := by
  rw [card_KddUnion]
  push_cast
  ring

theorem card_eq_GnV (d m : ℕ) : (Fintype.card (GnV d m) : ℝ) = 2 * d * m := by
  rw [card_GnV]
  push_cast
  ring

/-- `i_γ(m K_{d,d}) = #{A : e(A) ≤ m x}` with `x = 2γd²`. -/
theorem iGamma_KddUnion_eq (m d : ℕ) (γ : ℝ) :
    iGamma (KddUnion m d) d γ = #(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
      (edgesIn (KddUnion m d) A : ℝ) ≤ m * (2 * γ * (d : ℝ) ^ 2)) := by
  rw [iGamma_eq_card]
  congr 1
  apply Finset.filter_congr
  intro A _
  rw [card_eq_KddUnion]
  constructor <;> intro h <;> linarith

theorem iGamma_Gn_eq (d m : ℕ) (a₁ b₁ a₂ b₂ : Fin d) (γ : ℝ) :
    iGamma (Gn d m a₁ b₁ a₂ b₂) d γ = #(univ.filter fun A : Finset (GnV d m) =>
      (edgesIn (Gn d m a₁ b₁ a₂ b₂) A : ℝ) ≤ m * (2 * γ * (d : ℝ) ^ 2)) := by
  rw [iGamma_eq_card]
  congr 1
  apply Finset.filter_congr
  intro A _
  rw [card_eq_GnV]
  constructor <;> intro h <;> linarith

/-- Theorem D, part (i): `|V(G_n)| = 2dm`, `G_n` is `d`-regular and bipartite. -/
theorem thmD_facts (hB : TheoremBprime) (d m : ℕ) (hd : 2 ≤ d) (a₁ b₁ a₂ b₂ : Fin d) :
    Fintype.card (GnV d m) = 2 * d * m ∧ (Gn d m a₁ b₁ a₂ b₂).IsRegularOfDegree d ∧
      (Gn d m a₁ b₁ a₂ b₂).IsBipartite :=
  ⟨card_GnV d m, Gn_regular d m a₁ b₁ a₂ b₂ (hB d hd a₁ b₁ a₂ b₂).1,
    Gn_bipartite d m a₁ b₁ a₂ b₂ (hB d hd a₁ b₁ a₂ b₂).2.1⟩

/-- Theorem D, part (ii). -/
theorem thmD_main (h8 : Lemma8) (h6 : Lemma6) (h7 : Lemma7) (d : ℕ) (hd : 2 ≤ d) {γ : ℝ}
    (hγ1 : 1 / 8 < γ) (hγ2 : γ < 1 / 2) (a₁ b₁ a₂ b₂ : Fin d) :
    ∃ M₀ : ℕ, ∀ m ≥ M₀, iGamma (KddUnion m d) d γ < iGamma (Gn d m a₁ b₁ a₂ b₂) d γ := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have hx1 : (d : ℝ) ^ 2 / 4 < 2 * γ * (d : ℝ) ^ 2 := by nlinarith
  have hx2 : 2 * γ * (d : ℝ) ^ 2 < (d : ℝ) ^ 2 := by nlinarith
  obtain ⟨q, hq1, hmin⟩ := exists_qstar_gt d hd1 hx1 hx2
  have hq0 : 0 < q := by linarith
  have hA : 0 < Pf d q := Pf_pos d hq0.le
  have hB : 0 < evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q :=
    lt_of_lt_of_le one_pos (one_le_evalR_edgePoly _ hq0.le)
  have hAB : evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q < Pf d q ^ 2 := by
    have h := base_diff h6 d hd a₁ b₁ a₂ b₂ q
    have hD := (h7 d hd q hq0).1 hq1
    have : 0 < 2 * (q - 1) * evalR (Dpoly d) q := mul_pos (by linarith) hD
    linarith
  have hβ : 0 < Real.log (Pf d q ^ 2 / evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q) :=
    Real.log_pos ((one_lt_div hB).2 hAB)
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 (upper_tail h8 hd1 hx1 hx2 (L := psi d _ q) hmin
    (ε := Real.log (Pf d q ^ 2 / evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q) / 4) (by positivity))
  refine ⟨max M₁ 3, fun m hm => ?_⟩
  have hU := hM₁ m (le_of_max_le_left hm)
  have hm3 : 3 ≤ m := le_of_max_le_right hm
  have hG := card_gt_markov (Gn d m a₁ b₁ a₂ b₂) ((m : ℝ) * (2 * γ * (d : ℝ) ^ 2)) hq1.le
  rw [evalR_Gn] at hG
  have hC := compare_step hq0 hA hB hAB hm3 (x := 2 * γ * (d : ℝ) ^ 2)
  unfold psi at hU
  have key : (#(univ.filter fun A : Finset (GnV d m) =>
        (m : ℝ) * (2 * γ * (d : ℝ) ^ 2) < (edgesIn (Gn d m a₁ b₁ a₂ b₂) A : ℝ)) : ℝ) <
      (#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
        (m : ℝ) * (2 * γ * (d : ℝ) ^ 2) < (edgesIn (KddUnion m d) A : ℝ)) : ℝ) :=
    lt_of_le_of_lt hG (lt_of_lt_of_le hC hU)
  have key' := Nat.cast_lt.mp key
  have hK := card_le_add_card_gt (KddUnion m d) ((m : ℝ) * (2 * γ * (d : ℝ) ^ 2))
  have hGn := card_le_add_card_gt (Gn d m a₁ b₁ a₂ b₂) ((m : ℝ) * (2 * γ * (d : ℝ) ^ 2))
  rw [card_KddUnion] at hK
  rw [card_GnV] at hGn
  have hsum := hK.trans hGn.symm
  rw [iGamma_KddUnion_eq, iGamma_Gn_eq]
  omega

theorem theoremD (hB : TheoremBprime) (h8 : Lemma8) (h6 : Lemma6) (h7 : Lemma7) :
    TheoremD :=
  ⟨fun d m hd a₁ b₁ a₂ b₂ => thmD_facts hB d m hd a₁ b₁ a₂ b₂,
    fun d hd _ hγ1 hγ2 a₁ b₁ a₂ b₂ => thmD_main h8 h6 h7 d hd hγ1 hγ2 a₁ b₁ a₂ b₂⟩

/-- Remark 11. -/
theorem remark11_main (h8 : Lemma8) (h6 : Lemma6) (h7 : Lemma7) (d : ℕ) (hd : 2 ≤ d) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1 / 8) (a₁ b₁ a₂ b₂ : Fin d) :
    ∃ M₀ : ℕ, ∀ m ≥ M₀, iGamma (Gn d m a₁ b₁ a₂ b₂) d γ < iGamma (KddUnion m d) d γ := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have hx0 : 0 < 2 * γ * (d : ℝ) ^ 2 := by positivity
  have hx1 : 2 * γ * (d : ℝ) ^ 2 < (d : ℝ) ^ 2 / 4 := by nlinarith
  obtain ⟨q, hq0, hq1, hmin⟩ := exists_qstar_lt d hd1 hx0 hx1
  have hA : 0 < Pf d q := Pf_pos d hq0.le
  have hB : 0 < evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q :=
    lt_of_lt_of_le one_pos (one_le_evalR_edgePoly _ hq0.le)
  have hAB : evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q < Pf d q ^ 2 := by
    have h := base_diff h6 d hd a₁ b₁ a₂ b₂ q
    have hD := (h7 d hd q hq0).2 hq1
    have : 0 < 2 * (q - 1) * evalR (Dpoly d) q :=
      mul_pos_of_neg_of_neg (by linarith) hD
    linarith
  have hβ : 0 < Real.log (Pf d q ^ 2 / evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q) :=
    Real.log_pos ((one_lt_div hB).2 hAB)
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 (lower_tail h8 hd1 hx0 hx1 (L := psi d _ q) hmin
    (ε := Real.log (Pf d q ^ 2 / evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q) / 4) (by positivity))
  refine ⟨max M₁ 3, fun m hm => ?_⟩
  have hU := hM₁ m (le_of_max_le_left hm)
  have hm3 : 3 ≤ m := le_of_max_le_right hm
  have hG := card_le_markov (Gn d m a₁ b₁ a₂ b₂) ((m : ℝ) * (2 * γ * (d : ℝ) ^ 2)) hq0 hq1.le
  rw [evalR_Gn] at hG
  have hC := compare_step hq0 hA hB hAB hm3 (x := 2 * γ * (d : ℝ) ^ 2)
  unfold psi at hU
  have hsub : (#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
        (edgesIn (KddUnion m d) A : ℝ) < m * (2 * γ * (d : ℝ) ^ 2)) : ℝ) ≤
      (#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
        (edgesIn (KddUnion m d) A : ℝ) ≤ m * (2 * γ * (d : ℝ) ^ 2)) : ℝ) := by
    apply Nat.cast_le.2
    apply Finset.card_le_card
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    exact hA.le
  have key : (#(univ.filter fun A : Finset (GnV d m) =>
        (edgesIn (Gn d m a₁ b₁ a₂ b₂) A : ℝ) ≤ m * (2 * γ * (d : ℝ) ^ 2)) : ℝ) <
      (#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
        (edgesIn (KddUnion m d) A : ℝ) ≤ m * (2 * γ * (d : ℝ) ^ 2)) : ℝ) :=
    lt_of_le_of_lt hG (lt_of_lt_of_le hC (hU.trans hsub))
  rw [iGamma_KddUnion_eq, iGamma_Gn_eq]
  exact_mod_cast key

theorem remark11 (h8 : Lemma8) (h6 : Lemma6) (h7 : Lemma7) : Remark11 :=
  fun d hd _ hγ0 hγ1 a₁ b₁ a₂ b₂ => remark11_main h8 h6 h7 d hd hγ0 hγ1 a₁ b₁ a₂ b₂

end P3CD
