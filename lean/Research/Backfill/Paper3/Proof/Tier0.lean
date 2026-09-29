import Research.Backfill.Paper3.Proof.Poly

/-!
# Paper 3 back-fill: small Tier 0 and Tier 2 statements

`KddIndependentSets`, `IntegerForm`, `QuestionTrueHalf`, `LowGammaExamples`, `SethDensity`.
The counts use the decompositions of `Research.Backfill.Paper3.Proof.Basic`: a vertex set of `K_{d,d}` is a pair `(S, T)` of
subsets of the two sides and spans `|S| |T|` edges; a vertex set of `m K_{d,d}` is a family of
such pairs.
-/

set_option autoImplicit false

namespace P3Basic

open Finset SimpleGraph BackfillPaper3.Challenge

/-- `K_{d,d}` has `2^{d+1} - 1` independent sets. -/
theorem check_KddIndependentSets : KddIndependentSets := by
  intro d
  have h1 : iCount (Kdd d) 0 = ∑ S : Finset (Fin d), ∑ T : Finset (Fin d),
      (if #S * #T = 0 then 1 else 0) := by
    rw [iCount, Finset.card_filter, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (finsetSumEquiv (Fin d) (Fin d)) _ _ (fun A => ?_)
    have := edgesIn_Kdd d A.toLeft A.toRight
    rw [Finset.toLeft_disjSum_toRight] at this
    simp [finsetSumEquiv, this]
  have h2 : ∀ S : Finset (Fin d), ∑ T : Finset (Fin d), (if #S * #T = 0 then 1 else 0) =
      if S = ∅ then 2 ^ d else 1 := by
    intro S
    by_cases hS : S = ∅
    · simp [hS, Finset.card_univ, Fintype.card_finset]
    · have hS' : #S ≠ 0 := by simpa [Finset.card_eq_zero] using hS
      simp [hS, hS', Finset.card_eq_zero]
  rw [h1, Finset.sum_congr rfl fun S _ => h2 S, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const, Finset.filter_eq', Finset.filter_ne']
  simp only [Finset.mem_univ, ite_true, Finset.card_singleton, smul_eq_mul, one_mul, mul_one,
    Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  rw [pow_succ]
  omega

/-- `|V(m K_{d,d})| = 2dm`. -/
theorem card_KddUnion (m d : ℕ) : Fintype.card (Fin m × (Fin d ⊕ Fin d)) = 2 * d * m := by
  simp [Fintype.card_prod, Fintype.card_sum]
  ring

/-- A set of vertices of `m K_{d,d}` spans at most `m d²` edges. -/
theorem edgesIn_KddUnion_le (m d : ℕ) (A : Finset (Fin m × (Fin d ⊕ Fin d))) :
    edgesIn (KddUnion m d) A ≤ m * d ^ 2 := by
  have hA : A = (fibresEquiv m (Fin d ⊕ Fin d)).symm (fibresEquiv m (Fin d ⊕ Fin d) A) :=
    ((fibresEquiv m _).symm_apply_apply A).symm
  rw [hA]
  show edgesIn (copies m (Kdd d)) _ ≤ _
  rw [edgesIn_copies]
  calc ∑ i, edgesIn (Kdd d) (fibresEquiv m (Fin d ⊕ Fin d) A i)
      ≤ ∑ _i : Fin m, d ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        set B := fibresEquiv m (Fin d ⊕ Fin d) A i
        have h := edgesIn_Kdd d B.toLeft B.toRight
        rw [Finset.toLeft_disjSum_toRight] at h
        rw [h, sq]
        exact Nat.mul_le_mul (card_le_univ _ |>.trans (by simp))
          (card_le_univ _ |>.trans (by simp))
    _ = m * d ^ 2 := by simp

/-- §3: Question 1.3 for all `γ ≥ 0` is equivalent to the integer inequalities. -/
theorem check_IntegerForm : IntegerForm := by
  intro n d ⟨hd, hn, hdiv⟩
  have hcard : Fintype.card (Fin (n / (2 * d)) × (Fin d ⊕ Fin d)) = n := by
    rw [card_KddUnion]
    exact Nat.mul_div_cancel' hdiv
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro hQ V _ _ G _ hV hG t
    have hγ : (0 : ℝ) ≤ (t : ℝ) / (d * n) := by positivity
    have h := hQ ((t : ℝ) / (d * n)) hγ V G hV hG
    have ht : (t : ℝ) / (d * n) * d * n = t := by field_simp
    rw [iGamma_eq_iCount G d t (by rw [hV]; exact ht),
      iGamma_eq_iCount _ d t (by rw [hcard]; exact ht)] at h
    exact h
  · intro hI γ hγ V _ _ G _ hV hG
    rw [iGamma_eq_iCount_floor G d hγ, iGamma_eq_iCount_floor _ d hγ, hV, hcard]
    exact hI V G hV hG _

/-- §1: for `γ ≥ 1/2` the question holds trivially. -/
theorem check_QuestionTrueHalf : QuestionTrueHalf := by
  intro n d ⟨hd, hn, hdiv⟩ γ hγ V _ _ G _ hV hG
  have hcard : Fintype.card (Fin (n / (2 * d)) × (Fin d ⊕ Fin d)) = n := by
    rw [card_KddUnion]
    exact Nat.mul_div_cancel' hdiv
  -- every set of `m K_{d,d}` counts, so its `i_γ` is `2^n`
  have hK : iGamma (KddUnion (n / (2 * d)) d) d γ = 2 ^ n := by
    unfold iGamma
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_finset, hcard]
    intro A _
    have h1 := edgesIn_KddUnion_le (n / (2 * d)) d A
    have h2 : ((n / (2 * d) * d ^ 2 : ℕ) : ℝ) ≤ γ * d * (Fintype.card (Fin (n / (2 * d)) ×
        (Fin d ⊕ Fin d)) : ℝ) := by
      rw [hcard]
      obtain ⟨k, rfl⟩ := hdiv
      have hd0 : 0 < 2 * d := by omega
      rw [Nat.mul_div_cancel_left k hd0]
      push_cast
      nlinarith [sq_nonneg (d : ℝ), (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2 * k)]
    exact le_trans (by exact_mod_cast h1) h2
  have hG' : iGamma G d γ ≤ 2 ^ n := by
    unfold iGamma
    calc _ ≤ #(univ : Finset (Finset V)) := Finset.card_filter_le _ _
      _ = 2 ^ n := by rw [Finset.card_univ, Fintype.card_finset, hV]
  omega

/-- §1 ("Scope"): every counterexample of the paper with `γ ≤ 1/8` has `γ d < 1`. -/
theorem check_LowGammaExamples : LowGammaExamples := by
  constructor
  · intro d hd γ hγ
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hpos : (0 : ℝ) < d := by linarith
    have h1 : γ * d < 1 / (d : ℝ) ^ 2 * d := mul_lt_mul_of_pos_right hγ hpos
    have h2 : 1 / (d : ℝ) ^ 2 * d ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      nlinarith
    linarith
  · intro d hd γ hγ
    have hd' : (d : ℝ) ≤ 5 := by exact_mod_cast hd
    have hd0 : (0 : ℝ) ≤ d := by positivity
    nlinarith

/-- §1: Seth's density condition `e_G(J) ≤ (d/(kn)) C(|J|, 2)` implies `e_G(J) ≤ dn/(2k)`. -/
theorem check_SethDensity : SethDensity := by
  intro V _ _ G _ d k hk hn J hJ
  set n := Fintype.card V
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hJn : ((#J : ℕ) : ℝ) ≤ n := by exact_mod_cast Finset.card_le_univ J
  have hc : (((#J).choose 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    have h := Nat.choose_le_pow_div (α := ℝ) 2 (#J)
    have h2 : ((#J : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have : (0 : ℝ) ≤ (#J : ℕ) := by positivity
      nlinarith
    calc (((#J).choose 2 : ℕ) : ℝ) ≤ ((#J : ℕ) : ℝ) ^ 2 / (2 : ℕ).factorial := h
      _ ≤ (n : ℝ) ^ 2 / 2 := by
        rw [Nat.factorial_two]; push_cast
        exact div_le_div_of_nonneg_right h2 (by norm_num)
  have hcoef : (0 : ℝ) ≤ (d : ℝ) / (k * n) := by positivity
  calc (edgesIn G J : ℝ) ≤ (d : ℝ) / (k * n) * (((#J).choose 2 : ℕ) : ℝ) := hJ
    _ ≤ (d : ℝ) / (k * n) * ((n : ℝ) ^ 2 / 2) := mul_le_mul_of_nonneg_left hc hcoef
    _ = (d : ℝ) * n / (2 * k) := by field_simp

#print axioms check_KddIndependentSets
#print axioms check_IntegerForm
#print axioms check_QuestionTrueHalf
#print axioms check_LowGammaExamples
#print axioms check_SethDensity

end P3Basic
