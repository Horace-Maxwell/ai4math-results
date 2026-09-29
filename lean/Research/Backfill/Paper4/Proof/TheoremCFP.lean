import Research.Backfill.Paper4.Proof.FourPointConsequences
import Research.Backfill.Paper4.Proof.Readings

/-! The complete frozen TheoremC_FP, including its maximum identity and
the strong extension disjunction. Acceptance is recorded separately.
No cardinality hypothesis is added to the theorem: failure of Q3 supplies
three distinct vertices before the strong-reading equivalence is applied. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4

namespace TheoremCFP

lemma max_three_attained (A B C M : ℕ) (h : max (max A B) C = M) :
    A = M ∨ B = M ∨ C = M := by
  rcases le_total A B with hab | hba
  · rw [max_eq_right hab] at h
    rcases le_total B C with hbc | hcb
    · exact Or.inr (Or.inr ((max_eq_right hbc).symm.trans h))
    · exact Or.inr (Or.inl ((max_eq_left hcb).symm.trans h))
  · rw [max_eq_left hba] at h
    rcases le_total A C with hac | hca
    · exact Or.inr (Or.inr ((max_eq_right hac).symm.trans h))
    · exact Or.inl ((max_eq_left hca).symm.trans h)

lemma equation (V : Type) [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected) (hfp : Challenge.FourPointBM G) :
    Challenge.TheoremCEquation V G := by
  intro a b c htri hab hac hbc x y hxy
  have lab : G.dist a b < G.diam :=
    lt_of_le_of_ne (MetricBounds.dist_le_diameter G hc a b) hab
  have lac : G.dist a c < G.diam :=
    lt_of_le_of_ne (MetricBounds.dist_le_diameter G hc a c) hac
  have lbc : G.dist b c < G.diam :=
    lt_of_le_of_ne (MetricBounds.dist_le_diameter G hc b c) hbc
  have hlo := check_Proposition3 V G hc hfp x y hxy a b c lab lac lbc
  have ht : Challenge.triDist G a b c = Challenge.triameter G := htri
  rw [ht] at hlo
  have hhi :
      max (max (Challenge.triDist G a x y) (Challenge.triDist G b x y))
        (Challenge.triDist G c x y) ≤ Challenge.triameter G :=
    max_le (max_le (MetricBounds.triDist_le_triameter G a x y)
      (MetricBounds.triDist_le_triameter G b x y))
      (MetricBounds.triDist_le_triameter G c x y)
  exact le_antisymm hhi hlo

lemma extension_from_counterexample (V : Type) [Fintype V] (G : SimpleGraph V)
    (heq : Challenge.TheoremCEquation V G) {a b c : V}
    (htri : Challenge.IsTriametral G a b c)
    (hab : ¬ Challenge.IsDiametral G a b) (hac : ¬ Challenge.IsDiametral G a c)
    (hbc : ¬ Challenge.IsDiametral G b c) : Challenge.Question4 G := by
  intro x y hxy
  have hmax := heq a b c htri hab hac hbc x y hxy
  rcases max_three_attained _ _ _ _ hmax with ha | hb | hc
  · refine ⟨a, ?_⟩
    change Challenge.triDist G x y a = Challenge.triameter G
    rw [← Readings.triDist_rotate G a x y]
    exact ha
  · refine ⟨b, ?_⟩
    change Challenge.triDist G x y b = Challenge.triameter G
    rw [← Readings.triDist_rotate G b x y]
    exact hb
  · refine ⟨c, ?_⟩
    change Challenge.triDist G x y c = Challenge.triameter G
    rw [← Readings.triDist_rotate G c x y]
    exact hc

end TheoremCFP

/-- The exact frozen conjunction, without an extra nonempty or cardinality premise. -/
theorem check_TheoremC_FP : Challenge.TheoremC_FP := by
  classical
  intro V _ G hc hfp
  have heq := TheoremCFP.equation V G hc hfp
  by_cases h3 : Challenge.Question3 G
  · exact ⟨heq, Or.inl h3, Or.inl h3,
      Or.inl (check_Sec2_Q3_imp_Q3' V G hc h3)⟩
  · unfold Challenge.Question3 at h3
    push Not at h3
    obtain ⟨a, b, c, htri, hab, hac, hbc⟩ := h3
    have h4 := TheoremCFP.extension_from_counterexample V G heq htri hab hac hbc
    obtain ⟨hab', hac', hbc'⟩ :=
      Readings.triametral_distinct_of_no_diametral G hc htri hab hac hbc
    have hcard : 3 ≤ Fintype.card V := by
      have hh : 2 < Fintype.card V :=
        (Fintype.two_lt_card_iff (α := V)).mpr ⟨a, b, c, hab', hac', hbc'⟩
      omega
    have h4strong : Challenge.Question4Strong G :=
      (check_Sec2_readings_Q4 V G hc hcard).1.mp h4
    exact ⟨heq, Or.inr h4, Or.inr h4strong, Or.inr h4⟩

#print axioms check_TheoremC_FP
end CodexPaper4
