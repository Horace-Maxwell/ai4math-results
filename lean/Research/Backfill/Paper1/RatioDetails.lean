import Research.Backfill.Paper1.ParameterComparisons

/-! Exact monotonicity observation retained at note.tex T1061--1062. -/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
namespace PaperDetails

lemma ratio_monotonicity :
    StrictMonoOn (fun P : ℝ => (P - 1) ^ 2 / (P ^ 2 + 1)) (Set.Ici 1) ∧
    (∀ P : ℝ, (P - 1) ^ 2 / (P ^ 2 + 1) = 1 - 2 * P / (P ^ 2 + 1)) ∧
    ((2 : ℝ) - 1) ^ 2 / (2 ^ 2 + 1) = 1 / 5 ∧
    ((4 : ℝ) - 1) ^ 2 / (4 ^ 2 + 1) = 9 / 17 := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · intro x hx y hy hxy
    have hx1 : 1 ≤ x := hx
    have hy1 : 1 ≤ y := hy
    have hxyprod : 1 < x * y := by
      nlinarith [mul_nonneg (show 0 ≤ x - 1 by linarith) (show 0 ≤ y by linarith)]
    have hp : 0 < 2 * (y - x) * (x * y - 1) := by positivity
    apply (div_lt_div_iff₀ (by positivity : 0 < x ^ 2 + 1)
      (by positivity : 0 < y ^ 2 + 1)).mpr
    nlinarith [show (y - 1) ^ 2 * (x ^ 2 + 1) - (x - 1) ^ 2 * (y ^ 2 + 1) =
      2 * (y - x) * (x * y - 1) by ring]
  · intro P
    field_simp
    ring

end PaperDetails
#print axioms PaperDetails.ratio_monotonicity
end CodexPaper1
