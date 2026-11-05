import Research.Backfill.Paper7.EightHalfCoefficientExclusion

/-! NEW SOURCE ONLY. The four coefficient eliminations transported back to
the actual ordinary monodromy. Coverage is supplied by the parent reduction. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightHalf
open BackfillPaper7.Challenge

theorem mono_eight_opposite_four_coefficients_ne_one (p : Fin 8 → ℕ)
    (a b c d e f : ℤ)
    (h1 : (4 : ℤ)-p 1 = 2*a) (h2 : (4 : ℤ)-p 2 = 2*b)
    (h3 : (4 : ℤ)-p 3 = 2*c) (h5 : (4 : ℤ)-p 5 = 2*d)
    (h6 : (4 : ℤ)-p 6 = 2*e) (h7 : (4 : ℤ)-p 7 = 2*f)
    (hcases : (p 0+p 4 = 14 ∧ [a,b,c,d,e,f].Perm [-2,1,1,2,2,2]) ∨
      [a,b,c,d,e,f].Perm [-1,-1,2,2,2,2] ∨
      [a,b,c,d,e,f].Perm [-4,0,2,2,2,2] ∨
      [a,b,c,d,e,f].Perm [-4,2,2,2,2,2]) :
    Mono 8 p (fun _ => 0) 2 ≠ 1 := by
  rw [mono_eight_half_opposite p ((4 : ℤ)-p 0) ((4 : ℤ)-p 4)
    a b c d e f rfl rfl h1 h2 h3 h5 h6 h7]
  rcases hcases with ⟨hodd,hp⟩ | hp | hp | hp
  · exact half_opposite_case_a _ _ a b c d e f (by omega) hp
  · exact half_opposite_case_b _ _ a b c d e f hp
  · exact half_opposite_case_c _ _ a b c d e f hp
  · exact half_opposite_case_d _ _ a b c d e f hp
#print axioms Paper7EightHalf.mono_eight_opposite_four_coefficients_ne_one

end Paper7EightHalf
