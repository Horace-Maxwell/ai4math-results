import Research.Backfill.Paper7.C61ThreeMonodromy

/-! NEW SOURCE ONLY. Exact opposite half-integral transfer identities.
The six integer coefficients retain their cyclic order. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightHalf
open BackfillPaper7.Challenge Paper7C61Three
open scoped Matrix

def halfOppositeProduct (h k a b c d e f : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  realTransfer f*realTransfer e*realTransfer d*realTransfer ((k : ℝ)/2)*
    realTransfer c*realTransfer b*realTransfer a*realTransfer ((h : ℝ)/2)
#print axioms Paper7EightHalf.halfOppositeProduct

theorem half_opposite_identity_data (h k a b c d e f : ℤ)
    (hid : halfOppositeProduct h k a b c d e f = 1) :
    (a*b*c-a-c)+(d*e*f-d-f) = 0 ∧
      h*(a*b*c-a-c) = 2*(b*c-d*e) ∧
      k*(a*b*c-a-c) = 2*(a*b-e*f) := by
  let U : Matrix (Fin 2) (Fin 2) ℝ :=
    !![-(e : ℝ),(e : ℝ)*f-1;1-(d : ℝ)*e,(d : ℝ)*e*f-d-f]
  have hinv : U*(realTransfer f*realTransfer e*realTransfer d) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U,realTransfer,Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  have hprod : (realTransfer f*realTransfer e*realTransfer d)*
      (realTransfer ((k : ℝ)/2)*(realTransfer c*realTransfer b*realTransfer a)*
        realTransfer ((h : ℝ)/2)) = 1 := by
    simpa only [halfOppositeProduct,mul_assoc] using hid
  have he : realTransfer ((k : ℝ)/2)*(realTransfer c*realTransfer b*realTransfer a)*
      realTransfer ((h : ℝ)/2) = U := by
    calc
      _ = 1*(realTransfer ((k : ℝ)/2)*(realTransfer c*realTransfer b*realTransfer a)*
          realTransfer ((h : ℝ)/2)) := by simp
      _ = (U*(realTransfer f*realTransfer e*realTransfer d))*
          (realTransfer ((k : ℝ)/2)*(realTransfer c*realTransfer b*realTransfer a)*
            realTransfer ((h : ℝ)/2)) := by rw [hinv]
      _ = U*((realTransfer f*realTransfer e*realTransfer d)*
          (realTransfer ((k : ℝ)/2)*(realTransfer c*realTransfer b*realTransfer a)*
            realTransfer ((h : ℝ)/2))) := by rw [mul_assoc]
      _ = U := by rw [hprod,mul_one]
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) he
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) he
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) he
  norm_num [U,realTransfer,Matrix.mul_apply,Fin.sum_univ_two] at h11 h10 h01
  have hS : ((a : ℝ)*b*c-a-c)+((d : ℝ)*e*f-d-f) = 0 := by
    nlinarith only [h11]
  have hH : (h : ℝ)*((a : ℝ)*b*c-a-c) = 2*((b : ℝ)*c-d*e) := by
    nlinarith only [h10]
  have hK : (k : ℝ)*((a : ℝ)*b*c-a-c) = 2*((a : ℝ)*b-e*f) := by
    nlinarith only [h01]
  exact ⟨by exact_mod_cast hS,by exact_mod_cast hH,by exact_mod_cast hK⟩
#print axioms Paper7EightHalf.half_opposite_identity_data

theorem mono_eight_half_opposite (p : Fin 8 → ℕ) (h k a b c d e f : ℤ)
    (h0 : (4 : ℤ)-p 0 = h) (h4 : (4 : ℤ)-p 4 = k)
    (h1 : (4 : ℤ)-p 1 = 2*a) (h2 : (4 : ℤ)-p 2 = 2*b)
    (h3 : (4 : ℤ)-p 3 = 2*c) (h5 : (4 : ℤ)-p 5 = 2*d)
    (h6 : (4 : ℤ)-p 6 = 2*e) (h7 : (4 : ℤ)-p 7 = 2*f) :
    Mono 8 p (fun _ => 0) 2 = halfOppositeProduct h k a b c d e f := by
  have h0R : 2-(p 0 : ℝ)/2 = (h : ℝ)/2 := by
    have hh : (4 : ℝ)-p 0 = h := by exact_mod_cast h0
    linarith only [hh]
  have h4R : 2-(p 4 : ℝ)/2 = (k : ℝ)/2 := by
    have hh : (4 : ℝ)-p 4 = k := by exact_mod_cast h4
    linarith only [hh]
  have h1R : 2-(p 1 : ℝ)/2 = a := by
    have hh : (4 : ℝ)-p 1 = 2*a := by exact_mod_cast h1
    linarith only [hh]
  have h2R : 2-(p 2 : ℝ)/2 = b := by
    have hh : (4 : ℝ)-p 2 = 2*b := by exact_mod_cast h2
    linarith only [hh]
  have h3R : 2-(p 3 : ℝ)/2 = c := by
    have hh : (4 : ℝ)-p 3 = 2*c := by exact_mod_cast h3
    linarith only [hh]
  have h5R : 2-(p 5 : ℝ)/2 = d := by
    have hh : (4 : ℝ)-p 5 = 2*d := by exact_mod_cast h5
    linarith only [hh]
  have h6R : 2-(p 6 : ℝ)/2 = e := by
    have hh : (4 : ℝ)-p 6 = 2*e := by exact_mod_cast h6
    linarith only [hh]
  have h7R : 2-(p 7 : ℝ)/2 = f := by
    have hh : (4 : ℝ)-p 7 = 2*f := by exact_mod_cast h7
    linarith only [hh]
  have ht : Mono 8 p (fun _ => 0) 2 =
      realTransfer (2-(p 7 : ℝ)/2)*realTransfer (2-(p 6 : ℝ)/2)*
      realTransfer (2-(p 5 : ℝ)/2)*realTransfer (2-(p 4 : ℝ)/2)*
      realTransfer (2-(p 3 : ℝ)/2)*realTransfer (2-(p 2 : ℝ)/2)*
      realTransfer (2-(p 1 : ℝ)/2)*realTransfer (2-(p 0 : ℝ)/2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Mono,Tk,fk,List.finRange_succ,realTransfer,Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  rw [ht,h0R,h1R,h2R,h3R,h4R,h5R,h6R,h7R]
  rfl
#print axioms Paper7EightHalf.mono_eight_half_opposite

end Paper7EightHalf
