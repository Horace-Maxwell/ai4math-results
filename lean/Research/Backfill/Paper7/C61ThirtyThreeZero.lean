import Research.Backfill.Paper7.C61ThreeRootTwoZeros

/-! NEW SOURCE ONLY. Total thirty-three and any actual zero coordinate are
incompatible with identity monodromy at three. No square sum, coordinate
cap, support pattern, or candidate-list hypothesis is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Classical

theorem odd_complement_product_not_minus_81 (t x z : ℤ)
    (h : (9-t)*t*x*z = -81) : False := by
  have ht : t%2 = 0 ∨ t%2 = 1 := by omega
  have hm := congrArg (fun w : ℤ => w%2) h
  rcases ht with ht | ht <;>
    norm_num [Int.mul_emod,Int.sub_emod,ht] at hm
#print axioms Paper7C61Four.odd_complement_product_not_minus_81

theorem thirty_three_scalar_impossible (b x t z f : ℤ)
    (hs : b+(9-x)+(9-t)+(9-z)+f = 33)
    (hleft : 9*(9-b)+t*z = 18)
    (hright : x*t+(9-f)*9 = 18)
    (htriple : 81 = 9*(x+z)-x*t*z) : False := by
  have hfactor : (9-t)*(9-(x+z)) = 9 := by
    nlinarith only [hs,hleft,hright]
  have hxyz : t*x*z = 9*(x+z)-81 := by nlinarith only [htriple]
  have hprod : (9-t)*(t*x*z) = -81 := by
    rw [hxyz]
    nlinarith only [hfactor]
  apply odd_complement_product_not_minus_81 t x z
  simpa only [mul_assoc] using hprod
#print axioms Paper7C61Four.thirty_three_scalar_impossible

theorem thirty_three_zero_head_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 33) (hz0 : p 0 = 0) (h : TripleNumerators p) : False := by
  have hU0 : unitThree p 0 = 9 := by simp [unitThree,hz0]
  have hleft := (h 0).1
  change unitThree p 0*unitThree p 1+unitThree p 3*unitThree p 4 = 18 at hleft
  rw [hU0] at hleft
  have hright := (h 2).1
  change unitThree p 2*unitThree p 3+unitThree p 5*unitThree p 0 = 18 at hright
  rw [hU0] at hright
  have htriple := (h 2).2
  change 9*unitThree p 0 = 9*(unitThree p 2+unitThree p 4)-
    unitThree p 2*unitThree p 3*unitThree p 4 at htriple
  rw [hU0] at htriple
  norm_num only at htriple
  have hsN : p 1+p 2+p 3+p 4+p 5 = 33 := by
    simpa [totalP,Fin.sum_univ_succ,hz0,Nat.add_assoc] using hP
  have hsZ : (p 1 : ℤ)+p 2+p 3+p 4+p 5 = 33 := by exact_mod_cast hsN
  apply thirty_three_scalar_impossible (p 1) (unitThree p 2) (unitThree p 3)
    (unitThree p 4) (p 5)
  · dsimp only [unitThree]
    omega
  · simpa only [unitThree] using hleft
  · simpa only [unitThree] using hright
  · exact htriple
#print axioms Paper7C61Four.thirty_three_zero_head_impossible

theorem sum_thirty_three_zero_monodromy_three_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 33) (hz : ∃ j : Fin 6, p j = 0)
    (hm : Mono 6 p (fun _ => 0) 3 = 1) : False := by
  obtain ⟨j,hj⟩ := hz
  apply thirty_three_zero_head_impossible (turnThree p j)
  · rw [totalP_turn_three]
    exact hP
  · simpa only [turnThree,zero_add] using hj
  · exact triple_numerators_turn p j (mono_three_triple_numerators p hm)
#print axioms Paper7C61Four.sum_thirty_three_zero_monodromy_three_impossible

end Paper7C61Four
