import Research.Backfill.Paper7.C61ThreeMonodromy

/-! NEW SOURCE ONLY. Exact four-step transfer identities and their original
parameter consequences. No finite parameter coverage is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Three
open scoped BigOperators Matrix Classical

def realFourProduct (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  realTransfer d*realTransfer c*realTransfer b*realTransfer a
#print axioms Paper7B4Analytic.realFourProduct

theorem real_four_trace (a b c d : ℝ) :
    (realFourProduct a b c d).trace = a*b*c*d-(a+c)*(b+d)+2 := by
  norm_num [realFourProduct,realTransfer,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two]
  ring
#print axioms Paper7B4Analytic.real_four_trace

theorem real_four_identity_data (a b c d : ℝ) (h : realFourProduct a b c d=1) :
    a+c=0 ∧ b+d=0 ∧ a*b=0 := by
  let U : Matrix (Fin 2) (Fin 2) ℝ := !![-1,d;-c,c*d-1]
  have hinv : U*(realTransfer d*realTransfer c)=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U,realTransfer,Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  have hp : (realTransfer d*realTransfer c)*(realTransfer b*realTransfer a)=1 := by
    simpa only [realFourProduct,mul_assoc] using h
  have he : realTransfer b*realTransfer a=U := by
    calc
      _ = 1*(realTransfer b*realTransfer a) := by simp
      _ = (U*(realTransfer d*realTransfer c))*(realTransfer b*realTransfer a) := by rw [hinv]
      _ = U*((realTransfer d*realTransfer c)*(realTransfer b*realTransfer a)) := by rw [mul_assoc]
      _ = U := by rw [hp,mul_one]
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) he
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) he
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) he
  norm_num [U,realTransfer,Matrix.mul_apply,Fin.sum_univ_two] at h00 h01 h10
  refine ⟨by linarith, by linarith, ?_⟩
  rcases h00 with hb | ha
  · simp [hb]
  · simp [ha]
#print axioms Paper7B4Analytic.real_four_identity_data

theorem mono_four_product (p q : Fin 4 → ℕ) (m : ℝ) :
    Mono 4 p q m = realFourProduct (m-fk 4 p q m 0) (m-fk 4 p q m 1)
      (m-fk 4 p q m 2) (m-fk 4 p q m 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Mono,Tk,realFourProduct,realTransfer,List.finRange_succ] <;> ring
#print axioms Paper7B4Analytic.mono_four_product

theorem ordinary_trace_iff_spec (p q : Fin 4 → ℕ) (m : ℝ)
    (hmn : m≠-1) (hm0 : m≠0) (hm1 : m≠1) :
    (Mono 4 p q m).trace=2 ↔ m∈spec (SG 4 p q) := by
  have hc := Paper7Lemma22Periodic.lemma22_ordinary_clause 4 p q (by decide) m hmn hm0 hm1
  constructor
  · intro ht
    have hpos : 0 < mult (SG 4 p q) m := by
      by_cases he : Mono 4 p q m=1
      · have hh := hc.2.2.1.mpr he
        omega
      · have hh := hc.2.2.2.mpr ⟨he,ht⟩
        omega
    exact Multiset.count_pos.mp hpos
  · intro hs
    have hpos : 0 < mult (SG 4 p q) m := Multiset.count_pos.mpr hs
    have hcases : mult (SG 4 p q) m=1 ∨ mult (SG 4 p q) m=2 := by
      have hb := hc.2.1
      omega
    rcases hcases with h1 | h2
    · exact (hc.2.2.2.mp h1).2
    · rw [hc.2.2.1.mp h2]
      norm_num [Matrix.trace,Fin.sum_univ_two]
#print axioms Paper7B4Analytic.ordinary_trace_iff_spec

theorem identity_four_weight_equation (p q : Fin 4 → ℕ) (m : ℝ)
    (hm : 2 ≤ m) (h : Mono 4 p q m=1) :
    (m^2-1)*(totalP 4 p : ℝ)+m^2*(totalQ 4 q : ℝ)=4*m^2*(m^2-1) := by
  have hm0 : m≠0 := by linarith
  have hs0 : m^2-1≠0 := by nlinarith
  rw [mono_four_product] at h
  obtain ⟨h02,h13,_⟩ := real_four_identity_data _ _ _ _ h
  have hsum : (m-fk 4 p q m 0)+(m-fk 4 p q m 1)+
      (m-fk 4 p q m 2)+(m-fk 4 p q m 3)=0 := by linarith
  have he (i : Fin 4) : m*(m^2-1)*(m-fk 4 p q m i)=
      m^2*(m^2-1)-(m^2-1)*(p i : ℝ)-m^2*(q i : ℝ) := by
    unfold fk
    field_simp [hm0,hs0]; ring
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  have hz := congrArg (fun x : ℝ => m*(m^2-1)*x) hsum
  norm_num [totalP,totalQ,Fin.sum_univ_four]
  nlinarith only [h0,h1,h2,h3,hz]
#print axioms Paper7B4Analytic.identity_four_weight_equation

theorem identity_four_weight_lower (p q : Fin 4 → ℕ) (m : ℝ)
    (hm : 2 ≤ m) (h : Mono 4 p q m=1) :
    4*m^2 ≤ (totalP 4 p : ℝ)+2*(totalQ 4 q : ℝ) := by
  have he := identity_four_weight_equation p q m hm h
  have hs : 0 < m^2-1 := by nlinarith
  have hq := mul_nonneg (show 0 ≤ m^2-2 by nlinarith) (Nat.cast_nonneg (totalQ 4 q))
  have hb : (4*m^2)*(m^2-1) ≤ 
      ((totalP 4 p : ℝ)+2*(totalQ 4 q : ℝ))*(m^2-1) := by
    nlinarith only [he,hq]
  exact (mul_le_mul_iff_left₀ hs).mp hb
#print axioms Paper7B4Analytic.identity_four_weight_lower

theorem repeated_ordinary_below_four (p q : Fin 4 → ℕ)
    (hn : nOf 4 p q ≤ 49) (m : ℝ) (hm : 4 ≤ m) : mult (SG 4 p q) m≠2 := by
  intro hmult
  have hid := (Paper7Lemma22Periodic.lemma22_ordinary_clause 4 p q (by decide) m
    (by linarith) (by linarith) (by linarith)).2.2.1.mp hmult
  have hw := identity_four_weight_lower p q m (by linarith) hid
  have hnN : totalP 4 p+2*totalQ 4 q ≤ 45 := by
    change 4+totalP 4 p+2*totalQ 4 q ≤ 49 at hn
    omega
  have hnR : (totalP 4 p : ℝ)+2*(totalQ 4 q : ℝ) ≤ 45 := by exact_mod_cast hnN
  nlinarith
#print axioms Paper7B4Analytic.repeated_ordinary_below_four

end Paper7B4Analytic
