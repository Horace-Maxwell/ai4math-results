import Research.Backfill.Paper7.C61ThreeMonodromy

/-! NEW SOURCE ONLY. Repeated ordinary roots yield actual monodromy
identities; their scalar consequences retain all original coordinates. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge
open Paper7C61Profile Paper7C61Three
open scoped Matrix Classical

theorem actual_two_monodromy (p q : Fin 6 → ℕ)
    (h : (actual p q 0).val = 2) : Mono 6 p q 2 = 1 := by
  have hm : mult (SG 6 p q) 2 = 2 := by
    have hi := actual_eq_mult p q (0 : Fin 5)
    norm_num [value] at hi
    omega
  exact (Paper7Lemma22Periodic.lemma22_ordinary_clause 6 p q (by decide)
    2 (by norm_num) (by norm_num) (by norm_num)).2.2.1.mp hm
#print axioms Paper7C61Four.actual_two_monodromy

theorem actual_three_monodromy (p q : Fin 6 → ℕ)
    (h : (actual p q 1).val = 2) : Mono 6 p q 3 = 1 := by
  have hm : mult (SG 6 p q) 3 = 2 := by
    have hi := actual_eq_mult p q (1 : Fin 5)
    norm_num [value] at hi
    omega
  exact (Paper7Lemma22Periodic.lemma22_ordinary_clause 6 p q (by decide)
    3 (by norm_num) (by norm_num) (by norm_num)).2.2.1.mp hm
#print axioms Paper7C61Four.actual_three_monodromy

theorem ordinary_monodromy_pairs (p q : Fin 6 → ℕ) (m : ℝ)
    (hm : Mono 6 p q m = 1) :
    (m-fk 6 p q m 0)*(m-fk 6 p q m 1) +
      (m-fk 6 p q m 3)*(m-fk 6 p q m 4) = 2 ∧
    (m-fk 6 p q m 1)*(m-fk 6 p q m 2) +
      (m-fk 6 p q m 4)*(m-fk 6 p q m 5) = 2 ∧
    (m-fk 6 p q m 2)*(m-fk 6 p q m 3) +
      (m-fk 6 p q m 5)*(m-fk 6 p q m 0) = 2 := by
  have h : realSixProduct (m-fk 6 p q m 0) (m-fk 6 p q m 1)
      (m-fk 6 p q m 2) (m-fk 6 p q m 3)
      (m-fk 6 p q m 4) (m-fk 6 p q m 5) = 1 := by
    calc
      _ = Mono 6 p q m := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [Mono,Tk,realSixProduct,realTransfer,List.finRange_succ] <;> ring
      _ = 1 := hm
  have ht := real_six_triple_data _ _ _ _ _ _ h
  have hr := real_six_rotate _ _ _ _ _ _ (real_six_rotate _ _ _ _ _ _ h)
  exact ⟨ht.1,ht.2.1,(real_six_triple_data _ _ _ _ _ _ hr).1⟩
#print axioms Paper7C61Four.ordinary_monodromy_pairs

theorem two_three_scalar_elimination (a b d e : ℝ)
    (h2 : (2-a/2)*(2-b/2)+(2-d/2)*(2-e/2) = 2)
    (h3 : (3-a/3)*(3-b/3)+(3-d/3)*(3-e/3) = 2) :
    a+b+d+e = 24 ∧ a*b+d*e = 72 := by
  constructor <;> nlinarith only [h2,h3]
#print axioms Paper7C61Four.two_three_scalar_elimination

theorem double_two_three_qzero_coordinates (p q : Fin 6 → ℕ)
    (hq : q = (fun _ => 0))
    (h2 : (actual p q 0).val = 2) (h3 : (actual p q 1).val = 2) :
    ∀ k : Fin 6, p k+p (k+3) = 12 ∧
      p k*p (k+1)+p (k+3)*p (k+4) = 72 := by
  have hp2 := ordinary_monodromy_pairs p q 2 (actual_two_monodromy p q h2)
  have hp3 := ordinary_monodromy_pairs p q 3 (actual_three_monodromy p q h3)
  norm_num [fk,hq] at hp2 hp3
  have hA := two_three_scalar_elimination _ _ _ _ hp2.1 hp3.1
  have hB := two_three_scalar_elimination _ _ _ _ hp2.2.1 hp3.2.1
  have hC := two_three_scalar_elimination _ _ _ _ hp2.2.2 hp3.2.2
  have hA' : p 0+p 1+p 3+p 4 = 24 ∧ p 0*p 1+p 3*p 4 = 72 := by
    exact_mod_cast hA
  have hB' : p 1+p 2+p 4+p 5 = 24 ∧ p 1*p 2+p 4*p 5 = 72 := by
    exact_mod_cast hB
  have hC' : p 2+p 3+p 5+p 0 = 24 ∧ p 2*p 3+p 5*p 0 = 72 := by
    exact_mod_cast hC
  have h03 : p 0+p 3 = 12 := by omega
  have h14 : p 1+p 4 = 12 := by omega
  have h25 : p 2+p 5 = 12 := by omega
  intro k
  fin_cases k
  · change p 0+p 3 = 12 ∧ p 0*p 1+p 3*p 4 = 72
    exact ⟨h03,hA'.2⟩
  · change p 1+p 4 = 12 ∧ p 1*p 2+p 4*p 5 = 72
    exact ⟨h14,hB'.2⟩
  · change p 2+p 5 = 12 ∧ p 2*p 3+p 5*p 0 = 72
    exact ⟨h25,hC'.2⟩
  · change p 3+p 0 = 12 ∧ p 3*p 4+p 0*p 1 = 72
    constructor <;> omega
  · change p 4+p 1 = 12 ∧ p 4*p 5+p 1*p 2 = 72
    constructor <;> omega
  · change p 5+p 2 = 12 ∧ p 5*p 0+p 2*p 3 = 72
    constructor <;> omega
#print axioms Paper7C61Four.double_two_three_qzero_coordinates

end Paper7C61Four
