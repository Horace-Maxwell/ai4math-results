import Research.Backfill.Paper7.C61DoubleRootMonodromy
import Research.Backfill.Paper7.C61FinSixIndexSimp
import Research.Backfill.Paper7.C61ThreeQpositiveAlgebra

/-! NEW SOURCE ONLY. Integer divisibility from the actual monodromy identity
and three adjacent zero-q coordinates; no parameter-value enumeration. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Three
open scoped Matrix BigOperators Classical

theorem ordinary_monodromy_six_product (p q : Fin 6 → ℕ) (m : ℝ) :
    Mono 6 p q m = realSixProduct (m-fk 6 p q m 0) (m-fk 6 p q m 1)
      (m-fk 6 p q m 2) (m-fk 6 p q m 3) (m-fk 6 p q m 4) (m-fk 6 p q m 5) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Mono, Tk, realSixProduct, realTransfer, List.finRange_succ] <;> ring
#print axioms Paper7C61Four.ordinary_monodromy_six_product

theorem ordinary_monodromy_shift (p q : Fin 6 → ℕ) (m : ℝ)
    (hm : Mono 6 p q m=1) : Mono 6 (shiftSix p) (shiftSix q) m=1 := by
  rw [ordinary_monodromy_six_product] at hm ⊢
  have hr := real_six_rotate _ _ _ _ _ _ hm
  simpa [fk, shiftSix] using hr
#print axioms Paper7C61Four.ordinary_monodromy_shift

theorem ordinary_monodromy_even_triple (p q : Fin 6 → ℕ) (m : ℝ)
    (hm : Mono 6 p q m=1) :
    m-fk 6 p q m 0 = (m-fk 6 p q m 2)+(m-fk 6 p q m 4)-
      (m-fk 6 p q m 2)*(m-fk 6 p q m 3)*(m-fk 6 p q m 4) := by
  rw [ordinary_monodromy_six_product] at hm
  have hr := real_six_rotate _ _ _ _ _ _ (real_six_rotate _ _ _ _ _ _ hm)
  exact (real_six_triple_data _ _ _ _ _ _ hr).2.2
#print axioms Paper7C61Four.ordinary_monodromy_even_triple

theorem mono_two_head_q_divisible_three (p q : Fin 6 → ℕ)
    (hm : Mono 6 p q 2=1) (hq2 : q 2=0) (hq3 : q 3=0) (hq4 : q 4=0) :
    3 ∣ q 0 := by
  have ht := ordinary_monodromy_even_triple p q 2 hm
  norm_num [fk, hq2, hq3, hq4] at ht
  let Z : ℤ := 16-4*(p 0 : ℤ)-4*(4-(p 2 : ℤ))-4*(4-(p 4 : ℤ))+
    (4-(p 2 : ℤ))*(4-(p 3 : ℤ))*(4-(p 4 : ℤ))
  have hZR : 16*(q 0 : ℝ)=3*(Z : ℝ) := by
    dsimp [Z]
    push_cast
    nlinarith only [ht]
  have hZI : 16*(q 0 : ℤ)=3*Z := by exact_mod_cast hZR
  have hd : (3 : ℤ) ∣ (q 0 : ℤ) := ⟨Z-5*(q 0 : ℤ), by omega⟩
  exact_mod_cast hd
#print axioms Paper7C61Four.mono_two_head_q_divisible_three

theorem mono_three_head_q_divisible_eight (p q : Fin 6 → ℕ)
    (hm : Mono 6 p q 3=1) (hq2 : q 2=0) (hq3 : q 3=0) (hq4 : q 4=0) :
    8 ∣ q 0 := by
  have ht := ordinary_monodromy_even_triple p q 3 hm
  norm_num [fk, hq2, hq3, hq4] at ht
  let Z : ℤ := 81-9*(p 0 : ℤ)-9*(9-(p 2 : ℤ))-9*(9-(p 4 : ℤ))+
    (9-(p 2 : ℤ))*(9-(p 3 : ℤ))*(9-(p 4 : ℤ))
  have hZR : 81*(q 0 : ℝ)=8*(Z : ℝ) := by
    dsimp [Z]
    push_cast
    nlinarith only [ht]
  have hZI : 81*(q 0 : ℤ)=8*Z := by exact_mod_cast hZR
  have hd : (8 : ℤ) ∣ (q 0 : ℤ) := ⟨Z-10*(q 0 : ℤ), by omega⟩
  exact_mod_cast hd
#print axioms Paper7C61Four.mono_three_head_q_divisible_eight

theorem singleton_total_eq_head (q : Fin 6 → ℕ)
    (hq : ∀ j : Fin 6, j ≠ 0 → q j=0) : totalQ 6 q=q 0 := by
  have hq1 := hq 1 (by decide)
  have hq2 := hq 2 (by decide)
  have hq3 := hq 3 (by decide)
  have hq4 := hq 4 (by decide)
  have hq5 := hq 5 (by decide)
  norm_num [totalQ, Fin.sum_univ_six, hq1, hq2, hq3, hq4, hq5]
#print axioms Paper7C61Four.singleton_total_eq_head

theorem mono_two_singleton_head_total_divisible_three (p q : Fin 6 → ℕ)
    (hm : Mono 6 p q 2=1) (hq : ∀ j : Fin 6, j ≠ 0 → q j=0) :
    3 ∣ totalQ 6 q := by
  rw [singleton_total_eq_head q hq]
  exact mono_two_head_q_divisible_three p q hm
    (hq 2 (by decide)) (hq 3 (by decide)) (hq 4 (by decide))
#print axioms Paper7C61Four.mono_two_singleton_head_total_divisible_three

theorem mono_three_singleton_head_total_divisible_eight (p q : Fin 6 → ℕ)
    (hm : Mono 6 p q 3=1) (hq : ∀ j : Fin 6, j ≠ 0 → q j=0) :
    8 ∣ totalQ 6 q := by
  rw [singleton_total_eq_head q hq]
  exact mono_three_head_q_divisible_eight p q hm
    (hq 2 (by decide)) (hq 3 (by decide)) (hq 4 (by decide))
#print axioms Paper7C61Four.mono_three_singleton_head_total_divisible_eight

end Paper7C61Four
