import Research.Backfill.Paper7.TransferCentralWords

/-! Source-only descent for arbitrary integral transfer words bounded above
by one. Local surgery strictly decreases word length. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CentralWords
open Paper7TransferModFour
open scoped Matrix

def shifted (x : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1,1;-x-2,-x-1]
#print axioms Paper7CentralWords.shifted

theorem shifted_product_bounds (l : List ℤ) (hl : ∀ x ∈ l, x ≤ -2) :
    1 ≤ (l.map shifted).prod 0 0 ∧ 0 ≤ (l.map shifted).prod 1 0 ∧
      (l.length : ℤ) ≤ (l.map shifted).prod 0 1 ∧ 1 ≤ (l.map shifted).prod 1 1 := by
  induction l with
  | nil => norm_num
  | cons x l ih =>
    have hx := hl x (List.mem_cons_self ..)
    obtain ⟨h00,h10,h01,h11⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    have hlen : (0 : ℤ) ≤ l.length := Int.natCast_nonneg _
    have h01pos : 0 ≤ (l.map shifted).prod 0 1 := by omega
    have hc : 0 ≤ -x-2 := by omega
    have hd : 1 ≤ -x-1 := by omega
    have h10a := mul_nonneg hc (by omega : 0 ≤ (l.map shifted).prod 0 0)
    have h10b := mul_nonneg (by omega : 0 ≤ -x-1) h10
    have h11a := mul_nonneg hc h01pos
    have h11b := mul_nonneg (by omega : 0 ≤ (-x-1)-1) (by omega : 0 ≤ (l.map shifted).prod 1 1)
    norm_num [shifted,Matrix.mul_apply,Fin.sum_univ_two]
    exact ⟨by omega,by nlinarith only [h10a,h10b],by omega,by nlinarith only [h11a,h11b,h11]⟩
#print axioms Paper7CentralWords.shifted_product_bounds

theorem shifted_product_conjugacy (l : List ℤ) :
    (l.map shifted).prod = (-1 : ℤ)^l.length •
      ((!![0,-1;1,1] : Matrix (Fin 2) (Fin 2) ℤ)*word l*!![1,1;-1,0]) := by
  induction l with
  | nil =>
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [word,Matrix.mul_apply,Fin.sum_univ_two]
  | cons x l ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons]
    rw [ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [word,shifted,transfer,Matrix.mul_apply,Fin.sum_univ_two,pow_succ,smul_eq_mul,Matrix.vecMul,dotProduct,Matrix.vecHead,Matrix.vecTail]
    all_goals ring
#print axioms Paper7CentralWords.shifted_product_conjugacy

theorem large_negative_not_central (l : List ℤ) (hne : l ≠ [])
    (hl : ∀ x ∈ l, x ≤ -2) : ¬ Central (word l) := by
  intro hc
  have hb := (shifted_product_bounds l hl).2.2.1
  have hp : 0 < l.length := List.length_pos_iff.mpr hne
  have he := shifted_product_conjugacy l
  rcases hc with hc | hc
  all_goals
    rw [hc] at he
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) he
    norm_num [Matrix.mul_apply,Fin.sum_univ_two,smul_eq_mul] at hh
    omega
#print axioms Paper7CentralWords.large_negative_not_central

theorem central_deficit_bound (l : List ℤ) (hlen : 2 ≤ l.length)
    (hupper : ∀ x ∈ l, x ≤ 1) (hc : Central (word l)) :
    6 ≤ 3*(l.length : ℤ)+l.sum := by
  suffices ∀ n (l : List ℤ), l.length = n → 2 ≤ l.length →
      (∀ x ∈ l, x ≤ 1) → Central (word l) → 6 ≤ 3*(l.length : ℤ)+l.sum by
    exact this l.length l rfl hlen hupper hc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hlen htwo hupper hc
    by_cases hn : n = 2
    · have hl2 : l.length = 2 := hlen.trans hn
      cases l with
      | nil => simp at hl2
      | cons a l =>
        cases l with
        | nil => simp at hl2
        | cons b l =>
          have ht : l = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hl2; omega)
          subst l
          obtain ⟨rfl,rfl⟩ := central_two_zero a b hc
          norm_num
    have hthree : 3 ≤ l.length := by omega
    by_cases h1 : (1 : ℤ) ∈ l
    · obtain ⟨a,b,r,hperm,hc'⟩ := central_pivot l 1 h1 hthree hc
      have hlength := hperm.length_eq
      have hsum := hperm.sum_eq
      have hup (x : ℤ) (hx : x ∈ a::1::b::r) : x ≤ 1 := hupper x (hperm.mem_iff.mpr hx)
      have ha := hup a (by simp)
      have hb := hup b (by simp)
      have hrest (x : ℤ) (hx : x ∈ r) : x ≤ 1 := hup x (by simp [hx])
      have hnew : ∀ x ∈ (a-1)::(b-1)::r, x ≤ 1 := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · omega
        · omega
        · exact hrest x hx
      have hh := ih (((a-1)::(b-1)::r).length) (by simp only [List.length_cons] at hlength ⊢; omega)
        ((a-1)::(b-1)::r) rfl (by simp) hnew (central_surgery_one a b r hc')
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.sum_cons] at hh hlength hsum ⊢
      omega
    by_cases h0 : (0 : ℤ) ∈ l
    · obtain ⟨a,b,r,hperm,hc'⟩ := central_pivot l 0 h0 hthree hc
      have hlength := hperm.length_eq
      have hsum := hperm.sum_eq
      have hup (x : ℤ) (hx : x ∈ a::0::b::r) : x ≤ 0 := by
        have hx' := hperm.mem_iff.mpr hx
        have hxu := hupper x hx'
        have hx1 : x ≠ 1 := by intro he; subst x; exact h1 hx'
        omega
      have ha := hup a (by simp)
      have hb := hup b (by simp)
      have hnew : ∀ x ∈ (a+b)::r, x ≤ 1 := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · have hh := hup x (by simp [hx]); omega
      have hcent := central_surgery_zero a b r hc'
      have hr : r ≠ [] := by intro he; subst r; exact central_one_false (a+b) hcent
      have hh := ih (((a+b)::r).length) (by simp only [List.length_cons] at hlength ⊢; omega)
        ((a+b)::r) rfl (by have := List.length_pos_iff.mpr hr; simp only [List.length_cons]; omega) hnew hcent
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.sum_cons] at hh hlength hsum ⊢
      omega
    by_cases hm : (-1 : ℤ) ∈ l
    · obtain ⟨a,b,r,hperm,hc'⟩ := central_pivot l (-1) hm hthree hc
      have hlength := hperm.length_eq
      have hsum := hperm.sum_eq
      have hup (x : ℤ) (hx : x ∈ a::(-1)::b::r) : x ≤ -1 := by
        have hx' := hperm.mem_iff.mpr hx
        have hxu := hupper x hx'
        have hx1 : x ≠ 1 := by intro he; subst x; exact h1 hx'
        have hx0 : x ≠ 0 := by intro he; subst x; exact h0 hx'
        omega
      have ha := hup a (by simp)
      have hb := hup b (by simp)
      have hnew : ∀ x ∈ (a+1)::(b+1)::r, x ≤ 1 := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · omega
        · omega
        · have hh := hup x (by simp [hx]); omega
      have hh := ih (((a+1)::(b+1)::r).length) (by simp only [List.length_cons] at hlength ⊢; omega)
        ((a+1)::(b+1)::r) rfl (by simp) hnew (central_surgery_neg_one a b r hc')
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.sum_cons] at hh hlength hsum ⊢
      omega
    · apply False.elim
      apply large_negative_not_central l (by intro he; simp [he] at htwo) ?_ hc
      intro x hx
      have hh := hupper x hx
      have hx1 : x ≠ 1 := by intro he; subst x; exact h1 hx
      have hx0 : x ≠ 0 := by intro he; subst x; exact h0 hx
      have hxm : x ≠ -1 := by intro he; subst x; exact hm hx
      omega
#print axioms Paper7CentralWords.central_deficit_bound

end Paper7CentralWords
