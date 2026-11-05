import Mathlib

/-! Source-only. The character of integral determinant-one transfer products
modulo four. The local finite-ring identity is proved in Lean; no external
parameter enumeration or computed certificate is an input. -/
set_option autoImplicit false
noncomputable section
namespace Paper7TransferModFour
open scoped Matrix

def transfer {R : Type*} [Ring R] (x : R) : Matrix (Fin 2) (Fin 2) R :=
  !![x,-1;1,0]
#print axioms Paper7TransferModFour.transfer

def character (M : Matrix (Fin 2) (Fin 2) (ZMod 4)) : ZMod 4 :=
  if (M 1 0).val % 2 = 1 then (M 0 0+M 1 1+1)*M 1 0
  else (M 0 1-M 1 0+1)*M 0 0-1
#print axioms Paper7TransferModFour.character

theorem character_left_entries (x a b c d : ZMod 4) (h : a*d-b*c = 1) :
    (if a.val % 2 = 1 then (x*a-c+b+1)*a
      else (x*b-d-a+1)*(x*a-c)-1) =
    (if c.val % 2 = 1 then (a+d+1)*c else (b-c+1)*a-1)+x+1 := by
  have all_entries : ∀ x a b c d : ZMod 4, a*d-b*c = 1 →
      (if a.val % 2 = 1 then (x*a-c+b+1)*a
        else (x*b-d-a+1)*(x*a-c)-1) =
      (if c.val % 2 = 1 then (a+d+1)*c else (b-c+1)*a-1)+x+1 := by
    decide +kernel
  exact all_entries x a b c d h
#print axioms Paper7TransferModFour.character_left_entries

theorem character_left (x : ZMod 4) (M : Matrix (Fin 2) (Fin 2) (ZMod 4))
    (h : M.det = 1) : character (transfer x*M) = character M+x+1 := by
  have he : M 0 0*M 1 1-M 0 1*M 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using h
  simpa [character,transfer,Matrix.mul_apply,Fin.sum_univ_two,sub_eq_add_neg] using
    character_left_entries x (M 0 0) (M 0 1) (M 1 0) (M 1 1) he
#print axioms Paper7TransferModFour.character_left

theorem transfer_product_det (l : List (ZMod 4)) : (l.map transfer).prod.det = 1 := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons,List.prod_cons,Matrix.det_mul,ih,mul_one]
      simp [transfer,Matrix.det_fin_two]
#print axioms Paper7TransferModFour.transfer_product_det

theorem character_product (l : List (ZMod 4)) :
    character (l.map transfer).prod = (l.map (fun x => x+1)).sum := by
  induction l with
  | nil => norm_num [character]
  | cons x l ih =>
      rw [List.map_cons,List.prod_cons,character_left x _ (transfer_product_det l),ih]
      simp only [List.map_cons,List.sum_cons]
      ring
#print axioms Paper7TransferModFour.character_product

theorem transfer_product_map {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (l : List R) :
    f.mapMatrix (l.map transfer).prod = ((l.map f).map transfer).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons,List.prod_cons,map_mul,ih]
      congr 1
      ext i j
      change f (transfer x i j) = transfer (f x) i j
      fin_cases i <;> fin_cases j <;> simp [transfer]
#print axioms Paper7TransferModFour.transfer_product_map

theorem integer_transfer_identity_div_four (l : List ℤ)
    (h : ((l.map (Int.castRingHom ℝ)).map transfer).prod = 1) :
    (4 : ℤ) ∣ (l.map (fun x => x+1)).sum := by
  have hZ : (l.map transfer).prod = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    have hR := transfer_product_map (Int.castRingHom ℝ) l
    rw [h] at hR
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) hR
    change (((l.map transfer).prod i j : ℤ) : ℝ) = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j at hh
    fin_cases i <;> fin_cases j <;> norm_num at hh ⊢
    all_goals exact_mod_cast hh
  have h4 : ((l.map (Int.castRingHom (ZMod 4))).map transfer).prod = 1 := by
    rw [← transfer_product_map,hZ,map_one]
  have hc := character_product (l.map (Int.castRingHom (ZMod 4)))
  rw [h4] at hc
  have hsum : (((l.map (fun x => x+1)).sum : ℤ) : ZMod 4) = 0 := by
    have hm : (l.map (fun x : ℤ => (x : ZMod 4)+1)).sum = 0 := by
      simpa [character,List.map_map,Function.comp_def] using hc.symm
    simpa using hm
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hsum
#print axioms Paper7TransferModFour.integer_transfer_identity_div_four

end Paper7TransferModFour
