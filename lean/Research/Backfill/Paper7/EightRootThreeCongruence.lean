import Research.Backfill.Paper7.EightDoubleUnitExclusion

/-! NEW SOURCE ONLY repair after development 446. The five original
declarations are unchanged. Scalar factorization precedes list induction;
all denominators are cleared over the integers before reduction. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge Paper7TransferModFour
open scoped BigOperators Matrix Classical

def clearedThree (z : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![9-z,-3;3,0]
#print axioms Paper7EightCycle.clearedThree

theorem clearedThree_real_product (l : List ℤ) :
    (Int.castRingHom ℝ).mapMatrix (l.map clearedThree).prod = (3 : ℝ)^l.length •
      (l.map (fun z => transfer (3-(z : ℝ)/3))).prod := by
  have hstep (z : ℤ) : (Int.castRingHom ℝ).mapMatrix (clearedThree z) =
      (3 : ℝ) • transfer (3-(z : ℝ)/3) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [clearedThree,transfer,RingHom.mapMatrix,smul_eq_mul]
    all_goals ring
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,map_mul]
    rw [hstep,ih,smul_mul_smul_comm,pow_succ']
    have hbind (w : List ℤ) : (w >>= fun z => pure (z : ℝ)) =
        w.map (fun z : ℤ => (z : ℝ)) :=
      bind_pure_comp (fun z : ℤ => (z : ℝ)) w
    simp only [hbind,List.map_cons,List.prod_cons]
#print axioms Paper7EightCycle.clearedThree_real_product

theorem clearedThree_mod_four_product (l : List ℤ) :
    (Int.castRingHom (ZMod 4)).mapMatrix (l.map clearedThree).prod = (-1 : ZMod 4)^l.length •
      (l.map (fun z => transfer ((z : ZMod 4)+3))).prod := by
  have h3 : (3 : ZMod 4) = -1 := by decide
  have h9 : (9 : ZMod 4) = 1 := by decide
  have hstep (z : ℤ) : (Int.castRingHom (ZMod 4)).mapMatrix (clearedThree z) =
      (-1 : ZMod 4) • transfer ((z : ZMod 4)+3) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [clearedThree,transfer,RingHom.mapMatrix,smul_eq_mul]
    all_goals simp only [h3,h9,neg_neg]
    all_goals ring
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,map_mul]
    rw [hstep,ih,smul_mul_smul_comm,pow_succ']
    have hbind (w : List ℤ) : (w >>= fun z => pure (z : ZMod 4)) =
        w.map (fun z : ℤ => (z : ZMod 4)) :=
      bind_pure_comp (fun z : ℤ => (z : ZMod 4)) w
    simp only [hbind,List.map_cons,List.prod_cons]
#print axioms Paper7EightCycle.clearedThree_mod_four_product

theorem eight_three_word_div_four (l : List ℤ) (hlen : l.length = 8)
    (h : (l.map (fun z => transfer (3-(z : ℝ)/3))).prod = 1) : (4 : ℤ) ∣ l.sum := by
  have he := clearedThree_real_product l
  rw [hlen,h] at he
  norm_num at he
  have hZ : (l.map clearedThree).prod = (6561 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) he
    change (((l.map clearedThree).prod i j : ℤ) : ℝ) =
      ((6561 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j at hh
    fin_cases i <;> fin_cases j <;> norm_num at hh ⊢
    all_goals exact_mod_cast hh
  have hmod := clearedThree_mod_four_product l
  rw [hlen,hZ] at hmod
  have hroot : (l.map (fun z => transfer ((z : ZMod 4)+3))).prod = 1 := by
    have hh : (Int.castRingHom (ZMod 4)).mapMatrix
        ((6561 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)) = 1 := by
      have hcast : (6561 : ZMod 4) = 1 := by decide
      ext i j
      change ((((6561 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℤ) : ZMod 4) =
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 4)) i j
      simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij,hcast]
    rw [hh] at hmod
    norm_num at hmod
    exact hmod.symm
  have hc := character_product (l.map (fun z : ℤ => (z : ZMod 4)+3))
  have hmap : ((l.map (fun z : ℤ => (z : ZMod 4)+3)).map transfer).prod =
      (l.map (fun z => transfer ((z : ZMod 4)+3))).prod := by
    have hbind : (l >>= fun z => pure (z : ZMod 4)) =
        l.map (fun z : ℤ => (z : ZMod 4)) :=
      bind_pure_comp (fun z : ℤ => (z : ZMod 4)) l
    rw [hbind]
    simp only [List.map_map,Function.comp_def]
  rw [hmap,hroot] at hc
  have hs : ∀ w : List ℤ,
      ((w.map (fun z : ℤ => (z : ZMod 4)+3)).map (fun x => x+1)).sum = (w.sum : ZMod 4) := by
    intro w
    induction w with
    | nil => simp
    | cons z w ih =>
      simp only [List.map_cons,List.sum_cons,Int.cast_add]
      rw [ih]
      have h4 : (4 : ZMod 4) = 0 := by decide
      calc
        _ = (z : ZMod 4)+(w.sum : ZMod 4)+4 := by ring
        _ = _ := by rw [h4,add_zero]
  rw [hs l] at hc
  have hz : (l.sum : ZMod 4) = 0 := by simpa [character] using hc.symm
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hz
#print axioms Paper7EightCycle.eight_three_word_div_four

theorem eight_double_three_four_dvd_total (p : Fin 8 → ℕ)
    (hm : mult (SG 8 p (fun _ => 0)) 3 = 2) : (4 : ℤ) ∣ ((∑ i, p i : ℕ) : ℤ) := by
  have hid := ((Paper7Lemma22.check_Lemma22 8 p (fun _ => 0) (by decide)).1 3
    (by norm_num) (by norm_num) (by norm_num)).2.2.1.mp hm
  let l : List ℤ := (List.finRange 8).reverse.map (fun i => (p i : ℤ))
  have ht (i : Fin 8) : transfer (3-((p i : ℤ) : ℝ)/3) = Tk 8 p (fun _ => 0) 3 i := by
    norm_num [Tk,fk,transfer]
  have hprod : (l.map (fun z => transfer (3-(z : ℝ)/3))).prod = Mono 8 p (fun _ => 0) 3 := by
    simp only [l]
    change ((List.finRange 8).reverse.map
      (fun i => transfer (3-((p i : ℤ) : ℝ)/3))).prod =
        ((List.finRange 8).reverse.map (Tk 8 p (fun _ => 0) 3)).prod
    apply congrArg List.prod
    apply List.map_congr_left
    intro i _
    exact ht i
  have hh := eight_three_word_div_four l (by simp [l]) (hprod.trans hid)
  have hsum : l.sum = ((∑ i, p i : ℕ) : ℤ) := by
    norm_num [l,List.finRange_succ,Fin.sum_univ_succ]
    ring
  rwa [hsum] at hh
#print axioms Paper7EightCycle.eight_double_three_four_dvd_total

end Paper7EightCycle
