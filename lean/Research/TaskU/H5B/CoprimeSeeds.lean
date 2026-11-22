import Research.TaskU.H5.IntegerFactors
import Research.TaskU.H5.Audit
import Research.TaskU.H5B.ChallengeB

namespace TaskU.H5.Coprime
noncomputable section
open Finset Matrix

private def central (s : F → ℤ) (g : H) : ℤ :=
  if g.a=0 ∧ g.b=0 then s g.c else 0

private def flat (d : F → F → ℤ) (g : H) : ℤ := d g.a g.b

private theorem flat_zero (d : F → F → ℤ) (r : F) (hr : r ≠ 0) :
    frequencyBlock (flat d) 0 r = 0 := by
  ext i j : 1
  simp only [frequencyBlock, Matrix.of_apply, Matrix.zero_apply, sumH, flat]
  apply sum_eq_zero
  intro a _
  apply sum_eq_zero
  intro b _
  by_cases h : i = a+j
  · simp only [h,ite_true,zero_mul,zero_add,mul_add,AddChar.map_add_eq_mul]
    simp_rw [← mul_assoc,← sum_mul,← mul_sum, orthog, ite_eq_right hr, mul_zero, zero_mul]
  · simp [h]

private theorem block_add (f g : H → ℤ) (r : F) :
    frequencyBlock (fun x => f x + g x) 0 r = frequencyBlock f 0 r + frequencyBlock g 0 r := by
  ext i j : 1
  simp only [frequencyBlock, Matrix.of_apply, Matrix.add_apply, ← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  split_ifs <;> push_cast <;> ring

private theorem central_block (s : F → ℤ) (r : F) :
    frequencyBlock (central s) 0 r = diagonal (fun _ => ∑ c, (s c:ℂ)*ch (r*c)) := by
  ext i j : 1
  rw [frequencyBlock, Matrix.of_apply, sumH, diagonal_apply]
  simp only [central, zero_mul, zero_add]
  rw [sum_eq_single (0:F)]
  · rw [sum_eq_single (0:F)]
    · by_cases h : i=j <;> simp [h]
    · intro b _ hb; simp [hb]
    · simp
  · intro a _ ha; simp [ha]
  · simp

private def zcoeff (e : Bool) (k : F) : ℤ :=
  (if k=0 then 1 else 0) + (if e=true ∧ k=1 then 1 else 0)

private def seedTable (e : Bool) (a b : F) : ℤ :=
  if e=false then 0 else if a=0 then
    if b=0 then -2685 else if b=1 ∨ b=4 then -2684 else -2683
  else if a=1 ∨ a=4 then -829 else 2172

def coprimeSeed (e : Bool) (k : ℤ) (g : H) : ℤ :=
  central (zcoeff e) g + flat (seedTable e) g + k

private theorem augmented (e : Bool) (k : ℤ) :
    aug (coprimeSeed e k) = (if e then 57 else 1) + 125*k := by
  have hc : aug (coprimeSeed e 0) = if e then 57 else 1 := by cases e <;> decide +kernel
  have he (g : H) : coprimeSeed e k g = coprimeSeed e 0 g + k := by simp [coprimeSeed]
  rw [aug]
  simp only [he,sum_add_distrib, sum_const,card_univ,nsmul_eq_mul]
  rw [← aug, hc, Audit.order_check]
  norm_num

private theorem interp (s : F → ℤ) (d : F → F → ℤ) (r : F) (hr : r ≠ 0) :
    (frequencyBlock (fun g => central s g + flat d g) 0 r).det =
      (∑ c, (s c:ℂ)*ch (r*c))^5 := by
  rw [block_add,flat_zero d r hr,add_zero,central_block, det_diagonal]
  simp [ZMod.card]

private theorem seed_nonlinear (e : Bool) (k : ℤ) : Cyc5.norm (TraceWords.nonlinear (coprimeSeed e k)) = 1 := by
  apply Int.cast_injective (α := ℂ)
  rw [norm_values]
  have hs (r : F) (hr : r ≠ 0) : Cyc5.val (TraceWords.nonlinear (coprimeSeed e k)) (ch r) =
        (Cyc5.val (profile (zcoeff e)) (ch r))^5 := by
    rw [val_nonlinear _ _ hr, evalProfile _ _ hr]
    let d := fun a b => seedTable e a b + k
    have he : coprimeSeed e k = fun g => central (zcoeff e) g + flat d g := by
      funext g; simp [coprimeSeed,flat,d,add_assoc]
    rw [he,interp _ _ r hr]
  calc
    _ = ∏ r ∈ (univ : Finset F).erase 0, (Cyc5.val (profile (zcoeff e)) (ch r))^5 :=
      prod_congr rfl (fun r h => hs r (ne_of_mem_erase h))
    _ = _ := by
      rw [prod_pow,← norm_values, show Cyc5.norm (profile (zcoeff e))=1 by cases e <;> decide +kernel]
      norm_num

private theorem ray_of_shift (f : H → ℤ) (u v : F) (k : ℤ) (h : (u,v) ≠ (0,0)) :
    ray (fun g => f g+k) u v = ray f u v := by
  have cnt : ∀ x y : F, (x,y) ≠ (0,0) → ∀ j : F,
      counts (fun _ : H => 1) (fun g => x*g.a+y*g.b) j = 25 := by decide +kernel
  have hc (i : F) : counts (fun g => f g+k) (fun g => u*g.a+v*g.b) i =
      counts f (fun g => u*g.a+v*g.b) i + 25*k := by
    rw [← cnt u v h i]
    simp only [counts,sum_mul,← sum_add_distrib]
    apply sum_congr rfl
    intro g _
    split_ifs <;> ring
  ext <;> simp [ray,profile,hc]

private theorem seed_one (e : Bool) (k : ℤ) :
    Cyc5.norm (ray (coprimeSeed e k) 1 0) = 1 ∧
      ∀ j : F, Cyc5.norm (ray (coprimeSeed e k) j 1) = 1 := by
  have h1 : ∀ e : Bool, ∀ u v : F, (u,v) ≠ (0,0) →
      Cyc5.norm (ray (coprimeSeed e 0) u v) = 1 := by decide +kernel
  have he : coprimeSeed e k = fun g => coprimeSeed e 0 g+k := by funext g; simp [coprimeSeed]
  rw [he]
  constructor
  · rw [ray_of_shift _ _ _ _ (by decide)]
    exact h1 _ _ _ (by decide)
  · intro j
    have hn : (j,(1:F)) ≠ (0,0) := fun h => (by decide : (1:F)≠0) (congrArg Prod.snd h)
    rw [ray_of_shift _ _ _ _ hn]
    exact h1 _ _ _ hn

theorem seed_det (e : Bool) (k : ℤ) :
    groupDet (coprimeSeed e k) = (if e then 57 else 1) + 125*k := by
  obtain ⟨hh,hj⟩ := seed_one e k
  rw [integerFactorization,hh,seed_nonlinear]
  simp [hj,augmented]

theorem det_neg (f : H → ℤ) : groupDet (fun g => -f g) = -groupDet f := by
  unfold groupDet
  let A : Matrix H H ℤ := Matrix.of fun g h => f (g*h⁻¹)
  change (-A).det = -A.det
  rw [Matrix.det_neg,Audit.order_check]
  ring

theorem coprime_sufficient (m : ℤ) (h : m^4 ≡ 1 [ZMOD 125]) :
    ∃ f : H → ℤ, groupDet f = m := by
  have he := (ZMod.intCast_eq_intCast_iff _ _ 125).mpr h
  push_cast at he
  have hc : ∀ x : ZMod 125, x^4=1 → x=1 ∨ x=57 ∨ x= -1 ∨ x= -57 := by decide +kernel
  have lift (n : ℤ) (hn : (m:ZMod 125)=n) : ∃ k : ℤ, m = n + 125*k := by
    have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 125).mp hn
    obtain ⟨l,hl⟩ := hh
    exact ⟨-l,by push_cast at hl; omega⟩
  rcases hc _ he with h1|h2|h3|h4
  · obtain ⟨k,hk⟩ := lift 1 (by simpa using h1)
    exact ⟨_,(seed_det false k).trans hk.symm⟩
  · obtain ⟨k,hk⟩ := lift 57 (by simpa using h2)
    exact ⟨_,(seed_det true k).trans hk.symm⟩
  · obtain ⟨k,hk⟩ := lift (-1) (by simpa using h3)
    refine ⟨fun g => -coprimeSeed false (-k) g,?_⟩
    rw [det_neg,seed_det,hk]; norm_num; ring
  · obtain ⟨k,hk⟩ := lift (-57) (by simpa using h4)
    refine ⟨fun g => -coprimeSeed true (-k) g,?_⟩
    rw [det_neg,seed_det,hk]; norm_num; ring

end
end TaskU.H5.Coprime
