import Research.Backfill.Paper7.C61SingletonEffectiveMoments
import Research.Backfill.Paper7.C61FourTwentyEightExclusion

/-! NEW SOURCE ONLY. Cyclic transport of the complete effective-parameter
obstruction, including a distinguished site and an arbitrary zero site. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Parameters Paper7C61Three
open scoped BigOperators Classical

def EffectiveSingletonData (r : Fin 6 → ℕ) (k t : ℕ) : Prop :=
  totalP 6 r=27+k ∧ squares 6 r+6*k=243+2*k*t+7*k^2 ∧
    t+3*k≤13 ∧ (∀ j, r j≤13+k) ∧ (∃ j, r j=t+4*k) ∧
    Mono 6 r (fun _ => 0) 2=1
#print axioms Paper7C61Four.EffectiveSingletonData

theorem effective_singleton_data_shift (r : Fin 6 → ℕ) (k t : ℕ)
    (h : EffectiveSingletonData r k t) : EffectiveSingletonData (shiftSix r) k t := by
  obtain ⟨hP,hS,ht,hcap,⟨j,hj⟩,hm⟩ := h
  refine ⟨by rw [totalP_shift]; exact hP,?_,ht,fun j => hcap (j+1),?_,
    mono_two_qzero_shift r hm⟩
  · have he : squares 6 (shiftSix r)=squares 6 r := by
      simpa only [squares,shiftSix] using sum_shift_nat (fun j => r j^2)
    rw [he]
    exact hS
  · refine ⟨j+5,?_⟩
    simpa [shiftSix,add_assoc] using hj
#print axioms Paper7C61Four.effective_singleton_data_shift

theorem effective_singleton_head_zero_impossible (r : Fin 6 → ℕ) (k t : ℕ)
    (hk : k=1 ∨ k=2 ∨ k=3) (hz : r 0=0)
    (h : EffectiveSingletonData r k t) : False := by
  obtain ⟨hP,hS,ht,hcap,⟨j,hj⟩,hm⟩ := h
  have hn := mono_two_pair_numerators r hm
  rw [mono_two_six_product] at hm
  have hd := real_six_triple_data _ _ _ _ _ _ hm
  have hr := real_six_rotate _ _ _ _ _ _ (real_six_rotate _ _ _ _ _ _ hm)
  have hrotate := (real_six_triple_data _ _ _ _ _ _ hr).2.2
  have hreverse : coefficientTwo r (fun _ => 0) 2 = coefficientTwo r (fun _ => 0) 0 +
      coefficientTwo r (fun _ => 0) 4-coefficientTwo r (fun _ => 0) 0 *
        coefficientTwo r (fun _ => 0) 5 * coefficientTwo r (fun _ => 0) 4 := by
    linear_combination -hd.2.2 + coefficientTwo r (fun _ => 0) 0*hd.2.1
  have hpoly := hd.2.2
  norm_num [coefficientTwo,hz] at hpoly hreverse hrotate
  have hE : (r 4 : ℤ)=((r 1 : ℤ)-3)*((r 2 : ℤ)-4) := by
    exact_mod_cast (by nlinarith only [hpoly] :
      (r 4 : ℝ)=((r 1 : ℝ)-3)*((r 2 : ℝ)-4))
  have hC : (r 2 : ℤ)=((r 5 : ℤ)-3)*((r 4 : ℤ)-4) := by
    exact_mod_cast (by nlinarith only [hreverse] :
      (r 2 : ℝ)=((r 5 : ℝ)-3)*((r 4 : ℝ)-4))
  have hDE : (4-(r 3 : ℤ))*(4-(r 4 : ℤ))=4*(r 1 : ℤ)-8 := by
    have hi := hn.1
    norm_num [hz] at hi
    nlinarith only [hi]
  have hCD : (4-(r 2 : ℤ))*(4-(r 3 : ℤ))=4*(r 5 : ℤ)-8 := by
    have hi := hn.2.2
    norm_num [hz] at hi
    nlinarith only [hi]
  have htriple : (16 : ℤ)=4*((4-(r 2 : ℤ))+(4-(r 4 : ℤ)))-
      (4-(r 2 : ℤ))*(4-(r 3 : ℤ))*(4-(r 4 : ℤ)) := by
    exact_mod_cast (by nlinarith only [hrotate] : (16 : ℝ)=
      4*((4-(r 2 : ℝ))+(4-(r 4 : ℝ)))-
      (4-(r 2 : ℝ))*(4-(r 3 : ℝ))*(4-(r 4 : ℝ)))
  have hPN : r 1+r 2+r 3+r 4+r 5=27+k := by
    simpa [totalP,Fin.sum_univ_six,hz,Nat.add_assoc] using hP
  have hPZ : (r 1 : ℤ)+r 2+r 3+r 4+r 5=27+k := by exact_mod_cast hPN
  have hSN : r 1^2+r 2^2+r 3^2+r 4^2+r 5^2+6*k=243+2*k*t+7*k^2 := by
    simpa [squares,Fin.sum_univ_six,hz,Nat.add_assoc] using hS
  have hSZ : (r 1 : ℤ)^2+(r 2 : ℤ)^2+(r 3 : ℤ)^2+(r 4 : ℤ)^2+(r 5 : ℤ)^2+
      6*(k : ℤ)=243+2*(k : ℤ)*t+7*(k : ℤ)^2 := by exact_mod_cast hSN
  have htZ : (t : ℤ)+3*k≤13 := by exact_mod_cast ht
  have hcapZ (i : Fin 6) : (r i : ℤ)≤13+k := by exact_mod_cast hcap i
  have hmark : (t : ℤ)+4*k=r 1 ∨ (t : ℤ)+4*k=r 2 ∨ (t : ℤ)+4*k=r 3 ∨
      (t : ℤ)+4*k=r 4 ∨ (t : ℤ)+4*k=r 5 := by
    have hjZ : (r j : ℤ)=(t : ℤ)+4*k := by exact_mod_cast hj
    fin_cases j
    · change (r (0 : Fin 6) : ℤ)=(t : ℤ)+4*k at hjZ
      rw [hz] at hjZ
      norm_num at hjZ
      rcases hk with hk | hk | hk <;> omega
    · change (r (1 : Fin 6) : ℤ)=(t : ℤ)+4*k at hjZ
      exact Or.inl hjZ.symm
    · change (r (2 : Fin 6) : ℤ)=(t : ℤ)+4*k at hjZ
      exact Or.inr (Or.inl hjZ.symm)
    · change (r (3 : Fin 6) : ℤ)=(t : ℤ)+4*k at hjZ
      exact Or.inr (Or.inr (Or.inl hjZ.symm))
    · change (r (4 : Fin 6) : ℤ)=(t : ℤ)+4*k at hjZ
      exact Or.inr (Or.inr (Or.inr (Or.inl hjZ.symm)))
    · change (r (5 : Fin 6) : ℤ)=(t : ℤ)+4*k at hjZ
      exact Or.inr (Or.inr (Or.inr (Or.inr hjZ.symm)))
  rcases hk with rfl | rfl | rfl
  · apply effective_five_three_impossible (r 1) (r 2) (r 3) (r 4) (r 5) t
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by omega) (by have hi := hcapZ 3; omega)
      (by norm_num at hPZ; exact hPZ) (by norm_num at hSZ; omega)
      (by norm_num at hmark; exact hmark) hE hC hDE hCD
  · apply twenty_nine_scalar_impossible (r 1) (r 2) (r 3) (r 4) (r 5)
      (by positivity) (by have hi := hcapZ 3; omega)
      (by positivity) (by have hi := hcapZ 2; omega)
      (by positivity) (by have hi := hcapZ 4; omega)
      (by norm_num at hPZ; exact hPZ) (by nlinarith only [hDE])
      (by nlinarith only [hCD]) htriple
  · apply effective_five_nine_impossible (r 1) (r 2) (r 3) (r 4) (r 5) t
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by omega) (by have hi := hcapZ 3; omega)
      (by norm_num at hPZ; exact hPZ) (by norm_num at hSZ; omega)
      (by norm_num at hmark; exact hmark) hE hC hDE hCD
#print axioms Paper7C61Four.effective_singleton_head_zero_impossible

theorem effective_singleton_zero_impossible (r : Fin 6 → ℕ) (k t : ℕ)
    (hk : k=1 ∨ k=2 ∨ k=3) (hz : ∃ j, r j=0)
    (h : EffectiveSingletonData r k t) : False := by
  let r1 := shiftSix r
  let r2 := shiftSix r1
  let r3 := shiftSix r2
  let r4 := shiftSix r3
  let r5 := shiftSix r4
  have h1 := effective_singleton_data_shift r k t h
  have h2 := effective_singleton_data_shift r1 k t h1
  have h3 := effective_singleton_data_shift r2 k t h2
  have h4 := effective_singleton_data_shift r3 k t h3
  have h5 := effective_singleton_data_shift r4 k t h4
  obtain ⟨j,hj⟩ := hz
  fin_cases j
  · exact effective_singleton_head_zero_impossible r k t hk hj h
  · apply effective_singleton_head_zero_impossible r1 k t hk _ h1
    change r (1 : Fin 6)=0 at hj
    simpa [r1,shiftSix] using hj
  · apply effective_singleton_head_zero_impossible r2 k t hk _ h2
    change r (2 : Fin 6)=0 at hj
    simpa [r2,r1,shiftSix] using hj
  · apply effective_singleton_head_zero_impossible r3 k t hk _ h3
    change r (3 : Fin 6)=0 at hj
    simpa [r3,r2,r1,shiftSix] using hj
  · apply effective_singleton_head_zero_impossible r4 k t hk _ h4
    change r (4 : Fin 6)=0 at hj
    simpa [r4,r3,r2,r1,shiftSix] using hj
  · apply effective_singleton_head_zero_impossible r5 k t hk _ h5
    change r (5 : Fin 6)=0 at hj
    simpa [r5,r4,r3,r2,r1,shiftSix] using hj
#print axioms Paper7C61Four.effective_singleton_zero_impossible

end Paper7C61Four
