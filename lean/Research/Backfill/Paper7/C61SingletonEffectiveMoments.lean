import Research.Backfill.Paper7.C61SingletonEffectiveArithmetic

/-! NEW SOURCE ONLY. The two marked moment domains are treated by factor
signs and two-pair square inequalities, retaining all integral coordinates. -/
set_option autoImplicit false
namespace Paper7C61Four

theorem effective_five_three_impossible (b c d e f t : ℤ)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) (he0 : 0 ≤ e) (hf0 : 0 ≤ f)
    (ht0 : 0 ≤ t) (ht10 : t ≤ 10) (hd14 : d ≤ 14)
    (hs : b+c+d+e+f=28) (hq : b^2+c^2+d^2+e^2+f^2=244+2*t)
    (hmark : t+4=b ∨ t+4=c ∨ t+4=d ∨ t+4=e ∨ t+4=f)
    (hE : e=(b-3)*(c-4)) (hC : c=(f-3)*(e-4))
    (hDE : (4-d)*(4-e)=4*b-8) (hCD : (4-c)*(4-d)=4*f-8) : False := by
  have hz := five_positive_factors_small_square b c d e f (Or.inl hs)
    ⟨by intro _; omega,by intro hh; omega⟩ (by omega) hc0 he0 hE hC hDE hCD
  rcases hz with hz | hz
  · have hsmall : d+f=6 := by rw [hz] at hCD; nlinarith only [hCD]
    have hlarge : b+e=22 := by omega
    have hmark' : t+4=b ∨ t+4=e ∨ t+4=d ∨ t+4=f := by omega
    exact two_pairs_marked_three_impossible b e d f t hb0 he0 hd0 hf0 ht10 hlarge hsmall
      (by rw [hz] at hq; nlinarith only [hq]) hmark'
  · have hsmall : b+d=6 := by rw [hz] at hDE; nlinarith only [hDE]
    have hlarge : c+f=22 := by omega
    have hmark' : t+4=c ∨ t+4=f ∨ t+4=b ∨ t+4=d := by omega
    exact two_pairs_marked_three_impossible c f b d t hc0 hf0 hb0 hd0 ht10 hlarge hsmall
      (by rw [hz] at hq; nlinarith only [hq]) hmark'
#print axioms Paper7C61Four.effective_five_three_impossible

theorem effective_five_nine_impossible (b c d e f t : ℤ)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) (he0 : 0 ≤ e) (hf0 : 0 ≤ f)
    (ht0 : 0 ≤ t) (ht4 : t ≤ 4) (hd16 : d ≤ 16)
    (hs : b+c+d+e+f=30) (hq : b^2+c^2+d^2+e^2+f^2=288+6*t)
    (hmark : t+12=b ∨ t+12=c ∨ t+12=d ∨ t+12=e ∨ t+12=f)
    (hE : e=(b-3)*(c-4)) (hC : c=(f-3)*(e-4))
    (hDE : (4-d)*(4-e)=4*b-8) (hCD : (4-c)*(4-d)=4*f-8) : False := by
  have hz := five_positive_factors_small_square b c d e f (Or.inr hs)
    ⟨by intro hh; omega,by intro _; omega⟩ hd16 hc0 he0 hE hC hDE hCD
  rcases hz with hz | hz
  · have hsmall : d+f=6 := by rw [hz] at hCD; nlinarith only [hCD]
    have hlarge : b+e=24 := by omega
    have hmark' : t+12=b ∨ t+12=e ∨ t+12=d ∨ t+12=f := by omega
    exact two_pairs_marked_nine_impossible b e d f t hb0 he0 hd0 hf0 ht4 hlarge hsmall
      (by rw [hz] at hq; nlinarith only [hq]) hmark'
  · have hsmall : b+d=6 := by rw [hz] at hDE; nlinarith only [hDE]
    have hlarge : c+f=24 := by omega
    have hmark' : t+12=c ∨ t+12=f ∨ t+12=b ∨ t+12=d := by omega
    exact two_pairs_marked_nine_impossible c f b d t hc0 hf0 hb0 hd0 ht4 hlarge hsmall
      (by rw [hz] at hq; nlinarith only [hq]) hmark'
#print axioms Paper7C61Four.effective_five_nine_impossible

end Paper7C61Four
