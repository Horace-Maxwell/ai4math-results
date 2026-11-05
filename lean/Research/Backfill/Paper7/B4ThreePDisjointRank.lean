import Research.Backfill.Paper7.B4ThreePDisjointUnitArithmetic
import Research.Backfill.Paper7.B4ThreePSpectralRank

/-! Source-only actual exceptional kernel and positive spectral cardinality.
The unit offset follows from the Wmat recurrence, not a determinant premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem three_unit_recurrence_zero (a b c x y z : ℝ)
    (hd : threePDisjointDelta a b c ≠ 0)
    (h0 : y = (1-a)*x) (h1 : x+z = (1-b)*y) (h2 : y = (1-c)*z) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hz : z = ((1-b)*(1-a)-1)*x := by
    rw [h0] at h1
    nlinarith only [h1]
  have he : threePDisjointDelta a b c*x = 0 := by
    rw [h0,hz] at h2
    unfold threePDisjointDelta
    nlinarith only [h2]
  have hx : x = 0 := (mul_eq_zero.mp he).resolve_left hd
  exact ⟨hx,by rw [h0,hx,mul_zero],by rw [hz,hx,mul_zero]⟩
#print axioms Paper7B4Analytic.three_unit_recurrence_zero

theorem three_disjoint_unit_delta_zero (a b c d : ℕ) (hd : 0 < d)
    (hdet : threePDisjointDelta a b c ≠ 0) :
    deltaE 4 (threePDisjointP a b c) (threePDisjointQ d) 1 = 0 := by
  have hker : LinearMap.ker (Matrix.toLin'
      (Wmat 4 (threePDisjointP a b c) (threePDisjointQ d) 1)) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hrows := (Paper7Lemma22Gaps.mem_ker_Wmat_iff 4
      (threePDisjointP a b c) (threePDisjointQ d) 1 y).mp hy
    have hy3 : y 3 = 0 := by
      simpa [threePDisjointQ,hd] using hrows 3
    have h0 := hrows 0
    have h1 := hrows 1
    have h2 := hrows 2
    norm_num [threePDisjointP,threePDisjointQ] at h0 h1 h2
    have hp0 : prv 4 (0 : Fin 4) = 3 := by decide
    have hp1 : prv 4 (1 : Fin 4) = 0 := by decide
    have hp2 : prv 4 (2 : Fin 4) = 1 := by decide
    have hn0 : nxt 4 (0 : Fin 4) = 1 := by decide
    have hn1 : nxt 4 (1 : Fin 4) = 2 := by decide
    have hn2 : nxt 4 (2 : Fin 4) = 3 := by decide
    simp only [hp0,hp1,hp2,hn0,hn1,hn2,hy3,zero_add,add_zero] at h0 h1 h2
    obtain ⟨hy0,hy1,hy2⟩ := three_unit_recurrence_zero a b c (y 0) (y 1) (y 2)
      hdet h0 h1 h2
    funext i
    change y i = 0
    fin_cases i
    · exact hy0
    · exact hy1
    · exact hy2
    · exact hy3
  unfold deltaE
  rw [hker]
  simp
#print axioms Paper7B4Analytic.three_disjoint_unit_delta_zero

theorem three_disjoint_integral_big_card (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hG : IsIntegralGraph (SG 4 (threePDisjointP a b c) (threePDisjointQ d))) :
    (Bplus (SG 4 (threePDisjointP a b c) (threePDisjointQ d))).card = 4 := by
  let p := threePDisjointP a b c
  let q := threePDisjointQ d
  have hdet := (three_disjoint_integral_delta_positive a b c d ha hb hc hd hG).2.2.2
  have hdelta : deltaE 4 p q 1 = 0 := three_disjoint_unit_delta_zero a b c d hd
    (ne_of_gt hdet)
  have hKq : Kq 4 q = {3} := by
    ext i
    fin_cases i <;> simp [Kq,q,threePDisjointQ,hd]
  have hQ : ∑ i, q i = d := by simp [q,threePDisjointQ,Fin.sum_univ_four]
  have hP : ∑ i, p i = a+b+c := by simp [p,threePDisjointP,Fin.sum_univ_four]
  obtain ⟨hKp,hdelta0⟩ := three_positive_delta_zero p
    (by simpa [p,threePDisjointP] using ha)
    (by simpa [p,threePDisjointP] using hb)
    (by simpa [p,threePDisjointP] using hc)
    (by simp [p,threePDisjointP])
  have hzero := (Paper7Lemma22.check_Lemma22 4 p q (by decide)).2.1
  rw [hKp,hdelta0,hP] at hzero
  have hunit := ((Paper7Lemma22.check_Lemma22 4 p q (by decide)).2.2.1 1 (Or.inl rfl)).1
  rw [hKq,hdelta,hQ] at hunit
  norm_num at hunit
  have hs := Paper7Admissible.lemma24_counting_even 4 p q (by decide) hG (by decide)
  have hcard := Paper7Counting.symmetric_spectrum_card (SG 4 p q) hG hs.1
  change order 4 (pq 4 p q) = _ at hcard
  rw [Paper7Setup.sg_order,← hs.1 1] at hcard
  simp only [nOf,hP,hQ] at hcard
  change (Bplus (SG 4 p q)).card = 4
  omega
#print axioms Paper7B4Analytic.three_disjoint_integral_big_card

end Paper7B4Analytic
