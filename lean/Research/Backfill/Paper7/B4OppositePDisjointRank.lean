import Research.Backfill.Paper7.B4OppositePDisjointSpectrum
import Research.Backfill.Paper7.B4QzeroFullSupport

/-! Source-only exact zero and unit multiplicities for disjoint opposite P/Q. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

def oppositeP (a c : ℕ) : Fin 4 → ℕ := ![a,0,c,0]
#print axioms Paper7B4Analytic.oppositeP
def oppositeQ (b d : ℕ) : Fin 4 → ℕ := ![0,b,0,d]
#print axioms Paper7B4Analytic.oppositeQ

theorem opposite_unit_kernel_iff (a c b d : ℕ) (y : Fin 4 → ℝ) :
    y ∈ LinearMap.ker (Matrix.toLin' (Wmat 4 (oppositeP a c) (oppositeQ b d) 1)) ↔
      (if 0 < b then y 1 = 0 else y 0+y 2 = y 1) ∧
      (if 0 < d then y 3 = 0 else y 2+y 0 = y 3) ∧
      y 3+y 1 = (1-(a : ℝ))*y 0 ∧ y 1+y 3 = (1-(c : ℝ))*y 2 := by
  have hp0 : prv 4 (0 : Fin 4) = 3 := by decide
  have hp1 : prv 4 (1 : Fin 4) = 0 := by decide
  have hp2 : prv 4 (2 : Fin 4) = 1 := by decide
  have hp3 : prv 4 (3 : Fin 4) = 2 := by decide
  have hn0 : nxt 4 (0 : Fin 4) = 1 := by decide
  have hn1 : nxt 4 (1 : Fin 4) = 2 := by decide
  have hn2 : nxt 4 (2 : Fin 4) = 3 := by decide
  have hn3 : nxt 4 (3 : Fin 4) = 0 := by decide
  rw [Paper7Lemma22Gaps.mem_ker_Wmat_iff]
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · simpa [oppositeP,oppositeQ,hp1,hn1] using h 1
    · simpa [oppositeP,oppositeQ,hp3,hn3] using h 3
    · simpa [oppositeP,oppositeQ,hp0,hn0] using h 0
    · simpa [oppositeP,oppositeQ,hp2,hn2] using h 2
  · rintro ⟨h1,h3,h0,h2⟩ i
    fin_cases i
    · simpa [oppositeP,oppositeQ,hp0,hn0] using h0
    · simpa [oppositeP,oppositeQ,hp1,hn1] using h1
    · simpa [oppositeP,oppositeQ,hp2,hn2] using h2
    · simpa [oppositeP,oppositeQ,hp3,hn3] using h3
#print axioms Paper7B4Analytic.opposite_unit_kernel_iff

theorem opposite_unit_delta_zero_two_q (a c b d : ℕ)
    (ha : a ≠ 1) (hc : c ≠ 1) (hb : 0 < b) (hd : 0 < d) :
    deltaE 4 (oppositeP a c) (oppositeQ b d) 1 = 0 := by
  have haR : 1-(a : ℝ) ≠ 0 := by
    intro hh
    apply ha
    have he : (a : ℝ) = 1 := by linarith
    exact_mod_cast he
  have hcR : 1-(c : ℝ) ≠ 0 := by
    intro hh
    apply hc
    have he : (c : ℝ) = 1 := by linarith
    exact_mod_cast he
  have hker : LinearMap.ker (Matrix.toLin' (Wmat 4 (oppositeP a c) (oppositeQ b d) 1)) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    obtain ⟨h1,h3,h0,h2⟩ := (opposite_unit_kernel_iff a c b d y).mp hy
    simp only [hb,hd,ite_true] at h1 h3
    rw [h1,h3,zero_add] at h0 h2
    have hy0 : y 0 = 0 := (mul_eq_zero.mp h0.symm).resolve_left haR
    have hy2 : y 2 = 0 := (mul_eq_zero.mp h2.symm).resolve_left hcR
    funext i
    fin_cases i
    · change y (0 : Fin 4) = 0
      exact hy0
    · change y (1 : Fin 4) = 0
      exact h1
    · change y (2 : Fin 4) = 0
      exact hy2
    · change y (3 : Fin 4) = 0
      exact h3
  unfold deltaE
  rw [hker]
  simp
#print axioms Paper7B4Analytic.opposite_unit_delta_zero_two_q

theorem opposite_unit_delta_zero_one_q (a c b : ℕ)
    (_ha : 0 < a) (_hc : 0 < c) (hb : 0 < b) (hnot : ¬ (a = 1 ∧ c = 1)) :
    deltaE 4 (oppositeP a c) (oppositeQ b 0) 1 = 0 := by
  have hac : a*c ≠ 1 := by
    intro hh
    exact hnot ⟨Nat.eq_one_of_mul_eq_one_right hh, Nat.eq_one_of_mul_eq_one_left hh⟩
  have hprodR : (a : ℝ)*c-1 ≠ 0 := by
    intro hh
    apply hac
    have he : (a : ℝ)*c = 1 := by linarith
    exact_mod_cast he
  have hker : LinearMap.ker (Matrix.toLin' (Wmat 4 (oppositeP a c) (oppositeQ b 0) 1)) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    obtain ⟨h1,h3,h0,h2⟩ := (opposite_unit_kernel_iff a c b 0 y).mp hy
    simp only [hb,ite_true] at h1
    norm_num at h3
    rw [h1,add_zero] at h0
    rw [h1,zero_add] at h2
    have hy3 : y 3 = (1-(a : ℝ))*y 0 := h0
    have hy2 : y 2 = -(a : ℝ)*y 0 := by rw [hy3] at h3; nlinarith only [h3]
    have he : ((a : ℝ)*c-1)*y 0 = 0 := by
      rw [hy3,hy2] at h2
      nlinarith only [h2]
    have hy0 : y 0 = 0 := (mul_eq_zero.mp he).resolve_left hprodR
    have hy2z : y 2 = 0 := by rw [hy2,hy0,mul_zero]
    have hy3z : y 3 = 0 := by rw [hy3,hy0,mul_zero]
    funext i
    fin_cases i
    · change y (0 : Fin 4) = 0
      exact hy0
    · change y (1 : Fin 4) = 0
      exact h1
    · change y (2 : Fin 4) = 0
      exact hy2z
    · change y (3 : Fin 4) = 0
      exact hy3z
  unfold deltaE
  rw [hker]
  simp
#print axioms Paper7B4Analytic.opposite_unit_delta_zero_one_q

theorem opposite_unit_delta_one (c b d : ℕ) (hc : c ≠ 1) (hb : 0 < b) (hd : 0 < d) :
    deltaE 4 (oppositeP 1 c) (oppositeQ b d) 1 = 1 := by
  let K := LinearMap.ker (Matrix.toLin' (Wmat 4 (oppositeP 1 c) (oppositeQ b d) 1))
  have hcR : 1-(c : ℝ) ≠ 0 := by
    intro hh
    apply hc
    have he : (c : ℝ) = 1 := by linarith
    exact_mod_cast he
  have hK (y : Fin 4 → ℝ) : y ∈ K ↔ y 1 = 0 ∧ y 2 = 0 ∧ y 3 = 0 := by
    rw [opposite_unit_kernel_iff]
    simp only [hb,hd,ite_true]
    constructor
    · rintro ⟨h1,h3,_h0,h2⟩
      have he : (1-(c : ℝ))*y 2 = 0 := by rw [h1,h3,zero_add] at h2; exact h2.symm
      exact ⟨h1,(mul_eq_zero.mp he).resolve_left hcR,h3⟩
    · rintro ⟨h1,h2,h3⟩
      refine ⟨h1,h3,?_,?_⟩ <;> simp [h1,h2,h3]
  let v : Fin 4 → ℝ := ![1,0,0,0]
  have hv : v ∈ K := (hK v).mpr (by simp [v])
  have hspan : K = ℝ ∙ v := by
    apply le_antisymm
    · intro y hy
      obtain ⟨h1,h2,h3⟩ := (hK y).mp hy
      apply Submodule.mem_span_singleton.mpr
      refine ⟨y 0,?_⟩
      funext i
      fin_cases i <;> simp [v,h1,h2,h3]
    · exact (Submodule.span_singleton_le_iff_mem v K).mpr hv
  have hv0 : v ≠ 0 := by
    intro hh
    have he := congrFun hh 0
    norm_num [v] at he
  change Module.finrank ℝ K = 1
  rw [hspan]
  exact finrank_span_singleton hv0
#print axioms Paper7B4Analytic.opposite_unit_delta_one

theorem opposite_zero_multiplicity (a c b d : ℕ) (ha : 0 < a) (hc : 0 < c) :
    mult (SG 4 (oppositeP a c) (oppositeQ b d)) 0 = a+c := by
  have hK : Kp 4 (oppositeP a c) = {0,2} := by
    ext i
    simp only [Kp, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · change (0 < a) ↔ ((0 : Fin 4) = 0 ∨ (0 : Fin 4) = 2)
      exact ⟨fun _ => Or.inl rfl, fun _ => ha⟩
    · change (0 < (0 : ℕ)) ↔ ((1 : Fin 4) = 0 ∨ (1 : Fin 4) = 2)
      decide
    · change (0 < c) ↔ ((2 : Fin 4) = 0 ∨ (2 : Fin 4) = 2)
      exact ⟨fun _ => Or.inr rfl, fun _ => hc⟩
    · change (0 < (0 : ℕ)) ↔ ((3 : Fin 4) = 0 ∨ (3 : Fin 4) = 2)
      decide
  have hdelta : delta0 4 (oppositeP a c) = 2 := by
    rw [delta0,hK]
    decide +kernel
  have he := (Paper7Lemma22.check_Lemma22 4 (oppositeP a c) (oppositeQ b d) (by decide)).2.1
  rw [hK,hdelta] at he
  norm_num [oppositeP,Fin.sum_univ_four] at he
  omega
#print axioms Paper7B4Analytic.opposite_zero_multiplicity

theorem opposite_positive_card_offset (a c b d : ℕ) (ha : 0 < a) (hc : 0 < c)
    (hG : IsIntegralGraph (SG 4 (oppositeP a c) (oppositeQ b d))) :
    (Bplus (SG 4 (oppositeP a c) (oppositeQ b d))).card+
      deltaE 4 (oppositeP a c) (oppositeQ b d) 1 = 2+(Kq 4 (oppositeQ b d)).card := by
  let p := oppositeP a c
  let q := oppositeQ b d
  have hzero : mult (SG 4 p q) 0 = a+c := opposite_zero_multiplicity a c b d ha hc
  have hunit := ((Paper7Lemma22.check_Lemma22 4 p q (by decide)).2.2.1 1 (Or.inl rfl)).1
  have hs := Paper7Admissible.lemma24_counting_even 4 p q (by decide) hG (by decide)
  have hcard := Paper7Counting.symmetric_spectrum_card (SG 4 p q) hG hs.1
  have hpSum : (∑ i, p i) = a+c := by
    rw [Fin.sum_univ_four]
    change a+0+c+0 = a+c
    omega
  have hqSum : (∑ i, q i) = b+d := by
    rw [Fin.sum_univ_four]
    change 0+b+0+d = b+d
    omega
  have hn : nOf 4 p q = 4+(a+c)+2*(b+d) := by
    unfold nOf
    rw [hpSum,hqSum]
  change order 4 (pq 4 p q) = _ at hcard
  rw [Paper7Setup.sg_order,← hs.1 1,hzero,hn] at hcard
  rw [hqSum] at hunit
  change (Bplus (SG 4 p q)).card+deltaE 4 p q 1 = 2+(Kq 4 q).card
  omega
#print axioms Paper7B4Analytic.opposite_positive_card_offset

end Paper7B4Analytic
