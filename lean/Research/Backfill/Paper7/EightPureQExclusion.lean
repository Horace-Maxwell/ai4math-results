import Research.Backfill.Paper7.EightUnitResidual

/-! NEW SOURCE ONLY. Complete pure-Q exclusion for the original eight-cycle.
The strict unit-nullity bound follows from an explicit inverse row. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem cycle_eight_unit_green (y : Fin 8 → ℝ) (k : Fin 8) :
    3*y k = unitResidual (fun _ => 0) y k+2*unitResidual (fun _ => 0) y (k+1)+
      unitResidual (fun _ => 0) y (k+2)-unitResidual (fun _ => 0) y (k+3)-
      2*unitResidual (fun _ => 0) y (k+4)-unitResidual (fun _ => 0) y (k+5)+
      unitResidual (fun _ => 0) y (k+6)+2*unitResidual (fun _ => 0) y (k+7) := by
  have hp (i : Fin 8) : prv 8 i = i-1 := by fin_cases i <;> rfl
  have hn (i : Fin 8) : nxt 8 i = i+1 := by fin_cases i <;> rfl
  have hneg : (-1 : Fin 8) = 7 := by decide
  fin_cases k <;> norm_num [unitResidual_apply,hp,hn] <;> rw [hneg] <;> ring
#print axioms Paper7EightCycle.cycle_eight_unit_green

theorem cycle_eight_unit_injective : Function.Injective (unitResidual (fun _ => 0)) := by
  intro y z he
  funext k
  have hy := cycle_eight_unit_green y k
  have hz := cycle_eight_unit_green z k
  rw [he] at hy
  linarith only [hy,hz]
#print axioms Paper7EightCycle.cycle_eight_unit_injective

theorem pure_q_residual_injective (q : Fin 8 → ℕ) :
    Function.Injective (supportResidualMap (fun _ => 0) q) := by
  intro y z he
  apply Subtype.ext
  apply cycle_eight_unit_injective
  funext i
  by_cases hi : i ∈ Kq 8 q
  · exact congrFun he ⟨i,hi⟩
  · rw [unitResidual_zero_off_support _ q y.1 y.2 i hi,
      unitResidual_zero_off_support _ q z.1 z.2 i hi]
#print axioms Paper7EightCycle.pure_q_residual_injective

theorem pure_q_unit_delta_strict (q : Fin 8 → ℕ) (hK : (Kq 8 q).Nonempty) :
    deltaE 8 (fun _ => 0) q 1 < (Kq 8 q).card := by
  have hle := Paper7Lemma22Gaps.deltaE_nonempty_bound 8 (fun _ => 0) q 1 hK
  by_contra hh
  have heq : deltaE 8 (fun _ => 0) q 1 = (Kq 8 q).card := by omega
  have hdim : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (Wmat 8 (fun _ => 0) q 1))) =
      Module.finrank ℝ ({i : Fin 8 // i ∈ Kq 8 q} → ℝ) := by
    simpa only [deltaE,Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using heq
  have hsurj : Function.Surjective (supportResidualMap (fun _ => 0) q) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (pure_q_residual_injective q)
  obtain ⟨k,hk⟩ := hK
  let v : {i : Fin 8 // i ∈ Kq 8 q} → ℝ := fun i => if i.1 = k then 1 else 0
  obtain ⟨y,hy⟩ := hsurj v
  have hr (i : Fin 8) : unitResidual (fun _ => 0) y.1 i = if i = k then 1 else 0 := by
    by_cases hi : i ∈ Kq 8 q
    · exact congrFun hy ⟨i,hi⟩
    · have hik : i ≠ k := by intro he; subst i; exact hi hk
      rw [unitResidual_zero_off_support _ q y.1 y.2 i hi,ite_eq_right hik]
  have hz := Paper7Lemma22Gaps.kernel_zero_on_support 8 (fun _ => 0) q 1 y.1 y.2 k hk
  have hg := cycle_eight_unit_green y.1 k
  rw [hz] at hg
  simp only [hr] at hg
  fin_cases k <;> norm_num at hg
#print axioms Paper7EightCycle.pure_q_unit_delta_strict

theorem eight_pure_q_nonintegral (q : Fin 8 → ℕ) (hq : 0 < ∑ i, q i)
    (hn : nOf 8 (fun _ => 0) q ≤ 41) : ¬ IsIntegralGraph (SG 8 (fun _ => 0) q) := by
  intro hG
  have hK : (Kq 8 q).Nonempty := by
    by_contra hh
    have hz := Paper7Rank.support_sum_zero 8 q (Finset.not_nonempty_iff_eq_empty.mp hh)
    omega
  have hd := pure_q_unit_delta_strict q hK
  have hkp : Kp 8 (fun _ => 0) = ∅ := by simp [Kp]
  have hzero : delta0 8 (fun _ => 0) = 2 := by norm_num [delta0,hkp]
  have he := Paper7Admissible.lemma24_counting_even 8 (fun _ => 0) q (by decide) hG (by decide)
  have hsym := he.1 1
  have hplus := ((Paper7Lemma22.check_Lemma22 8 (fun _ => 0) q (by decide)).2.2.1 1 (Or.inl rfl)).1
  have hminus := ((Paper7Lemma22.check_Lemma22 8 (fun _ => 0) q (by decide)).2.2.1 (-1) (Or.inr rfl)).1
  have hdeq : deltaE 8 (fun _ => 0) q (-1) = deltaE 8 (fun _ => 0) q 1 := by omega
  have hr := Paper7Rank.rank_identity 8 (fun _ => 0) q (by decide) hG
  have hbc := Paper7Counting.symmetric_big_card (SG 8 (fun _ => 0) q) he.1
  have hbound := (eight_big_card_bounds (fun _ => 0) q (by simpa using hq) hn hG).2
  rw [hkp,hzero] at hr
  norm_num only [Finset.card_empty,Nat.cast_zero] at hr
  have hc : (Bplus (SG 8 (fun _ => 0) q)).card = 4 := by omega
  have hu : mult (SG 8 (fun _ => 0) q) 1+1 = ∑ i, q i := by omega
  have hq16 : (∑ i, q i) ≤ 16 := by simp only [nOf,Finset.sum_const_zero,add_zero] at hn; omega
  have huR : (mult (SG 8 (fun _ => 0) q) 1 : ℝ)+1 = (∑ i, q i : ℕ) := by exact_mod_cast hu
  have hqR : (∑ i, q i : ℕ) ≤ (16 : ℝ) := by exact_mod_cast hq16
  have hs := he.2.1
  simp only [nOf,Finset.sum_const_zero,add_zero] at hs
  push_cast at hs huR hqR
  have ht := Paper7Admissible.square_floor_sum (Bplus (SG 8 (fun _ => 0) q))
    (Paper7Admissible.bplus_integral_entries 8 (fun _ => 0) q hG)
  have hcount := Paper7Admissible.bplus_count_le_two 8 (fun _ => 0) q (by decide) 2
  have hcountR : ((Bplus (SG 8 (fun _ => 0) q)).count 2 : ℝ) ≤ 2 := by exact_mod_cast hcount
  change 9*((Bplus (SG 8 (fun _ => 0) q)).card : ℝ) ≤
    S2 (SG 8 (fun _ => 0) q)+5*((Bplus (SG 8 (fun _ => 0) q)).count 2 : ℝ) at ht
  rw [hc] at ht
  norm_num at ht
  linarith only [ht,hs,huR,hqR,hcountR]
#print axioms Paper7EightCycle.eight_pure_q_nonintegral

end Paper7EightCycle
