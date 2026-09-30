import Research.Backfill.Paper8.Challenge

/-!
# Paper 8, Section 3: the secular polynomial `R`

Evaluation of `R = secular m` at real points; `R` is monic of degree `|B|` (`secular_monic`); the
value `R(b) = -k_b ∏_{b' ≠ b} (b - b')` at `b ∈ B` and its sign; the factorisation
`R(t) = ∏ (t - b) · (1 - F(t))` for `t ∉ B`; and `R(t) > 0` for `t > b* + |m|` (item U1).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Polynomial

namespace P8Spec

/-- `R(t)` for real `t`, written out. -/
theorem aeval_secular (m : Multiset ℕ) (t : ℝ) :
    aeval t (secular m) = ∏ b ∈ Bset m, (t - (b : ℝ)) -
      ∑ b ∈ Bset m, (kb m b : ℝ) * ∏ b' ∈ (Bset m).erase b, (t - (b' : ℝ)) := by
  simp [secular]

/-- Evaluating the real image of `R` is the same as `aeval`. -/
theorem eval_map_secular (m : Multiset ℕ) (t : ℝ) :
    ((secular m).map (Int.castRingHom ℝ)).eval t = aeval t (secular m) := by
  rw [← algebraMap_int_eq, eval_map_algebraMap]

/-- `R` is monic of degree `r = |B|` (for a nonempty multiset). -/
theorem secular_monic (m : Multiset ℕ) (hm : m ≠ 0) :
    (secular m).Monic ∧ (secular m).natDegree = (Bset m).card := by
  have hne : (Bset m).Nonempty := Multiset.toFinset_nonempty.2 hm
  have hPm : (∏ b ∈ Bset m, (X - C (b : ℤ))).Monic :=
    monic_prod_of_monic _ _ (fun b _ => monic_X_sub_C _)
  have hPd : (∏ b ∈ Bset m, (X - C (b : ℤ))).natDegree = (Bset m).card := by
    rw [natDegree_prod_of_monic _ _ (fun b _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  have hQd : (∑ b ∈ Bset m, C (kb m b : ℤ) * ∏ b' ∈ (Bset m).erase b, (X - C (b' : ℤ))).natDegree
      ≤ (Bset m).card - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro b hb
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_prod_of_monic _ _ (fun b _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_erase_of_mem hb, le_refl]
  have hlt : (∑ b ∈ Bset m, C (kb m b : ℤ) * ∏ b' ∈ (Bset m).erase b, (X - C (b' : ℤ))).natDegree
      < (∏ b ∈ Bset m, (X - C (b : ℤ))).natDegree := by
    rw [hPd]
    have := hne.card_pos
    omega
  refine ⟨hPm.sub_of_left (degree_lt_degree hlt), ?_⟩
  rw [secular, natDegree_sub_eq_left_of_natDegree_lt hlt, hPd]

/-- `k_b ≥ 1` for `b ∈ B`. -/
theorem kb_pos_of_mem (m : Multiset ℕ) (b : ℕ) (hb : b ∈ Bset m) : 0 < kb m b :=
  Multiset.count_pos.2 (Multiset.mem_toFinset.1 hb)

/-- `∑_{b ∈ B} k_b = |m|`. -/
theorem sum_kb (m : Multiset ℕ) : ∑ b ∈ Bset m, (kb m b : ℝ) = (Multiset.card m : ℝ) := by
  rw [← Multiset.toFinset_sum_count_eq m, Nat.cast_sum]
  rfl

/-- `R(b) = -k_b ∏_{b' ∈ B, b' ≠ b} (b - b')` for `b ∈ B`. -/
theorem aeval_secular_of_mem (m : Multiset ℕ) (b : ℕ) (hb : b ∈ Bset m) :
    aeval (b : ℝ) (secular m) =
      -((kb m b : ℝ) * ∏ b' ∈ (Bset m).erase b, ((b : ℝ) - (b' : ℝ))) := by
  rw [aeval_secular]
  have h1 : ∏ c ∈ Bset m, ((b : ℝ) - (c : ℝ)) = 0 := Finset.prod_eq_zero hb (by simp)
  rw [h1, Finset.sum_eq_single b]
  · ring
  · intro c _ hcb
    have : ∏ b' ∈ (Bset m).erase c, ((b : ℝ) - (b' : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hcb, hb⟩) (by simp)
    rw [this, mul_zero]
  · intro h
    exact absurd hb h

/-- Sign of `R(b)` for `b ∈ B`: `(-1)^N R(b) < 0`, where `N` is the number of elements of `B`
larger than `b`. -/
theorem sign_aeval_secular_of_mem (m : Multiset ℕ) (b : ℕ) (hb : b ∈ Bset m) :
    (-1 : ℝ) ^ ((Bset m).filter (fun c => b < c)).card * aeval (b : ℝ) (secular m) < 0 := by
  rw [aeval_secular_of_mem m b hb]
  have hk : (0 : ℝ) < kb m b := by exact_mod_cast kb_pos_of_mem m b hb
  have hfac : ∀ c ∈ (Bset m).erase b,
      ((b : ℝ) - (c : ℝ)) = (if b < c then -1 else 1) * |(b : ℝ) - (c : ℝ)| := by
    intro c _
    split_ifs with h
    · have : (b : ℝ) < c := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]
      ring
    · have : (c : ℝ) ≤ b := by exact_mod_cast not_lt.1 h
      rw [abs_of_nonneg (by linarith)]
      ring
  have hfilt : ((Bset m).erase b).filter (fun c => b < c) = (Bset m).filter (fun c => b < c) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hc⟩, hlt⟩
      exact ⟨hc, hlt⟩
    · rintro ⟨hc, hlt⟩
      exact ⟨⟨by omega, hc⟩, hlt⟩
  have hprod : ∏ c ∈ (Bset m).erase b, ((b : ℝ) - (c : ℝ)) =
      (-1) ^ ((Bset m).filter (fun c => b < c)).card *
        ∏ c ∈ (Bset m).erase b, |(b : ℝ) - (c : ℝ)| := by
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one, hfilt]
  have hpos : 0 < ∏ c ∈ (Bset m).erase b, |(b : ℝ) - (c : ℝ)| := by
    apply Finset.prod_pos
    intro c hc
    rw [abs_pos, sub_ne_zero]
    exact_mod_cast (Finset.ne_of_mem_erase hc).symm
  rw [hprod]
  have hsq : ((-1 : ℝ) ^ ((Bset m).filter (fun c => b < c)).card) *
      ((-1) ^ ((Bset m).filter (fun c => b < c)).card) = 1 := by
    rw [← mul_pow]
    norm_num
  have hkp := mul_pos hk hpos
  linear_combination (-((kb m b : ℝ) * ∏ c ∈ (Bset m).erase b, |(b : ℝ) - (c : ℝ)|)) * hsq + hkp

/-- `R(b) ≠ 0` for `b ∈ B`. -/
theorem aeval_secular_ne_zero_of_mem (m : Multiset ℕ) (b : ℕ) (hb : b ∈ Bset m) :
    aeval (b : ℝ) (secular m) ≠ 0 := by
  intro h
  have := sign_aeval_secular_of_mem m b hb
  rw [h, mul_zero] at this
  exact lt_irrefl _ this

/-- For `t ∉ B`: `R(t) = ∏_{b ∈ B} (t - b) · (1 - ∑_{b ∈ B} k_b/(t - b))`. -/
theorem aeval_secular_eq_mul (m : Multiset ℕ) (t : ℝ) (ht : ∀ b ∈ Bset m, t ≠ (b : ℝ)) :
    aeval t (secular m) = (∏ b ∈ Bset m, (t - (b : ℝ))) *
      (1 - ∑ b ∈ Bset m, (kb m b : ℝ) / (t - (b : ℝ))) := by
  rw [aeval_secular, mul_sub, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hne : t - (b : ℝ) ≠ 0 := sub_ne_zero.2 (ht b hb)
  rw [← Finset.mul_prod_erase _ _ hb]
  field_simp

/-- Item U1: `R(t) > 0` for `t > b* + |m|`. -/
theorem aeval_secular_pos (m : Multiset ℕ) (t : ℝ)
    (ht : (bstar m : ℝ) + (Multiset.card m : ℝ) < t) : 0 < aeval t (secular m) := by
  have hb : ∀ b ∈ Bset m, (b : ℝ) ≤ bstar m := by
    intro b hb
    exact_mod_cast (Finset.le_sup (f := id) hb)
  have hcard : (0 : ℝ) ≤ Multiset.card m := Nat.cast_nonneg _
  have hts : 0 < t - (bstar m : ℝ) := by linarith
  have htb : ∀ b ∈ Bset m, 0 < t - (b : ℝ) := by
    intro b hb'
    have := hb b hb'
    linarith
  rw [aeval_secular_eq_mul m t (fun b hb' => ne_of_gt (sub_pos.1 (htb b hb')))]
  apply mul_pos (Finset.prod_pos htb)
  have hle : ∑ b ∈ Bset m, (kb m b : ℝ) / (t - (b : ℝ)) ≤
      ∑ b ∈ Bset m, (kb m b : ℝ) / (t - (bstar m : ℝ)) := by
    apply Finset.sum_le_sum
    intro b hb'
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hts
    linarith [hb b hb']
  rw [← Finset.sum_div, sum_kb] at hle
  have hlt : (Multiset.card m : ℝ) / (t - (bstar m : ℝ)) < 1 := by
    rw [div_lt_one hts]
    linarith
  linarith

end P8Spec
