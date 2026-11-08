import Research.Backfill.Paper1.EqualParityMax

/-! Full frozen Section8OddSet, for all equal-parity exponent pairs.
No maximality assertion for the unrestricted conjecture is made here.
Acceptance is recorded separately from the proof source. -/
set_option autoImplicit false
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace OddSet

lemma last_le_power {x : ℝ} (hx : 2 < x) (a : ℕ) : Tv x a sgnv a ≤ x^a := by
  have hx0 : 0 < x := by linarith
  have h := Zp_abs_le (by linarith : 1 ≤ x) (isSign_abs_le (sgnv_isSign a)) 0 (Nat.zero_le a)
  have hz : Zp x a sgnv 0 ≤ 1 := le_trans (le_abs_self _) h
  rw [Tv_last hx0.ne']
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hz (pow_pos hx0 a).le

lemma two_negative {p q : ℝ} (hp : 2 < p) (hq : 2 < q) (a b : ℕ)
    (X : ℕ → ℕ → ℝ)
    (hY : ∀ i ≤ a, ∀ j ≤ b, 2*X i j-1 = -(sgnv i*sgnv j)) :
    2*L1mat p q a b X = p^a*q^b + L1 p a sgnv*L1 q b sgnv -
      2*Tv p a sgnv a*Tv q b sgnv b := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hM : ∀ u v, Mentry p q a b (fun i j => 2*X i j-1) u v =
      -(Tv p a sgnv u*Tv q b sgnv v) := by
    intro u v
    have hprod : ∀ i ≤ a, ∀ j ≤ b, 2*X i j-1 = ((-1:ℝ)*sgnv i)*sgnv j := by
      intro i hi j hj
      rw [hY i hi j hj]
      ring
    rw [Mentry_prod p q a b hprod, Tv_smul]
    ring
  have hpp := Tv_sgnv_last_pos hp a
  have hqq := Tv_sgnv_last_pos hq b
  have hle : Tv p a sgnv a*Tv q b sgnv b ≤ p^a*q^b :=
    mul_le_mul (last_le_power hp a) (last_le_power hq b) hqq.le (pow_pos hp0 a).le
  have ht : ∀ u ∈ range (a+1), ∀ v ∈ range (b+1),
      |Mentry p q a b (fun i j => 2*X i j-1) u v + Mentry p q a b (fun _ _ => 1) u v| =
      |Tv p a sgnv u*Tv q b sgnv v| +
        (if a=u ∧ b=v then p^a*q^b-2*Tv p a sgnv a*Tv q b sgnv b else 0) := by
    intro u hu v hv
    rw [hM, Mentry_ones hp0.ne' hq0.ne' a b (by simpa using Nat.le_of_lt_succ (mem_range.mp hu))
      (by simpa using Nat.le_of_lt_succ (mem_range.mp hv))]
    split_ifs with h
    · obtain ⟨rfl,rfl⟩ := h
      rw [abs_of_nonneg (by linarith), abs_of_pos (mul_pos hpp hqq)]
      ring
    · simp only [add_zero, abs_neg]
  rw [two_L1mat, Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun v hv => ht u hu v hv))]
  simp only [Finset.sum_add_distrib]
  rw [double_sum_ite (F := fun _ _ => p^a*q^b-2*Tv p a sgnv a*Tv q b sgnv b) (by omega) (by omega)]
  have hprod : (∑ u ∈ range (a+1), ∑ v ∈ range (b+1), |Tv p a sgnv u*Tv q b sgnv v|) =
      L1 p a sgnv*L1 q b sgnv := by
    unfold L1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    exact abs_mul _ _
  rw [hprod]
  ring

lemma odd_sign {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∀ i ≤ a, ∀ j ≤ b,
      2*(if p^i*q^j ∈ Challenge.oddSet p q a b then (1:ℝ) else 0)-1 = -(sgnv i*sgnv j) := by
  intro i hi j hj
  change 2*(if p^i*q^j ∈ ICGEqualParity.DantiPQ p q a b then (1:ℝ) else 0)-1 = _
  rw [sgnv_mul]
  rcases Nat.even_or_odd (i+j) with he | ho
  · rw [ite_eq_left he, ite_eq_right (fun h => (Nat.not_even_iff_odd.mpr
      ((ICGEqualParity.pq_mem_DantiPQ hp hq hpq hi hj).mp h)) he)]
    norm_num
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr ho),
      ite_eq_left ((ICGEqualParity.pq_mem_DantiPQ hp hq hpq hi hj).mpr ho)]
    norm_num

lemma value {p q a b : ℕ} (hpq : Challenge.DistinctOddPrimes p q)
    (hab : Even (a+b)) :
    Challenge.energy (p^a*q^b) (Challenge.oddSet p q a b) =
      (((p^a*q^b:ℕ):ℝ)+Challenge.dClosed a p*Challenge.dClosed b q)/2-
        Challenge.deltaK a p*Challenge.deltaK b q := by
  obtain ⟨hp,hq,hne,hpo,hqo⟩ := hpq
  have hpR : (2:ℝ) < p := by exact_mod_cast (show 2 < p from lt_of_lt_of_le (by omega) (hp.odd_iff.mp hpo))
  have hqR : (2:ℝ) < q := by exact_mod_cast (show 2 < q from lt_of_lt_of_le (by omega) (hq.odd_iff.mp hqo))
  have hd := ICGEqualParity.DantiPQ_subset hp hq hne hab
  change Challenge.oddSet p q a b ⊆ (p^a*q^b).properDivisors at hd
  rw [OppositeParity.energy_eq_matrix_of_subset hd, energy_icgAdj_pq p q a b hp hq hne]
  have h := two_negative hpR hqR a b
    (fun i j => if p^i*q^j ∈ Challenge.oddSet p q a b then (1:ℝ) else 0) (odd_sign hp hq hne)
  rw [EqualParityMax.L1_eq_dClosed hpR, EqualParityMax.L1_eq_dClosed hqR,
    EqualParityMax.Tv_last_eq_deltaK hpR, EqualParityMax.Tv_last_eq_deltaK hqR] at h
  push_cast
  linarith

lemma strict_bound {p q a b : ℕ} (hpq : Challenge.DistinctOddPrimes p q)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : Even (a+b)) (D : Finset ℕ)
    (hD : Challenge.IsConnSet (p^a*q^b) D) :
    Challenge.energy (p^a*q^b) D < (((p^a*q^b:ℕ):ℝ)+
      Challenge.dClosed a p*Challenge.dClosed b q)/2 := by
  obtain ⟨hp,hq,hne,hpo,hqo⟩ := hpq
  have hp3 := hp.odd_iff.mp hpo
  have hq3 := hq.odd_iff.mp hqo
  have hpR : (2:ℝ) < p := by exact_mod_cast (show 2 < p by omega)
  have hqR : (2:ℝ) < q := by exact_mod_cast (show 2 < q by omega)
  have hp0 : (0:ℝ) < p := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hmin : (3:ℝ) ≤ min (p:ℝ) q := le_min (by exact_mod_cast hp3) (by exact_mod_cast hq3)
  have hmax : (5:ℝ) ≤ max (p:ℝ) q := by
    have hp4 : p ≠ 4 := by intro he; subst p; norm_num at hp
    have hq4 : q ≠ 4 := by intro he; subst q; norm_num at hq
    have hm : 5 ≤ max p q := by omega
    exact_mod_cast hm
  let X : ℕ → ℕ → ℝ := fun i j => if p^i*q^j ∈ D then 1 else 0
  let Y : ℕ → ℕ → ℝ := fun i j => 2*X i j-1
  have hY : Challenge.IsSignMat a b Y := by
    intro i hi j hj
    dsimp [Y,X]
    split_ifs <;> norm_num
  have H := check_Remark13 (p:ℝ) (q:ℝ) hmin hmax a b ha hb Y hY
  rw [PathAndSign.l1Mat_triple_eq_L1mat, Additional.dNorm_eq_L1, Additional.dNorm_eq_L1] at H
  have hup := two_L1mat_le hp0 hq0 a b X
  have he : Challenge.energy (p^a*q^b) D = L1mat p q a b X := by
    rw [OppositeParity.energy_eq_matrix_of_subset hD.2, energy_icgAdj_pq p q a b hp hq hne]
  rw [he, ← EqualParityMax.L1_eq_dClosed hpR, ← EqualParityMax.L1_eq_dClosed hqR]
  push_cast
  by_contra hnot
  have hge := not_lt.mp hnot
  have hnorm : L1mat p q a b Y = L1 p a sgnv*L1 q b sgnv := by
    change 2*L1mat p q a b X ≤ L1mat p q a b Y + (p:ℝ)^a*(q:ℝ)^b at hup
    linarith [H.1]
  rcases H.2.mp hnorm with hpos | hneg
  · have hn : p^a*q^b ∉ D := fun hm => Nat.self_notMem_properDivisors (hD.2 hm)
    have hc := hpos a le_rfl b le_rfl
    have hs : Challenge.sAlt a*Challenge.sAlt b = (1:ℝ) := by
      unfold Challenge.sAlt
      rw [← pow_add, hab.neg_one_pow]
    simp [Y,X,hn,hs] at hc
    norm_num at hc
  · have hneg' : ∀ i ≤ a, ∀ j ≤ b, 2*X i j-1 = -(sgnv i*sgnv j) := hneg
    have hv := two_negative hpR hqR a b X hneg'
    have hd : 0 < Tv p a sgnv a*Tv q b sgnv b :=
      mul_pos (Tv_sgnv_last_pos hpR a) (Tv_sgnv_last_pos hqR b)
    nlinarith only [hv,hge,hd]

end OddSet

theorem check_Section8OddSet : Challenge.Section8OddSet := by
  intro p q a b hpq ha hb hab
  refine ⟨⟨EqualParityMax.oddSet_nonempty p q a b ha, ?_⟩, OddSet.value hpq hab, ?_⟩
  · exact ICGEqualParity.DantiPQ_subset hpq.1 hpq.2.1 hpq.2.2.1 hab
  · exact OddSet.strict_bound hpq ha hb hab

#print axioms check_Section8OddSet
end CodexPaper1
