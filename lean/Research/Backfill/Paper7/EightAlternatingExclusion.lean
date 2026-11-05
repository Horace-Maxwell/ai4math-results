import Research.Backfill.Paper7.EightAlternatingTransfer
import Research.Backfill.Paper7.EightCycleSquarePacking
import Research.Backfill.Paper7.DihedralOrbitBasics

/-! NEW SOURCE ONLY. Complete exclusion of the pure-P branch whose support is
contained in one parity class. The unrestricted eight-cycle remains open. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem eight_alternating_unit_absent (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    1 ∉ spec (SG 8 p (fun _ => 0)) := by
  intro hunit
  have h15 := eight_alternating_unit_small p ho hunit
  have hc := (eight_big_card_bounds p (fun _ => 0) (by simpa using hp) hn hG).1
  have ht := Paper7Admissible.square_floor_sum (Bplus (SG 8 p (fun _ => 0)))
    (Paper7Admissible.bplus_integral_entries 8 p (fun _ => 0) hG)
  have hcount := Paper7Admissible.bplus_count_le_two 8 p (fun _ => 0) (by decide) 2
  have hs := (Paper7Admissible.lemma24_counting_even 8 p (fun _ => 0)
    (by decide) hG (by decide)).2.1
  have hcR : (3 : ℝ) ≤ (Bplus (SG 8 p (fun _ => 0))).card := by exact_mod_cast hc
  have hcountR : ((Bplus (SG 8 p (fun _ => 0))).count 2 : ℝ) ≤ 2 := by exact_mod_cast hcount
  have hnR : (nOf 8 p (fun _ => 0) : ℝ) ≤ 15 := by exact_mod_cast h15
  have hmR : (0 : ℝ) ≤ mult (SG 8 p (fun _ => 0)) 1 := Nat.cast_nonneg _
  change 9*((Bplus (SG 8 p (fun _ => 0))).card : ℝ) ≤
    S2 (SG 8 p (fun _ => 0))+5*((Bplus (SG 8 p (fun _ => 0))).count 2 : ℝ) at ht
  linarith only [ht,hs,hcR,hcountR,hnR,hmR]
#print axioms Paper7EightCycle.eight_alternating_unit_absent

theorem eight_alternating_spectrum_data (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    (Bplus (SG 8 p (fun _ => 0))).card = 4 ∧
      mult (SG 8 p (fun _ => 0)) 1 = 0 ∧
      S2 (SG 8 p (fun _ => 0)) = nOf 8 p (fun _ => 0) := by
  have hm : mult (SG 8 p (fun _ => 0)) 1 = 0 :=
    Multiset.count_eq_zero.mpr (eight_alternating_unit_absent p ho hp hn hG)
  have hK : (Kp 8 p).Nonempty := by
    by_contra hh
    have hz := Paper7Rank.support_sum_zero 8 p (Finset.not_nonempty_iff_eq_empty.mp hh)
    omega
  have hd := Paper7Rank.delta0_le_card_of_nonempty 8 p hK
  have hr := Paper7MainReduction.qzero_positive_rank_balance 8 p (by decide) (by decide) hG
  have hc := (eight_big_card_bounds p (fun _ => 0) (by simpa using hp) hn hG).2
  refine ⟨by omega,hm,?_⟩
  have hs := (Paper7Admissible.lemma24_counting_even 8 p (fun _ => 0)
    (by decide) hG (by decide)).2.1
  simpa only [hm,Nat.cast_zero,sub_zero] using hs
#print axioms Paper7EightCycle.eight_alternating_spectrum_data

theorem eight_alternating_repeated_order (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) (x : ℝ) (hx : 2 ≤ x)
    (hm : (Bplus (SG 8 p (fun _ => 0))).count x = 2) :
    (nOf 8 p (fun _ => 0) : ℝ) = 4*x^2 := by
  have hmult : mult (SG 8 p (fun _ => 0)) x = 2 := by
    simpa only [Bplus,mult,Multiset.count_filter,hx,ite_true] using hm
  have hid := ((Paper7Lemma22.check_Lemma22 8 p (fun _ => 0) (by decide)).1 x
    (by linarith) (by linarith) (by linarith)).2.2.1.mp hmult
  exact eight_alternating_identity_order p ho x (by linarith) hid
#print axioms Paper7EightCycle.eight_alternating_repeated_order

theorem eight_alternating_small_counts (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    (Bplus (SG 8 p (fun _ => 0))).count 2 ≤ 1 ∧
      (Bplus (SG 8 p (fun _ => 0))).count 3 ≤ 1 ∧
      (Bplus (SG 8 p (fun _ => 0))).count 4 ≤ 1 := by
  obtain ⟨hc,_hu,hS⟩ := eight_alternating_spectrum_data p ho hp hn hG
  have hints := Paper7Admissible.bplus_integral_entries 8 p (fun _ => 0) hG
  have hcounts := Paper7Admissible.bplus_count_le_two 8 p (fun _ => 0) (by decide)
  have hnR : (nOf 8 p (fun _ => 0) : ℝ) ≤ 41 := by exact_mod_cast hn
  have h2 : (Bplus (SG 8 p (fun _ => 0))).count 2 ≤ 1 := by
    by_contra hh
    have heq : (Bplus (SG 8 p (fun _ => 0))).count 2 = 2 := by have := hcounts 2; omega
    have hn16 := eight_alternating_repeated_order p ho 2 (by norm_num) heq
    have ht := Paper7Admissible.square_floor_sum (Bplus (SG 8 p (fun _ => 0))) hints
    change 9*((Bplus (SG 8 p (fun _ => 0))).card : ℝ) ≤
      S2 (SG 8 p (fun _ => 0))+5*((Bplus (SG 8 p (fun _ => 0))).count 2 : ℝ) at ht
    rw [hc,heq,hS,hn16] at ht
    norm_num at ht
  have h3 : (Bplus (SG 8 p (fun _ => 0))).count 3 ≤ 1 := by
    by_contra hh
    have heq : (Bplus (SG 8 p (fun _ => 0))).count 3 = 2 := by have := hcounts 3; omega
    have hn36 := eight_alternating_repeated_order p ho 3 (by norm_num) heq
    have ht := square_floor_sixteen (Bplus (SG 8 p (fun _ => 0))) hints
    change 16*((Bplus (SG 8 p (fun _ => 0))).card : ℝ) ≤ S2 (SG 8 p (fun _ => 0))+
      12*((Bplus (SG 8 p (fun _ => 0))).count 2 : ℝ)+
      7*((Bplus (SG 8 p (fun _ => 0))).count 3 : ℝ) at ht
    have h2R : ((Bplus (SG 8 p (fun _ => 0))).count 2 : ℝ) ≤ 1 := by exact_mod_cast h2
    rw [hc,heq,hS,hn36] at ht
    norm_num at ht
    linarith only [ht,h2R]
  have h4 : (Bplus (SG 8 p (fun _ => 0))).count 4 ≤ 1 := by
    by_contra hh
    have heq : (Bplus (SG 8 p (fun _ => 0))).count 4 = 2 := by have := hcounts 4; omega
    have hn64 := eight_alternating_repeated_order p ho 4 (by norm_num) heq
    norm_num at hn64
    linarith only [hn64,hnR]
  exact ⟨h2,h3,h4⟩
#print axioms Paper7EightCycle.eight_alternating_small_counts

theorem eight_alternating_nonintegral (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) : ¬ IsIntegralGraph (SG 8 p (fun _ => 0)) := by
  intro hG
  obtain ⟨hc,_hu,hS⟩ := eight_alternating_spectrum_data p ho hp hn hG
  obtain ⟨h2,h3,h4⟩ := eight_alternating_small_counts p ho hp hn hG
  have ht := square_floor_twenty_five (Bplus (SG 8 p (fun _ => 0)))
    (Paper7Admissible.bplus_integral_entries 8 p (fun _ => 0) hG)
  change 25*((Bplus (SG 8 p (fun _ => 0))).card : ℝ) ≤ S2 (SG 8 p (fun _ => 0))+
    21*((Bplus (SG 8 p (fun _ => 0))).count 2 : ℝ)+
    16*((Bplus (SG 8 p (fun _ => 0))).count 3 : ℝ)+
    9*((Bplus (SG 8 p (fun _ => 0))).count 4 : ℝ) at ht
  have h2R : ((Bplus (SG 8 p (fun _ => 0))).count 2 : ℝ) ≤ 1 := by exact_mod_cast h2
  have h3R : ((Bplus (SG 8 p (fun _ => 0))).count 3 : ℝ) ≤ 1 := by exact_mod_cast h3
  have h4R : ((Bplus (SG 8 p (fun _ => 0))).count 4 : ℝ) ≤ 1 := by exact_mod_cast h4
  have hnR : (nOf 8 p (fun _ => 0) : ℝ) ≤ 41 := by exact_mod_cast hn
  rw [hc,hS] at ht
  norm_num at ht
  linarith only [ht,h2R,h3R,h4R,hnR]
#print axioms Paper7EightCycle.eight_alternating_nonintegral

theorem eight_qzero_saturated_nonintegral (p : Fin 8 → ℕ)
    (hp : 0 < ∑ i, p i) (hn : nOf 8 p (fun _ => 0) ≤ 41)
    (hd : delta0 8 p = (Kp 8 p).card) : ¬ IsIntegralGraph (SG 8 p (fun _ => 0)) := by
  intro hG
  obtain ⟨k,hk⟩ : ∃ k : Fin 8, 0 < p k := by
    by_contra hh
    push Not at hh
    have hz : ∑ i, p i = 0 := Finset.sum_eq_zero (fun i _ => by have := hh i; omega)
    omega
  let σ : Fin 8 → Fin 8 := fun i => i+k
  have hσ : IsDihedral 8 σ := by refine ⟨k,Or.inl ?_⟩; intro i; rfl
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 8 p (fun _ => 0)
    (p ∘ σ) (fun _ => 0) (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hsum : ∑ i, (p ∘ σ) i = ∑ i, p i :=
    (Paper7PruningCanonical.dihedral_bijective 8 (by decide) σ hσ).sum_comp p
  have hp' : 0 < ∑ i, (p ∘ σ) i := by rw [hsum]; exact hp
  have hn' : nOf 8 (p ∘ σ) (fun _ => 0) ≤ 41 := by simpa only [nOf,hsum] using hn
  have ho' : ∀ i : Fin 8, Odd i.val → (p ∘ σ) i = 0 :=
    eight_saturated_rotated_odd_zero p hd k hk
  exact eight_alternating_nonintegral (p ∘ σ) ho' hp' hn' hI
#print axioms Paper7EightCycle.eight_qzero_saturated_nonintegral

end Paper7EightCycle
