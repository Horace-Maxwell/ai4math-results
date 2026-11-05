import Research.Backfill.Paper7.C61OrbitTransport
import Research.Backfill.Paper7.Lemma21
import Research.Backfill.Paper7.IntegralThresholdOne
import Research.Backfill.Paper7.Lemma24SmallEven
import Research.Backfill.Paper7.CycleThreeSupportReduction

/-! Necessary bounds for every original parameter tuple. In particular the
zero q coordinate is proved before it is used to reduce the finite domain. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Classification
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem parameter_bounds (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42) :
    (∑ k, p k) + 2 * (∑ k, q k) ≤ 36 ∧
      (∀ k, p k ≤ 36) ∧ (∀ k, q k ≤ 18) := by
  have ht : (∑ k, p k) + 2 * (∑ k, q k) ≤ 36 := by
    unfold nOf at hn
    omega
  refine ⟨ht, ?_, ?_⟩
  · intro k
    have hk : p k ≤ ∑ j, p j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (p j)) (Finset.mem_univ k)
    omega
  · intro k
    have hk : q k ≤ ∑ j, q j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (q j)) (Finset.mem_univ k)
    omega
#print axioms Paper7C61Classification.parameter_bounds

theorem positive_q_support_bound (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : (Kq 6 q).card ≤ 5 := by
  have hr := (Paper7Lemma21.check_Lemma21 6 p q (by decide)).2.2.1
  rw [Paper7Lemma41.integral_Ngt_one_eq_Bplus_card (SG 6 p q) hG] at hr
  have hb := ((Paper7Admissible.lemma24_small_even_counts 6 p q (by decide)
    hG (by decide)).2 hn).1
  omega
#print axioms Paper7C61Classification.positive_q_support_bound

theorem exists_zero_q (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : ∃ k, q k = 0 := by
  by_contra h
  have hpos (k : Fin 6) : 0 < q k := Nat.pos_of_ne_zero (fun hk => h ⟨k, hk⟩)
  have hfull : Kq 6 q = Finset.univ := by
    exact Finset.filter_eq_self.mpr (fun k _ => hpos k)
  have hc := positive_q_support_bound p q hn hG
  rw [hfull, Finset.card_univ, Fintype.card_fin] at hc
  omega
#print axioms Paper7C61Classification.exists_zero_q

theorem big_card_le_ten (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : (bigEigs (SG 6 p q)).card ≤ 10 := by
  have hs := (Paper7Admissible.lemma24_counting_even 6 p q (by decide)
    hG (by decide)).1
  rw [Paper7Counting.symmetric_big_card (SG 6 p q) hs]
  have hb := ((Paper7Admissible.lemma24_small_even_counts 6 p q (by decide)
    hG (by decide)).2 hn).1
  omega
#print axioms Paper7C61Classification.big_card_le_ten

theorem delta0_full_support_zero (p : Fin 6 → ℕ) (hp : ∀ k, 0 < p k) :
    delta0 6 p = 0 := by
  have hK : Kp 6 p = Finset.univ :=
    Finset.filter_eq_self.mpr (fun k _ => hp k)
  have hne : Kp 6 p ≠ ∅ := by
    rw [hK]
    exact Finset.univ_nonempty.ne_empty
  rw [delta0, ite_eq_right hne, hK, Paper7CycleThree.evenGaps_univ_zero]
#print axioms Paper7C61Classification.delta0_full_support_zero

theorem nonempty_q_has_zero_p (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (hKq : (Kq 6 q).Nonempty) :
    ∃ k, p k = 0 := by
  by_contra h
  have hp (k : Fin 6) : 0 < p k := Nat.pos_of_ne_zero (fun hk => h ⟨k, hk⟩)
  have hKp : Kp 6 p = Finset.univ :=
    Finset.filter_eq_self.mpr (fun k _ => hp k)
  have hcard : (Kp 6 p).card = 6 := by
    rw [hKp, Finset.card_univ, Fintype.card_fin]
  have hz := delta0_full_support_zero p hp
  have hr := Paper7Rank.rank_identity 6 p q (by decide) hG
  have he1 := Paper7Lemma22Gaps.deltaE_nonempty_bound 6 p q 1 hKq
  have he2 := Paper7Lemma22Gaps.deltaE_nonempty_bound 6 p q (-1) hKq
  have hb := big_card_le_ten p q hn hG
  rw [hcard, hz] at hr
  omega
#print axioms Paper7C61Classification.nonempty_q_has_zero_p

theorem support_dichotomy (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : q = (fun _ => 0) ∨ ∃ k, p k = 0 := by
  by_cases hq : q = (fun _ => 0)
  · exact Or.inl hq
  · apply Or.inr
    apply nonempty_q_has_zero_p p q hn hG
    by_contra hK
    have he : Kq 6 q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    apply hq
    funext k
    have hk : ¬ 0 < q k := by
      intro hk
      have hm : k ∈ Kq 6 q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
      rw [he] at hm
      exact Finset.notMem_empty k hm
    omega
#print axioms Paper7C61Classification.support_dichotomy

/-- Normalization retains the full graph, both sums, and the order. It does not
claim that guards depending on a chosen prefix are invariant. -/
theorem normalized_zero_q (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) :
    ∃ σ : Fin 6 → Fin 6, IsDihedral 6 σ ∧ (q ∘ σ) 0 = 0 ∧
      0 < ∑ k, ((p ∘ σ) k + (q ∘ σ) k) ∧
      nOf 6 (p ∘ σ) (q ∘ σ) ≤ 42 ∧
      IsIntegralGraph (SG 6 (p ∘ σ) (q ∘ σ)) := by
  obtain ⟨k, hk⟩ := exists_zero_q p q hn hG
  obtain ⟨σ, hσ, hσ0⟩ :=
    Paper7PruningCanonical.dihedral_rotation_to 6 (by decide) k 0 rfl
  refine ⟨σ, hσ, ?_, ?_, ?_, (integral_comp_iff p q σ hσ).mpr hG⟩
  · change q (σ 0) = 0
    rw [hσ0, hk]
  · rwa [pendant_sum_comp p q σ hσ]
  · rwa [nOf_comp p q σ hσ]
#print axioms Paper7C61Classification.normalized_zero_q

end Paper7C61Classification
