import Research.Backfill.Paper7.CycleThreeAbsPacking
import Research.Backfill.Paper7.RankCardinality

/-! Necessary support restrictions from actual exceptional kernels and rank.
No bounded-search result or graph classification is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem deltaE_full_q_zero (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (hq : ∀ k, 0 < q k) : deltaE b p q ε = 0 := by
  have hw : Wmat b p q ε = (1 : Matrix (Fin b) (Fin b) ℝ) := by
    apply Matrix.ext
    intro i j
    simp only [Wmat, hq i, ite_true, Matrix.one_apply, eq_comm]
  unfold deltaE
  rw [hw, Matrix.toLin'_one, LinearMap.ker_id]
  exact finrank_bot ℝ (Fin b → ℝ)
#print axioms Paper7CycleThree.deltaE_full_q_zero

theorem triangle_delta0_le_support (p : Fin 3 → ℕ) :
    delta0 3 p ≤ (Kp 3 p).card := by
  by_cases hK : Kp 3 p = ∅
  · norm_num [delta0, hK]
  · exact Paper7Rank.delta0_le_card_of_nonempty 3 p
      (Finset.nonempty_iff_ne_empty.mpr hK)
#print axioms Paper7CycleThree.triangle_delta0_le_support

theorem triangle_exists_zero_q (p q : Fin 3 → ℕ)
    (hG : IsIntegralGraph (SG 3 p q)) (hn : nOf 3 p q ≤ 49) :
    ∃ k, q k = 0 := by
  classical
  by_contra hzero
  have hq : ∀ k, 0 < q k := by
    intro k
    by_contra hk
    exact hzero ⟨k, by omega⟩
  have hK : Kq 3 q = Finset.univ := by
    ext k
    simp [Kq, hq k]
  have hcard : (Kq 3 q).card = 3 := by simp [hK]
  have hplus := deltaE_full_q_zero 3 p q 1 hq
  have hminus := deltaE_full_q_zero 3 p q (-1) hq
  have hr := Paper7Rank.rank_identity 3 p q (by omega) hG
  rw [hcard, hplus, hminus] at hr
  have hzeroBound := triangle_delta0_le_support p
  have hlarge := triangle_large_card_le_seven p q hG hn
  omega
#print axioms Paper7CycleThree.triangle_exists_zero_q

theorem evenGaps_univ_zero (b : ℕ) : evenGaps b Finset.univ = 0 := by
  classical
  unfold evenGaps
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro k _hk hgap
  obtain ⟨d, hd, heven, _hend, hclear⟩ := hgap
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdle : d ≤ 1 := by
    by_contra h
    exact hclear 1 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) (Finset.mem_univ _)
  have heq : d = 1 := by omega
  subst d
  exact (by decide : ¬ Even (1 : ℕ)) heven
#print axioms Paper7CycleThree.evenGaps_univ_zero

theorem triangle_delta0_full_p_zero (p : Fin 3 → ℕ) (hp : ∀ k, 0 < p k) :
    delta0 3 p = 0 := by
  have hK : Kp 3 p = Finset.univ := by
    ext k
    simp [Kp, hp k]
  have hne : Kp 3 p ≠ ∅ := by rw [hK]; exact Finset.univ_nonempty.ne_empty
  rw [delta0, ite_eq_right hne, hK, evenGaps_univ_zero]
#print axioms Paper7CycleThree.triangle_delta0_full_p_zero

/-- If only one coordinate can lie outside the q-support, evaluation there
injects the actual exceptional kernel into the one-dimensional scalar space. -/
theorem triangle_deltaE_single_free_le_one (p q : Fin 3 → ℕ) (j : Fin 3)
    (hq : ∀ k, k ≠ j → 0 < q k) (ε : ℝ) : deltaE 3 p q ε ≤ 1 := by
  let S := LinearMap.ker (Matrix.toLin' (Wmat 3 p q ε))
  let ev : S →ₗ[ℝ] ℝ := (LinearMap.proj j).comp S.subtype
  have hinj : Function.Injective ev := by
    intro y z heq
    apply Subtype.ext
    funext k
    by_cases hk : k = j
    · subst k
      exact heq
    · have hy : y.val k = 0 :=
        Paper7Lemma22Gaps.kernel_zero_on_support 3 p q ε y.val y.property k
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq k hk⟩)
      have hz : z.val k = 0 :=
        Paper7Lemma22Gaps.kernel_zero_on_support 3 p q ε z.val z.property k
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq k hk⟩)
      exact hy.trans hz.symm
  change Module.finrank ℝ S ≤ 1
  simpa only [Module.finrank_self] using ev.finrank_le_finrank_of_injective hinj
#print axioms Paper7CycleThree.triangle_deltaE_single_free_le_one

theorem triangle_two_q_exists_zero_p (p q : Fin 3 → ℕ)
    (hG : IsIntegralGraph (SG 3 p q)) (hn : nOf 3 p q ≤ 49)
    (j : Fin 3) (hqj : q j = 0) (hq : ∀ k, k ≠ j → 0 < q k) :
    ∃ k, p k = 0 := by
  by_contra hzero
  have hp : ∀ k, 0 < p k := by
    intro k
    by_contra hk
    exact hzero ⟨k, by omega⟩
  have hKp : Kp 3 p = Finset.univ := by
    ext k
    simp [Kp, hp k]
  have hKq : Kq 3 q = Finset.univ.erase j := by
    ext k
    by_cases hk : k = j
    · subst k
      simp [Kq, hqj]
    · simp [Kq, hk, hq k hk]
  have hpcard : (Kp 3 p).card = 3 := by simp [hKp]
  have hqcard : (Kq 3 q).card = 2 := by simp [hKq]
  have hz := triangle_delta0_full_p_zero p hp
  have hplus := triangle_deltaE_single_free_le_one p q j hq 1
  have hminus := triangle_deltaE_single_free_le_one p q j hq (-1)
  have hr := Paper7Rank.rank_identity 3 p q (by omega) hG
  rw [hpcard, hqcard, hz] at hr
  have hlarge := triangle_large_card_le_seven p q hG hn
  omega
#print axioms Paper7CycleThree.triangle_two_q_exists_zero_p

end Paper7CycleThree
