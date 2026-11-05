import Research.Backfill.Paper7.LegacyCandidates
import Research.Backfill.Paper7.Lemma24
import Research.Backfill.Paper7.WindowBounds

/-! Actual spectral multiplicities, encoded in the frozen finite feature type.
Source-only candidate: no admissibility or search correctness is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningSpectrum
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem value_abs_bound (i : Fin 8) : (2 : ℝ) ≤ |(value i : ℝ)| := by
  have h : (2 : ℕ) ≤ value i := by simp only [value]; omega
  have hr : (2 : ℝ) ≤ value i := by exact_mod_cast h
  exact hr.trans (le_abs_self _)
#print axioms Paper7PruningSpectrum.value_abs_bound

def actualCounts (b : ℕ) (x : PQ b) (hb : 3 ≤ b) : SpectralCounts :=
  (fun i => ⟨mult (SG b x.1 x.2) (value i),
    Nat.lt_succ_of_le (Paper7Admissible.lemma24_large_multiplicity b x.1 x.2 hb
      (value i) (value_abs_bound i))⟩,
   if Even b then 0 else fun i => ⟨mult (SG b x.1 x.2) (-(value i : ℝ)),
    Nat.lt_succ_of_le (Paper7Admissible.lemma24_large_multiplicity b x.1 x.2 hb
      (-(value i : ℝ)) (by simpa only [abs_neg] using value_abs_bound i))⟩)
#print axioms Paper7PruningSpectrum.actualCounts

theorem actualCounts_pos (b : ℕ) (x : PQ b) (hb : 3 ≤ b) (i : Fin 8) :
    ((actualCounts b x hb).1 i).val = mult (SG b x.1 x.2) (value i) := rfl
#print axioms Paper7PruningSpectrum.actualCounts_pos

theorem actualCounts_neg_even (b : ℕ) (x : PQ b) (hb : 3 ≤ b) (he : Even b) :
    (actualCounts b x hb).2 = 0 := by simp only [actualCounts, ite_eq_left he]
#print axioms Paper7PruningSpectrum.actualCounts_neg_even

theorem actualCounts_neg_odd (b : ℕ) (x : PQ b) (hb : 3 ≤ b) (ho : Odd b) (i : Fin 8) :
    ((actualCounts b x hb).2 i).val = mult (SG b x.1 x.2) (-(value i : ℝ)) := by
  simp only [actualCounts, ite_eq_right (Nat.not_even_iff_odd.mpr ho)]
#print axioms Paper7PruningSpectrum.actualCounts_neg_odd

theorem nOf_eq_b_weight (b : ℕ) (x : PQ b) : nOf b x.1 x.2 = b + weight x := by
  unfold nOf weight pSum qSum
  omega
#print axioms Paper7PruningSpectrum.nOf_eq_b_weight

theorem budget_pendants_positive (b N : ℕ) (x : PQ b) (hx : Budget b N x) :
    0 < ∑ k, (x.1 k + x.2 k) := by
  have hw := hx.1
  rw [sum_add_distrib]
  unfold weight pSum qSum at hw
  omega
#print axioms Paper7PruningSpectrum.budget_pendants_positive

theorem budget_spectral_window (b N : ℕ) (x : PQ b) (hb : 3 ≤ b)
    (hN : N ≤ 49) (hx : Budget b N x) :
    ∀ a ∈ spec (SG b x.1 x.2), |a| < 10 := by
  have hn : nOf b x.1 x.2 ≤ 49 := by
    rw [nOf_eq_b_weight]
    exact hx.2.trans hN
  intro a ha
  exact (Paper7SpectralWindow.sun_spectral_window b x.1 x.2 hb hn a ha).2
#print axioms Paper7PruningSpectrum.budget_spectral_window

end Paper7PruningSpectrum
