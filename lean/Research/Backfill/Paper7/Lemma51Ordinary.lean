import Research.Backfill.Paper7.SunSchurInertia
import Research.Backfill.Paper7.TridiagonalSignInertia

set_option autoImplicit false

noncomputable section

namespace Paper7Comparison

open BackfillPaper7.Challenge

/-- Exactly the whole ordinary branch of frozen Lemma51, all four inequalities.
The separate exceptional branch is not assumed or folded into this helper. -/
theorem lemma51_ordinary (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (m : ℝ) (t : Fin b → ℝ) (hm : 2 ≤ m)
    (ht : ∀ k ∈ Xset b, t k ≤ fk b p q m k - m) :
    nPos (tridiag (Xset b) t) ≤ Ngt (SG b p q) m ∧
      nPos (tridiag (Xset b) t) ≤ Nlt (SG b p q) (-m) ∧
      nPos (tridiag (Xset b) t) + nZero (tridiag (Xset b) t) ≤ Nge (SG b p q) m ∧
      nPos (tridiag (Xset b) t) + nZero (tridiag (Xset b) t) ≤ Nle (SG b p q) (-m) := by
  have hm0 : m ≠ 0 := by linarith
  have hmq : m ^ 2 - 1 ≠ 0 := by nlinarith
  have hmn0 : -m ≠ 0 := neg_ne_zero.mpr hm0
  have hmnq : (-m) ^ 2 - 1 ≠ 0 := by simpa only [neg_sq] using hmq
  have hmono := tridiag_inertia_mono (Xset b) t (fun k => fk b p q m k - m) ht
  have hp := sunSchur_compressed_bounds b p q hb (Xset b) (fun _ h => h) m hm0 hmq
  have hn := sunSchur_compressed_bounds b p q hb (Xset b) (fun _ h => h) (-m) hmn0 hmnq
  have hs := reduced_tridiag_negative_parameter b p q (Xset b) m
  rw [hs.1, hs.2] at hn
  exact ⟨hmono.1.trans hp.1, hmono.1.trans hn.2.1,
    hmono.2.2.trans hp.2.2.1, hmono.2.2.trans hn.2.2.2⟩
#print axioms Paper7Comparison.lemma51_ordinary

end Paper7Comparison
