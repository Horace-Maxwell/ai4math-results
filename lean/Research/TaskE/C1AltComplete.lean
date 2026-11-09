import Research.TaskE.C1AltCore

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma c1_one_alt : CodexPaper1.TaskE.Challenge.C1OneAltThree := by
  intro a ha q hq g hg hna y hy0 hy1 c _hc halt
  rcases halt with hc | hc
  · let w : ℕ → ℝ := fun i => -g i
    have hw : IsSignVec a w := by
      intro i hi
      rcases hg i hi with h | h <;> simp [w, h]
    have hn : ¬ (∀ i ≤ a, w i = -sAlt i) := by
      intro hh
      apply hna
      left
      intro i hi
      have ht := hh i hi
      dsimp [w] at ht
      linarith
    have hd : DeltaC a 3 w = DeltaC a 3 g :=
      CodexPaper1.Chain.delta_sign_scale a 3 1 w g (by intros; simp [w])
    have hp : psi a 3 q y c (fun i => -mu q 0 * g i) =
        psi a 3 q y sAlt (fun i => mu q 0 * w i) := by
      apply CodexPaper1.Prop31.psi_congr _ _ _ _ hc
      intro i _hi
      dsimp [w]
      ring
    have hh := c1_one_alt_positive ha hq hy0 hy1 hw hn
    rw [hd] at hh
    rw [hp]
    exact hh
  · have hn : ¬ (∀ i ≤ a, g i = -sAlt i) := by intro hh; exact hna (Or.inr hh)
    have hh := c1_one_alt_positive ha hq hy0 hy1 hg hn
    have hp : psi a 3 q y c (fun i => -mu q 0 * g i) =
        psi a 3 q y (fun i => -sAlt i) (fun i => -(mu q 0 * g i)) := by
      apply CodexPaper1.Prop31.psi_congr _ _ _ _ hc
      intro i _hi
      ring
    have hnψ : psi a 3 q y (fun i => -sAlt i) (fun i => -(mu q 0 * g i)) =
        psi a 3 q y sAlt (fun i => mu q 0 * g i) := by
      simpa only [pow_one, neg_one_mul] using
        CodexPaper1.Prop31.psi_sign_scale a 3 q y sAlt (fun i => mu q 0 * g i) 1
    rw [hp, hnψ]
    exact hh

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.c1_one_alt
