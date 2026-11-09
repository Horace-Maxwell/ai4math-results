import Research.TaskE.C0AltCore
import Research.TaskE.C0TerminalLow

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma ik_unit_positive {a k : ℕ} {q y : ℝ} (hq : 5 ≤ q) (hy : Ik a k q y) :
    0 < y ∧ y ≤ 1 := by
  obtain ⟨hm0, h0L, hL1, hm1⟩ := q_parameters hq
  unfold Ik at hy
  split_ifs at hy
  · exact ⟨hm0.trans_le hy.1, hy.2.trans (hL1.trans hm1)⟩
  · rcases hy with hy | hy
    · exact ⟨(hm0.trans_le h0L).trans_le hy.1, hy.2.trans hm1⟩
    · rw [hy]; norm_num

lemma c0_zero : CodexPaper1.TaskE.Challenge.C1ZeroThree := by
  intro a ha q hq g hg hga _hneg hplus hlow y hy c hc hanti
  have hu := ik_unit_positive hq hy
  have hprev := terminal_low a ha g hg hga hplus hlow
  have he : q * etaMap q 1 y = q - 1 - y := by
    change q * ((q - 1 - y) / q) = _
    field_simp [show q ≠ 0 by linarith]
  rw [he]
  by_cases halt : IsPmAlt a c
  · rcases halt with halt | halt
    · have hn : ¬ (∀ i ≤ a, g i = -sAlt i) := by
        intro hh
        apply hanti
        intro i hi
        have h1 := halt i hi
        have h2 := hh i hi
        linarith
      have hp := c0_alt_positive ha hq hu.1.le hu.2 hg hprev hn
      have hcψ : psi a 3 q y c g = psi a 3 q y sAlt g :=
        CodexPaper1.Prop31.psi_congr _ _ _ _ halt (by intros; rfl)
      rw [hcψ]
      exact hp
    · let w : ℕ → ℝ := fun i => -g i
      have hw : IsSignVec a w := by
        intro i hi
        rcases hg i hi with h | h <;> simp [w, h]
      have hn : ¬ (∀ i ≤ a, w i = -sAlt i) := by
        intro hh
        apply hanti
        intro i hi
        have h1 := halt i hi
        have h2 := hh i hi
        dsimp [w] at h2
        linarith
      have hwprev : w (a - 1) ≠ w a := by
        intro hh
        apply hprev
        dsimp [w] at hh
        linarith
      have hd : DeltaC a 3 w = DeltaC a 3 g :=
        CodexPaper1.Chain.delta_sign_scale a 3 1 w g (by intros; simp [w])
      have hp := c0_alt_positive ha hq hu.1.le hu.2 hw hwprev hn
      rw [hd] at hp
      have hcψ : psi a 3 q y c g =
          psi a 3 q y (fun i => -sAlt i) (fun i => -w i) := by
        apply CodexPaper1.Prop31.psi_congr _ _ _ _ halt
        intro i _hi
        dsimp [w]; ring
      have hsψ : psi a 3 q y (fun i => -sAlt i) (fun i => -w i) = psi a 3 q y sAlt w := by
        simpa only [pow_one, neg_one_mul] using CodexPaper1.Prop31.psi_sign_scale a 3 q y sAlt w 1
      rw [hcψ, hsψ]
      exact hp
  · exact c0_nonalt ha hq hu.1 hu.2 hc hg halt hanti

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.c0_zero
