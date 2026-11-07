import Research.Backfill.Paper2.EntryTheorems
import Research.Backfill.Paper2.DataSubstitution361047

/-! Complete original indexing and reduced uniqueness; independent of the hard
Fuss-Catalan coefficient identification. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.Rem11Bridges
open PowerSeries BackfillPaper2.Challenge

private theorem index_iff (i : ℕ) :
    (∃ k : ℕ, 2 * i + 1 = 3 ^ k) ↔ ∃ k : ℕ, i = (3 ^ k - 1) / 2 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have ho : Odd (3 ^ k : ℕ) := Odd.pow (by decide : Odd (3 : ℕ))
    obtain ⟨j, hj⟩ := ho
    exact ⟨k, by omega⟩

theorem check_Rem11_remainingStep : Rem11_remainingStep := by
  intro F h0 hF
  have he := EntryA361047.residue F h0 hF
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    exact EntryA361047.S_deriv
  · rw [he]
    exact EntryA361047.S_subst_g
  · intro m
    constructor
    · rintro ⟨k, rfl⟩
      rw [he]
      exact EntryA361047.coeff_S_pow k
    · intro hm
      rw [he]
      exact EntryA361047.coeff_S_nonpow m (by intro k hk; exact hm ⟨k, hk⟩)

theorem check_Rem11_intended : Rem11_intended := by
  intro A h0 hA i
  have h := EntryTheorems.check_Thm10 A h0 hA (2 * i + 1)
  constructor
  · constructor
    · intro hc
      apply (index_iff i).mp
      by_contra hn
      have hz := h.2 hn
      have hbad : (1 : ℤ) ≡ 0 [ZMOD 3] := hc.symm.trans hz
      norm_num [Int.ModEq] at hbad
    · intro hi
      exact h.1 ((index_iff i).mpr hi)
  · intro hi
    apply h.2
    intro hp
    exact hi ((index_iff i).mp hp)

theorem check_Rem11_literalFalse : Rem11_literalFalse := by
  intro A h0 hA
  have h3 : coeff 3 A = 1 :=
    (DataSubstitution361047.check_DATA_A361047 A h0 hA).2.2.1
  refine ⟨h3, ?_⟩
  intro hbad
  have hc : coeff (2 * 2 - 1) A ≡ 1 [ZMOD 3] := by rw [h3]
  obtain ⟨k, hk⟩ := (hbad 2 (by omega)).1.mp hc
  have hsmall : k < 2 := by
    by_contra hn
    have hp := pow_le_pow_right' (by decide : 1 ≤ (3 : ℕ)) (show 2 ≤ k by omega)
    norm_num at hp
    omega
  interval_cases k <;> norm_num at hk


end BackfillPaper2.Rem11Bridges
#print axioms BackfillPaper2.Rem11Bridges.check_Rem11_remainingStep
#print axioms BackfillPaper2.Rem11Bridges.check_Rem11_intended
#print axioms BackfillPaper2.Rem11Bridges.check_Rem11_literalFalse
