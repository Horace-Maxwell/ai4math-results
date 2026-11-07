import Research.Backfill.Paper2.CatalanTransport
import Research.Backfill.Paper2.CatalanParity

/-! Original Theorem 5 outlets for the five Catalan-parity entries.
These use the fully accepted universal coefficient transports, not OEIS samples. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.CatalanTheorems
open PowerSeries BackfillPaper2.Challenge

private theorem parity_bridge (a : ℤ) (n : ℕ) (hn : 1 ≤ n)
    (h : a ≡ (catalan (n - 1) : ℤ) [ZMOD 2]) :
    Odd a ↔ ∃ k : ℕ, n = 2 ^ k := by
  have hc := (ZMod.intCast_eq_intCast_iff _ _ 2).mpr h
  rw [← ZMod.intCast_eq_one_iff_odd, hc, Int.cast_natCast,
    ZMod.natCast_eq_one_iff_odd, CatalanParity.check_RC_catalanParity (n - 1)]
  constructor
  · rintro ⟨k, hk⟩
    have hp : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩

theorem check_Thm5_1 : Thm5_1 := by
  intro A h n hn
  exact parity_bridge (coeff n A) n hn (CatalanTransport.check_RC_coeffMod2.1 A h n hn)

theorem check_Thm5_2 : Thm5_2 := by
  intro A h0 h n hn
  exact parity_bridge (coeff n A) n hn (CatalanTransport.check_RC_coeffMod2.2.1 A h0 h n hn)

theorem check_Thm5_3 : Thm5_3 := by
  intro A h0 h n hn
  exact parity_bridge (coeff n A) n hn (CatalanTransport.check_RC_coeffMod2.2.2.1 A h0 h n hn)

theorem check_Thm5_4_A338633 : Thm5_4_A338633 := by
  intro A T h n hn
  exact parity_bridge (coeff n A) n hn (CatalanTransport.check_RC_coeffMod2.2.2.2.1 A T h n hn)

theorem check_Thm5_4_A338634 : Thm5_4_A338634 := by
  intro A T h n hn
  exact parity_bridge (coeff n A) n hn (CatalanTransport.check_RC_coeffMod2.2.2.2.2 A T h n hn)

end BackfillPaper2.CatalanTheorems
#print axioms BackfillPaper2.CatalanTheorems.check_Thm5_1
#print axioms BackfillPaper2.CatalanTheorems.check_Thm5_2
#print axioms BackfillPaper2.CatalanTheorems.check_Thm5_3
#print axioms BackfillPaper2.CatalanTheorems.check_Thm5_4_A338633
#print axioms BackfillPaper2.CatalanTheorems.check_Thm5_4_A338634
