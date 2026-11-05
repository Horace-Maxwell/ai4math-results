import Research.Backfill.Paper7.MomentB4Type22SumDifference

/-! SOURCE ONLY. General exact support-sum interface and three complete
zero-band certificates. Numerical candidate supports are never hypotheses
of the final count; each is checked by its complete finite-domain theorem. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open scoped BigOperators Classical

def type22SDRowAccept (S : ℕ) (D : Fin 19) (R : Fin 10) : Prop :=
  (0 < D.val ∧ D.val ≤ S ∧ (S-D.val)%2 = 0) ∧
    b4Type22SDAccept S D.val R.val
#print axioms Paper7MomentCanonicalNumeric.type22SDRowAccept

theorem type22_strip_eq_support (S : Fin 19) (a : Finset (Fin 19 × Fin 10))
    (hc : ∀ D : Fin 19, ∀ R : Fin 10, type22SDRowAccept S.val D R ↔ (D,R) ∈ a) :
    b4Type22SDStrip S = ∑ p ∈ a,
      (min ((S.val-p.1.val)/2) p.2.val+1-(p.2.val-(S.val+p.1.val)/2)) := by
  unfold b4Type22SDStrip
  dsimp only [type22SDRowAccept] at hc
  simp_rw [hc]
  calc
    _ = ∑ p : Fin 19 × Fin 10, if p ∈ a then
        min ((S.val-p.1.val)/2) p.2.val+1-(p.2.val-(S.val+p.1.val)/2) else 0 := by
      rw [Fintype.sum_prod_type]
    _ = _ := Finset.sum_ite_mem_eq a _
#print axioms Paper7MomentCanonicalNumeric.type22_strip_eq_support

theorem type22_strip_eq_zero_of_no_row (S : Fin 19)
    (hc : ∀ D : Fin 19, ∀ R : Fin 10, ¬ type22SDRowAccept S.val D R) :
    b4Type22SDStrip S = 0 := by
  unfold b4Type22SDStrip
  dsimp only [type22SDRowAccept] at hc
  apply Finset.sum_eq_zero
  intro D _
  apply Finset.sum_eq_zero
  intro R _
  exact ite_eq_right (hc D R)
#print axioms Paper7MomentCanonicalNumeric.type22_strip_eq_zero_of_no_row

theorem type22_low_band_certificate : ∀ S : Fin 4, ∀ D : Fin 19, ∀ R : Fin 10,
    ¬ type22SDRowAccept S.val D R := by
  simp only [type22SDRowAccept,b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_low_band_certificate

theorem type22_middle_zero_band_certificate : ∀ S : Fin 2, ∀ D : Fin 19,
    ∀ R : Fin 10, ¬ type22SDRowAccept (7+S.val) D R := by
  simp only [type22SDRowAccept,b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_middle_zero_band_certificate

theorem type22_high_band_certificate : ∀ S : Fin 3, ∀ D : Fin 19, ∀ R : Fin 10,
    ¬ type22SDRowAccept (16+S.val) D R := by
  simp only [type22SDRowAccept,b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_high_band_certificate

theorem b4_type22_strip_zero_low (S : Fin 19) (hS : S.val < 4) :
    b4Type22SDStrip S = 0 := by
  apply type22_strip_eq_zero_of_no_row
  exact type22_low_band_certificate ⟨S.val,hS⟩
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strip_zero_low

theorem b4_type22_strip_zero_middle (S : Fin 19) (hS : S.val = 7 ∨ S.val = 8) :
    b4Type22SDStrip S = 0 := by
  have hb : S.val-7 < 2 := by omega
  have he : 7+(S.val-7) = S.val := by omega
  apply type22_strip_eq_zero_of_no_row
  have hc := type22_middle_zero_band_certificate ⟨S.val-7,hb⟩
  simpa only [he] using hc
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strip_zero_middle

theorem b4_type22_strip_zero_high (S : Fin 19) (hS : 16 ≤ S.val) :
    b4Type22SDStrip S = 0 := by
  have hb : S.val-16 < 3 := by have := S.isLt; omega
  have he : 16+(S.val-16) = S.val := by omega
  apply type22_strip_eq_zero_of_no_row
  have hc := type22_high_band_certificate ⟨S.val-16,hb⟩
  simpa only [he] using hc
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strip_zero_high

end Paper7MomentCanonicalNumeric
