import Research.Backfill.Paper7.MomentB4Type22StripSupport

/-! SOURCE ONLY. Seven full remaining nonzero strips. Every support equality
quantifies all D:Fin19 and R:Fin10. Literal supports are candidate data until
their displayed kernel proof bodies pass; no support equality is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open scoped BigOperators Classical

theorem type22_strip_nine_certificate : ∀ D : Fin 19, ∀ R : Fin 10,
    type22SDRowAccept 9 D R ↔ (D,R) ∈ ({(9,9)} : Finset (Fin 19 × Fin 10)) := by
  simp only [type22SDRowAccept,b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_strip_nine_certificate

theorem type22_strip_ten_certificate : ∀ D : Fin 19, ∀ R : Fin 10,
    type22SDRowAccept 10 D R ↔ (D,R) ∈ ({(8,7)} : Finset (Fin 19 × Fin 10)) := by
  simp only [type22SDRowAccept,b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_strip_ten_certificate

theorem type22_strip_eleven_certificate : ∀ D : Fin 19, ∀ R : Fin 10,
    type22SDRowAccept 11 D R ↔ (D,R) ∈ ({(11,4)} : Finset (Fin 19 × Fin 10)) := by
  simp only [type22SDRowAccept,b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_strip_eleven_certificate

theorem type22_strip_twelve_certificate : ∀ D : Fin 19, ∀ R : Fin 10,
    type22SDRowAccept 12 D R ↔ (D,R) ∈ ({(12,3),(12,6)} : Finset (Fin 19 × Fin 10)) := by
  simp only [type22SDRowAccept,b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_strip_twelve_certificate

theorem type22_strip_thirteen_certificate : ∀ D : Fin 19, ∀ R : Fin 10,
    type22SDRowAccept 13 D R ↔ (D,R) ∈ ({(11,4)} : Finset (Fin 19 × Fin 10)) := by
  simp only [type22SDRowAccept,b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_strip_thirteen_certificate

theorem type22_strip_fourteen_certificate : ∀ D : Fin 19, ∀ R : Fin 10,
    type22SDRowAccept 14 D R ↔ (D,R) ∈ ({(6,2)} : Finset (Fin 19 × Fin 10)) := by
  simp only [type22SDRowAccept,b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_strip_fourteen_certificate

theorem type22_strip_fifteen_certificate : ∀ D : Fin 19, ∀ R : Fin 10,
    type22SDRowAccept 15 D R ↔ (D,R) ∈ ({(3,0),(7,2)} : Finset (Fin 19 × Fin 10)) := by
  simp only [type22SDRowAccept,b4Type22SDAccept,b4Type22MomentSD]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type22_strip_fifteen_certificate

theorem b4_type22_strip_nine : b4Type22SDStrip 9 = 1 := by
  rw [type22_strip_eq_support 9 {(9,9)} type22_strip_nine_certificate]
  norm_num
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strip_nine

theorem b4_type22_strip_ten : b4Type22SDStrip 10 = 2 := by
  rw [type22_strip_eq_support 10 {(8,7)} type22_strip_ten_certificate]
  norm_num
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strip_ten

theorem b4_type22_strip_eleven : b4Type22SDStrip 11 = 1 := by
  rw [type22_strip_eq_support 11 {(11,4)} type22_strip_eleven_certificate]
  norm_num
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strip_eleven

theorem b4_type22_strip_twelve : b4Type22SDStrip 12 = 2 := by
  rw [type22_strip_eq_support 12 {(12,3),(12,6)} type22_strip_twelve_certificate]
  norm_num
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strip_twelve

theorem b4_type22_strip_thirteen : b4Type22SDStrip 13 = 2 := by
  rw [type22_strip_eq_support 13 {(11,4)} type22_strip_thirteen_certificate]
  norm_num
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strip_thirteen

theorem b4_type22_strip_fourteen : b4Type22SDStrip 14 = 3 := by
  rw [type22_strip_eq_support 14 {(6,2)} type22_strip_fourteen_certificate]
  norm_num
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strip_fourteen

theorem b4_type22_strip_fifteen : b4Type22SDStrip 15 = 4 := by
  rw [type22_strip_eq_support 15 {(3,0),(7,2)} type22_strip_fifteen_certificate]
  norm_num
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strip_fifteen

end Paper7MomentCanonicalNumeric
