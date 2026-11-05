import Research.Backfill.Paper7.MomentB4FixedTypeTriangleSlices

/-! SOURCE ONLY. Exact coordinates for every strict Type22 triangle pair.
S=z+t and D=t-z retain zero endpoints, parity, the original R guard,
the whole catalogue, and the original interval-fibre weight. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

abbrev B4Type22StrictPair :=
  {p : Fin 19 × Fin 19 // p.1 < p.2 ∧ p.1.val+p.2.val ≤ 18}
#print axioms Paper7MomentCanonicalNumeric.B4Type22StrictPair

abbrev B4Type22StrictSD :=
  {s : Fin 19 × Fin 19 // 0 < s.2.val ∧ s.2.val ≤ s.1.val ∧
    (s.1.val-s.2.val)%2 = 0}
#print axioms Paper7MomentCanonicalNumeric.B4Type22StrictSD

theorem type22_sd_nat_decode (S D : ℕ) (hD : 0 < D) (hDS : D ≤ S)
    (hpar : (S-D)%2 = 0) :
    (S-D)/2 < (S+D)/2 ∧ (S-D)/2+(S+D)/2 = S ∧
      (S+D)/2-(S-D)/2 = D := by omega
#print axioms Paper7MomentCanonicalNumeric.type22_sd_nat_decode

theorem type22_sd_nat_encode (z t : ℕ) (hzt : z ≤ t) :
    (z+t-(t-z))/2 = z ∧ (z+t+(t-z))/2 = t := by omega
#print axioms Paper7MomentCanonicalNumeric.type22_sd_nat_encode

def type22StrictPairToSD (p : B4Type22StrictPair) : B4Type22StrictSD := by
  have hp : p.val.1.val < p.val.2.val := p.property.1
  have hb := p.property.2
  refine ⟨(⟨p.val.1.val+p.val.2.val,by omega⟩,
    ⟨p.val.2.val-p.val.1.val,by have := p.val.2.isLt; omega⟩),?_,?_,?_⟩
  all_goals dsimp; omega
#print axioms Paper7MomentCanonicalNumeric.type22StrictPairToSD

def type22StrictSDToPair (s : B4Type22StrictSD) : B4Type22StrictPair := by
  have hS := s.val.1.isLt
  have hD := s.property.1
  have hDS := s.property.2.1
  have hpar := s.property.2.2
  have hc := type22_sd_nat_decode s.val.1.val s.val.2.val hD hDS hpar
  refine ⟨(⟨(s.val.1.val-s.val.2.val)/2,by omega⟩,
    ⟨(s.val.1.val+s.val.2.val)/2,by omega⟩),?_,?_⟩
  · exact hc.1
  · change (s.val.1.val-s.val.2.val)/2+(s.val.1.val+s.val.2.val)/2 ≤ 18
    omega
#print axioms Paper7MomentCanonicalNumeric.type22StrictSDToPair

theorem type22_sd_decode_encode (p : B4Type22StrictPair) :
    type22StrictSDToPair (type22StrictPairToSD p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact (type22_sd_nat_encode p.val.1.val p.val.2.val p.property.1.le).1
  · apply Fin.ext
    exact (type22_sd_nat_encode p.val.1.val p.val.2.val p.property.1.le).2
#print axioms Paper7MomentCanonicalNumeric.type22_sd_decode_encode

theorem type22_sd_encode_decode (s : B4Type22StrictSD) :
    type22StrictPairToSD (type22StrictSDToPair s) = s := by
  have hc := type22_sd_nat_decode s.val.1.val s.val.2.val
    s.property.1 s.property.2.1 s.property.2.2
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact hc.2.1
  · apply Fin.ext
    exact hc.2.2
#print axioms Paper7MomentCanonicalNumeric.type22_sd_encode_decode

def type22StrictPairSDEquiv : B4Type22StrictPair ≃ B4Type22StrictSD where
  toFun := type22StrictPairToSD
  invFun := type22StrictSDToPair
  left_inv := type22_sd_decode_encode
  right_inv := type22_sd_encode_decode
#print axioms Paper7MomentCanonicalNumeric.type22StrictPairSDEquiv

def b4Type22MomentSD (S D R : ℕ) : ℤ :=
  12+6*(S : ℤ)+(S : ℤ)^2+(D : ℤ)^2+4*(R : ℤ)
#print axioms Paper7MomentCanonicalNumeric.b4Type22MomentSD

theorem type22_theta_sum_difference (z t : Fin 19) (R : Fin 10) (hzt : z ≤ t) :
    b4Theta (type22Row (z,t,R)) (2*R.val)+4 =
      b4Type22MomentSD (z.val+t.val) (t.val-z.val) R.val := by
  have hz : z.val ≤ t.val := hzt
  norm_num [b4Theta,type22Row,Fin.sum_univ_four,b4Type22MomentSD,Nat.cast_sub hz]
  ring
#print axioms Paper7MomentCanonicalNumeric.type22_theta_sum_difference

def b4Type22SDAccept (S D R : ℕ) : Prop :=
  R ≤ S ∧ 0 < S+R ∧ S+R ≤ 18 ∧
    ∃ sm ∈ b4FeatureCatalog, sm.2 = b4Type22MomentSD S D R ∧
      sm.1 ≤ (4+(2*S+2*R) : ℕ) ∧
      ((4+(2*S+2*R) : ℕ) : ℤ)-max ((2*R : ℕ) : ℤ) 2 ≤ sm.1
#print axioms Paper7MomentCanonicalNumeric.b4Type22SDAccept

theorem type22_accept_iff_sum_difference (z t : Fin 19) (R : Fin 10) (hzt : z ≤ t) :
    type22Accept (z,t,R) ↔ b4Type22SDAccept (z.val+t.val) (t.val-z.val) R.val := by
  have hs : (∑ i, type22Row (z,t,R) i) = 2*(z.val+t.val) := by
    norm_num [type22Row,Fin.sum_univ_four]
    omega
  have hM := type22_theta_sum_difference z t R hzt
  unfold type22Accept B4CatalogRowAccept b4Type22SDAccept
  dsimp only [Prod.fst, Prod.snd]
  rw [hs,hM]
  constructor
  · rintro ⟨hQ,hp,hn,hcat⟩
    exact ⟨by omega,by omega,by omega,hcat⟩
  · rintro ⟨hQ,hp,hn,hcat⟩
    exact ⟨by omega,by omega,by omega,hcat⟩
#print axioms Paper7MomentCanonicalNumeric.type22_accept_iff_sum_difference

theorem type22_sd_decoded_accept (s : B4Type22StrictSD) (R : Fin 10) :
    type22Accept ((type22StrictSDToPair s).val.1,(type22StrictSDToPair s).val.2,R) ↔
      b4Type22SDAccept s.val.1.val s.val.2.val R.val := by
  rw [type22_accept_iff_sum_difference _ _ R (type22StrictSDToPair s).property.1.le]
  have hc := type22_sd_nat_decode s.val.1.val s.val.2.val
    s.property.1 s.property.2.1 s.property.2.2
  change b4Type22SDAccept
    ((s.val.1.val-s.val.2.val)/2+(s.val.1.val+s.val.2.val)/2)
    ((s.val.1.val+s.val.2.val)/2-(s.val.1.val-s.val.2.val)/2) R.val ↔ _
  rw [hc.2.1,hc.2.2]
#print axioms Paper7MomentCanonicalNumeric.type22_sd_decoded_accept

theorem type22_sd_catalog_remainder (S D R : ℕ) (ha : b4Type22SDAccept S D R) :
    ∃ sm ∈ b4FeatureCatalog,
      sm.2-(12+6*(S : ℤ)+(S : ℤ)^2+(D : ℤ)^2) = 4*(R : ℤ) ∧
      0 ≤ sm.2-(12+6*(S : ℤ)+(S : ℤ)^2+(D : ℤ)^2) ∧
      sm.2-(12+6*(S : ℤ)+(S : ℤ)^2+(D : ℤ)^2) ≤ 4*(18-(S : ℤ)) := by
  rcases ha with ⟨_hRS,_hp,hbudget,sm,hm,hM,_hlo,_hhi⟩
  have hRN : 0 ≤ (R : ℤ) := Int.natCast_nonneg R
  have hbound : (S : ℤ)+R ≤ 18 := by exact_mod_cast hbudget
  unfold b4Type22MomentSD at hM
  refine ⟨sm,hm,?_,?_,?_⟩ <;> linarith
#print axioms Paper7MomentCanonicalNumeric.type22_sd_catalog_remainder

def b4Type22SDStrip (S : Fin 19) : ℕ :=
  ∑ D : Fin 19, ∑ R : Fin 10,
    if (0 < D.val ∧ D.val ≤ S.val ∧ (S.val-D.val)%2 = 0) ∧
        b4Type22SDAccept S.val D.val R.val then
      min ((S.val-D.val)/2) R.val+1-(R.val-(S.val+D.val)/2) else 0
#print axioms Paper7MomentCanonicalNumeric.b4Type22SDStrip

end Paper7MomentCanonicalNumeric
