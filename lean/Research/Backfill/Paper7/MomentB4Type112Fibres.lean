import Research.Backfill.Paper7.MomentB4Type112Bounds

/-! NEW SOURCE ONLY. A complete bijection for the original Type112.
The repeated middle q is retained in the finite index; the two remaining
q coordinates are an interval fibre. No numerical sum is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

abbrev B4Type112RowIndex := Fin 38 × Fin 19 × Fin 38 × Fin 19
#print axioms Paper7MomentCanonicalNumeric.B4Type112RowIndex

abbrev B4Type112Index := B4Type112RowIndex × Fin 10
#print axioms Paper7MomentCanonicalNumeric.B4Type112Index

def type112Row (r : B4Type112RowIndex) : Fin 4 → ℕ :=
  ![r.1.val,r.2.1.val,r.2.2.1.val,r.2.1.val]
#print axioms Paper7MomentCanonicalNumeric.type112Row

def type112Residual (r : B4Type112Index) : ℕ := r.1.2.2.2.val-2*r.2.val
#print axioms Paper7MomentCanonicalNumeric.type112Residual

def type112Accept (r : B4Type112Index) : Prop :=
  r.2.val ≤ r.1.2.1.val ∧ 2*r.2.val ≤ r.1.2.2.2.val ∧
    B4CatalogRowAccept (type112Row r.1) r.1.2.2.2.val
#print axioms Paper7MomentCanonicalNumeric.type112Accept

abbrev B4Type112Fibre (r : B4Type112Index) :=
  {q : ℕ // type112Residual r-r.1.2.2.1.val ≤ q ∧
    q ≤ min r.1.1.val (type112Residual r) ∧ type112Accept r}
#print axioms Paper7MomentCanonicalNumeric.B4Type112Fibre

instance b4Type112FibreFintype (r : B4Type112Index) : Fintype (B4Type112Fibre r) :=
  Fintype.subtype
    ((Finset.Icc (type112Residual r-r.1.2.2.1.val) (min r.1.1.val (type112Residual r))).filter
      (fun _ => type112Accept r)) (by
      intro q
      by_cases ha : type112Accept r
      · simp [ha]
      · simp [ha])
#print axioms Paper7MomentCanonicalNumeric.b4Type112FibreFintype

def b4Type112Encode (w : B4Type112) : Σ r : B4Type112Index, B4Type112Fibre r := by
  have hb := b4_type112_budget_bounds w
  let z : Fin 38 := ⟨w.val.1.1.val+w.val.1.2.val,by omega⟩
  let t : Fin 19 := ⟨w.val.2.1.1.val+w.val.2.1.2.val,by omega⟩
  let u : Fin 38 := ⟨w.val.2.2.1.val+w.val.2.2.2.val,by omega⟩
  let Q : Fin 19 := ⟨w.val.1.2.val+2*w.val.2.1.2.val+w.val.2.2.2.val,by omega⟩
  let k : Fin 10 := ⟨w.val.2.1.2.val,by omega⟩
  refine ⟨((z,t,u,Q),k),w.val.1.2.val,?_,?_,?_,?_,?_⟩
  · dsimp [type112Residual,Q,k,u]
    omega
  · apply le_min
    · dsimp [z]; omega
    · dsimp [type112Residual,Q,k]; omega
  · dsimp [k,t]
    omega
  · dsimp [k,Q]
    omega
  · exact (b4_three_letter_catalog_iff w.val.1 w.val.2.1 w.val.2.2).mp w.property
#print axioms Paper7MomentCanonicalNumeric.b4Type112Encode

def b4Type112Decode (s : Σ r : B4Type112Index, B4Type112Fibre r) : B4Type112 := by
  have hqz : s.2.val ≤ s.1.1.1.val := (le_min_iff.mp s.2.property.2.1).1
  have hqR : s.2.val ≤ type112Residual s.1 := (le_min_iff.mp s.2.property.2.1).2
  have hqu : type112Residual s.1-s.2.val ≤ s.1.1.2.2.1.val := by
    have := s.2.property.1
    omega
  have hkt : s.1.2.val ≤ s.1.1.2.1.val := s.2.property.2.2.1
  have hkQ : 2*s.1.2.val ≤ s.1.1.2.2.2.val := s.2.property.2.2.2.1
  have hRQ : type112Residual s.1 ≤ s.1.1.2.2.2.val := Nat.sub_le _ _
  let a : B4Letter :=
    (⟨s.1.1.1.val-s.2.val,by have := s.1.1.1.isLt; omega⟩,
     ⟨s.2.val,by have := s.1.1.2.2.2.isLt; omega⟩)
  let b : B4Letter :=
    (⟨s.1.1.2.1.val-s.1.2.val,by have := s.1.1.2.1.isLt; omega⟩,
     ⟨s.1.2.val,by have := s.1.2.isLt; omega⟩)
  let c : B4Letter :=
    (⟨s.1.1.2.2.1.val-(type112Residual s.1-s.2.val),by have := s.1.1.2.2.1.isLt; omega⟩,
     ⟨type112Residual s.1-s.2.val,by have := s.1.1.2.2.2.isLt; omega⟩)
  refine ⟨(a,b,c),?_⟩
  apply (b4_three_letter_catalog_iff a b c).mpr
  have ha : a.1.val+a.2.val = s.1.1.1.val := Nat.sub_add_cancel hqz
  have hb : b.1.val+b.2.val = s.1.1.2.1.val := Nat.sub_add_cancel hkt
  have hc : c.1.val+c.2.val = s.1.1.2.2.1.val := Nat.sub_add_cancel hqu
  have hQ : a.2.val+2*b.2.val+c.2.val = s.1.1.2.2.2.val := by
    dsimp [a,b,c,type112Residual]
    dsimp [type112Residual] at hqR
    omega
  rw [ha,hb,hc,hQ]
  exact s.2.property.2.2.2.2
#print axioms Paper7MomentCanonicalNumeric.b4Type112Decode

theorem b4Type112Decode_encode (w : B4Type112) : b4Type112Decode (b4Type112Encode w) = w := by
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> apply Fin.ext
    · change (w.val.1.1.val+w.val.1.2.val)-w.val.1.2.val = w.val.1.1.val
      omega
    · rfl
  · apply Prod.ext
    · apply Prod.ext <;> apply Fin.ext
      · change (w.val.2.1.1.val+w.val.2.1.2.val)-w.val.2.1.2.val = w.val.2.1.1.val
        omega
      · rfl
    · apply Prod.ext <;> apply Fin.ext
      · change (w.val.2.2.1.val+w.val.2.2.2.val)-
          ((w.val.1.2.val+2*w.val.2.1.2.val+w.val.2.2.2.val)-
            2*w.val.2.1.2.val-w.val.1.2.val) = w.val.2.2.1.val
        omega
      · change (w.val.1.2.val+2*w.val.2.1.2.val+w.val.2.2.2.val)-
          2*w.val.2.1.2.val-w.val.1.2.val = w.val.2.2.2.val
        omega
#print axioms Paper7MomentCanonicalNumeric.b4Type112Decode_encode

theorem b4Type112Encode_decode (s : Σ r : B4Type112Index, B4Type112Fibre r) :
    b4Type112Encode (b4Type112Decode s) = s := by
  have hqz : s.2.val ≤ s.1.1.1.val := (le_min_iff.mp s.2.property.2.1).1
  have hqR : s.2.val ≤ type112Residual s.1 := (le_min_iff.mp s.2.property.2.1).2
  have hqu : type112Residual s.1-s.2.val ≤ s.1.1.2.2.1.val := by
    have := s.2.property.1
    omega
  have hkt : s.1.2.val ≤ s.1.1.2.1.val := s.2.property.2.2.1
  have hkQ : 2*s.1.2.val ≤ s.1.1.2.2.2.val := s.2.property.2.2.2.1
  apply Sigma.subtype_ext
  · apply Prod.ext
    · apply Prod.ext
      · apply Fin.ext
        change (s.1.1.1.val-s.2.val)+s.2.val = s.1.1.1.val
        omega
      · apply Prod.ext
        · apply Fin.ext
          change (s.1.1.2.1.val-s.1.2.val)+s.1.2.val = s.1.1.2.1.val
          omega
        · apply Prod.ext <;> apply Fin.ext
          · change (s.1.1.2.2.1.val-(type112Residual s.1-s.2.val))+
              (type112Residual s.1-s.2.val) = s.1.1.2.2.1.val
            omega
          · change s.2.val+2*s.1.2.val+(type112Residual s.1-s.2.val) = s.1.1.2.2.2.val
            dsimp [type112Residual] at hqR ⊢
            omega
    · apply Fin.ext
      rfl
  · rfl
#print axioms Paper7MomentCanonicalNumeric.b4Type112Encode_decode

def b4Type112FibreEquiv : B4Type112 ≃ Σ r : B4Type112Index, B4Type112Fibre r where
  toFun := b4Type112Encode
  invFun := b4Type112Decode
  left_inv := b4Type112Decode_encode
  right_inv := b4Type112Encode_decode
#print axioms Paper7MomentCanonicalNumeric.b4Type112FibreEquiv

theorem b4Type112Fibre_card (r : B4Type112Index) :
    Fintype.card (B4Type112Fibre r) = if type112Accept r then
      min r.1.1.val (type112Residual r)+1-(type112Residual r-r.1.2.2.1.val) else 0 := by
  rw [Fintype.card_of_subtype
    (p := fun q : ℕ => type112Residual r-r.1.2.2.1.val ≤ q ∧
      q ≤ min r.1.1.val (type112Residual r) ∧ type112Accept r)
    ((Finset.Icc (type112Residual r-r.1.2.2.1.val) (min r.1.1.val (type112Residual r))).filter
      (fun _ => type112Accept r)) (by
      intro q
      by_cases ha : type112Accept r
      · simp [ha]
      · simp [ha])]
  by_cases ha : type112Accept r <;> simp [ha]
#print axioms Paper7MomentCanonicalNumeric.b4Type112Fibre_card

def b4Type112FiniteSum : ℕ := ∑ r : B4Type112Index,
  if type112Accept r then
    min r.1.1.val (type112Residual r)+1-(type112Residual r-r.1.2.2.1.val) else 0
#print axioms Paper7MomentCanonicalNumeric.b4Type112FiniteSum

theorem b4_type112_card_eq_finite_sum : Fintype.card B4Type112 = b4Type112FiniteSum := by
  rw [Fintype.card_congr b4Type112FibreEquiv,Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun r _ => b4Type112Fibre_card r)
#print axioms Paper7MomentCanonicalNumeric.b4_type112_card_eq_finite_sum

end Paper7MomentCanonicalNumeric
