import Research.Backfill.Paper7.MomentB4PairInterval

/-! NEW SOURCE ONLY. Full finite-fibre count of the original Type22.
All word constraints, zero boundaries, catalogue guards and Q multiplicities
are retained. This is an unevaluated finite sum, not a numerical count. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

abbrev B4Type22Index := Fin 19 × Fin 19 × Fin 10
#print axioms Paper7MomentCanonicalNumeric.B4Type22Index

def type22Row (r : B4Type22Index) : Fin 4 → ℕ :=
  ![r.1.val,r.2.1.val,r.1.val,r.2.1.val]
#print axioms Paper7MomentCanonicalNumeric.type22Row

def type22Accept (r : B4Type22Index) : Prop :=
  B4CatalogRowAccept (type22Row r) (2*r.2.2.val)
#print axioms Paper7MomentCanonicalNumeric.type22Accept

abbrev B4Type22Fibre (r : B4Type22Index) :=
  {q : ℕ // r.2.2.val-r.2.1.val ≤ q ∧ q ≤ min r.1.val r.2.2.val ∧ type22Accept r}
#print axioms Paper7MomentCanonicalNumeric.B4Type22Fibre

instance b4Type22FibreFintype (r : B4Type22Index) : Fintype (B4Type22Fibre r) :=
  Fintype.subtype ((Finset.Icc (r.2.2.val-r.2.1.val) (min r.1.val r.2.2.val)).filter
    (fun _ => type22Accept r)) (by
      intro q
      by_cases ha : type22Accept r
      · simp [ha]
      · simp [ha])
#print axioms Paper7MomentCanonicalNumeric.b4Type22FibreFintype

def b4Type22Encode (a : B4Type22) : Σ r : B4Type22Index, B4Type22Fibre r := by
  have hb := b4_type22_budget_bounds a
  let z : Fin 19 := ⟨a.val.1.1.val+a.val.1.2.val,by omega⟩
  let t : Fin 19 := ⟨a.val.2.1.val+a.val.2.2.val,by omega⟩
  let R : Fin 10 := ⟨a.val.1.2.val+a.val.2.2.val,by omega⟩
  refine ⟨(z,t,R),a.val.1.2.val,?_,?_,?_⟩
  · dsimp [R,t]
    omega
  · apply le_min
    · dsimp [z]; omega
    · dsimp [R]; omega
  · exact (b4_two_letter_catalog_iff a.val.1 a.val.2).mp a.property
#print axioms Paper7MomentCanonicalNumeric.b4Type22Encode

def b4Type22Decode (s : Σ r : B4Type22Index, B4Type22Fibre r) : B4Type22 := by
  have hqz : s.2.val ≤ s.1.1.val := (le_min_iff.mp s.2.property.2.1).1
  have hqR : s.2.val ≤ s.1.2.2.val := (le_min_iff.mp s.2.property.2.1).2
  have hqt : s.1.2.2.val-s.2.val ≤ s.1.2.1.val := by have := s.2.property.1; omega
  let a : B4Letter :=
    (⟨s.1.1.val-s.2.val,by have := s.1.1.isLt; omega⟩,
     ⟨s.2.val,by have := s.1.2.2.isLt; omega⟩)
  let b : B4Letter :=
    (⟨s.1.2.1.val-(s.1.2.2.val-s.2.val),by have := s.1.2.1.isLt; omega⟩,
     ⟨s.1.2.2.val-s.2.val,by have := s.1.2.1.isLt; omega⟩)
  refine ⟨(a,b),?_⟩
  apply (b4_two_letter_catalog_iff a b).mpr
  have ha : a.1.val+a.2.val = s.1.1.val := Nat.sub_add_cancel hqz
  have hb : b.1.val+b.2.val = s.1.2.1.val := Nat.sub_add_cancel hqt
  have hR : a.2.val+b.2.val = s.1.2.2.val := by dsimp [a,b]; omega
  rw [ha,hb,hR]
  exact s.2.property.2.2
#print axioms Paper7MomentCanonicalNumeric.b4Type22Decode

theorem b4Type22Decode_encode (a : B4Type22) : b4Type22Decode (b4Type22Encode a) = a := by
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> apply Fin.ext
    · change (a.val.1.1.val+a.val.1.2.val)-a.val.1.2.val = a.val.1.1.val
      omega
    · rfl
  · apply Prod.ext <;> apply Fin.ext
    · change (a.val.2.1.val+a.val.2.2.val)-
        ((a.val.1.2.val+a.val.2.2.val)-a.val.1.2.val) = a.val.2.1.val
      omega
    · change (a.val.1.2.val+a.val.2.2.val)-a.val.1.2.val = a.val.2.2.val
      omega
#print axioms Paper7MomentCanonicalNumeric.b4Type22Decode_encode

theorem b4Type22Encode_decode (s : Σ r : B4Type22Index, B4Type22Fibre r) :
    b4Type22Encode (b4Type22Decode s) = s := by
  have hqz : s.2.val ≤ s.1.1.val := (le_min_iff.mp s.2.property.2.1).1
  have hqR : s.2.val ≤ s.1.2.2.val := (le_min_iff.mp s.2.property.2.1).2
  have hqt : s.1.2.2.val-s.2.val ≤ s.1.2.1.val := by have := s.2.property.1; omega
  apply Sigma.subtype_ext
  · apply Prod.ext
    · apply Fin.ext
      change (s.1.1.val-s.2.val)+s.2.val = s.1.1.val
      omega
    · apply Prod.ext <;> apply Fin.ext
      · change (s.1.2.1.val-(s.1.2.2.val-s.2.val))+
          (s.1.2.2.val-s.2.val) = s.1.2.1.val
        omega
      · change s.2.val+(s.1.2.2.val-s.2.val) = s.1.2.2.val
        omega
  · rfl
#print axioms Paper7MomentCanonicalNumeric.b4Type22Encode_decode

def b4Type22FibreEquiv : B4Type22 ≃ Σ r : B4Type22Index, B4Type22Fibre r where
  toFun := b4Type22Encode
  invFun := b4Type22Decode
  left_inv := b4Type22Decode_encode
  right_inv := b4Type22Encode_decode
#print axioms Paper7MomentCanonicalNumeric.b4Type22FibreEquiv

theorem b4Type22Fibre_card (r : B4Type22Index) :
    Fintype.card (B4Type22Fibre r) =
      if type22Accept r then min r.1.val r.2.2.val+1-(r.2.2.val-r.2.1.val) else 0 := by
  rw [Fintype.card_of_subtype
    ((Finset.Icc (r.2.2.val-r.2.1.val) (min r.1.val r.2.2.val)).filter
      (fun _ => type22Accept r)) (by
      intro q
      by_cases ha : type22Accept r
      · simp [ha]
      · simp [ha])]
  by_cases ha : type22Accept r <;> simp [ha]
#print axioms Paper7MomentCanonicalNumeric.b4Type22Fibre_card

def b4Type22FiniteSum : ℕ := ∑ r : B4Type22Index,
  if type22Accept r then min r.1.val r.2.2.val+1-(r.2.2.val-r.2.1.val) else 0
#print axioms Paper7MomentCanonicalNumeric.b4Type22FiniteSum

theorem b4_type22_card_eq_finite_sum : Fintype.card B4Type22 = b4Type22FiniteSum := by
  rw [Fintype.card_congr b4Type22FibreEquiv,Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun r _ => b4Type22Fibre_card r)
#print axioms Paper7MomentCanonicalNumeric.b4_type22_card_eq_finite_sum

theorem b4_canonical_clauses_iff_type22_finite_sum :
    ((canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641) ∧
      ((canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641) ↔
        3*b4Type22FiniteSum+2*Fintype.card B4Type112 = 10584 := by
  rw [b4_canonical_clauses_iff_two_types,b4_type22_card_eq_finite_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_canonical_clauses_iff_type22_finite_sum

end Paper7MomentCanonicalNumeric
