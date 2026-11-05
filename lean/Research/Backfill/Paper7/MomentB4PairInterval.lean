import Research.Backfill.Paper7.MomentB4QuarterTurnEmpty

/-! NEW SOURCE ONLY. Exact original catalogue interface and a closed
two-coordinate bounded-Q fibre. No finite count is evaluated here. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_candidate_catalog_iff (x : PQ 4) :
    x ∈ CandB1 4 41 ↔ B4CatalogRowAccept (fun i => x.1 i+x.2 i) (qSum x) := by
  constructor
  · intro hx
    apply (b4_guarded_catalog_iff _ _).mp
    refine ⟨?_,b4_encode_accept x hx⟩
    change (∑ i, x.2 i) ≤ ∑ i, (x.1 i+x.2 i)
    exact Finset.sum_le_sum (fun i _ => Nat.le_add_left _ _)
  · intro hx
    have hg := (b4_guarded_catalog_iff (fun i => x.1 i+x.2 i) (qSum x)).mpr hx
    have hh := (b4_decode_mem_iff (fun i => x.1 i+x.2 i) x.2
      (fun i => Nat.le_add_left _ _)).mpr hg.2
    simpa only [Nat.add_sub_cancel_right] using hh
#print axioms Paper7MomentCanonicalNumeric.b4_candidate_catalog_iff

abbrev BoundedPairQ (z t R : ℕ) :=
  {q : ℕ × ℕ // q.1 ≤ z ∧ q.2 ≤ t ∧ q.1+q.2 = R}
#print axioms Paper7MomentCanonicalNumeric.BoundedPairQ

def boundedPairQIntervalEquiv (z t R : ℕ) :
    BoundedPairQ z t R ≃ ↥(Finset.Icc (R-t) (min z R)) where
  toFun q := ⟨q.val.1,by
    apply Finset.mem_Icc.mpr
    have h := q.property
    exact ⟨by omega,le_min h.1 (by omega)⟩⟩
  invFun q := ⟨(q.val,R-q.val),by
    have h := Finset.mem_Icc.mp q.property
    have hz := (le_min_iff.mp h.2).1
    have hR := (le_min_iff.mp h.2).2
    exact ⟨hz,by omega,by omega⟩⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h := q.property.2.2
      change R-q.val.1 = q.val.2
      omega
  right_inv q := by apply Subtype.ext; rfl
#print axioms Paper7MomentCanonicalNumeric.boundedPairQIntervalEquiv

instance boundedPairQFinite (z t R : ℕ) : Finite (BoundedPairQ z t R) :=
  Finite.of_injective (boundedPairQIntervalEquiv z t R)
    (boundedPairQIntervalEquiv z t R).injective
#print axioms Paper7MomentCanonicalNumeric.boundedPairQFinite

theorem boundedPairQ_card (z t R : ℕ) :
    Nat.card (BoundedPairQ z t R) = min z R+1-(R-t) := by
  rw [Nat.card_congr (boundedPairQIntervalEquiv z t R),Nat.card_eq_fintype_card,
    Fintype.card_coe,Nat.card_Icc]
#print axioms Paper7MomentCanonicalNumeric.boundedPairQ_card

theorem b4_two_letter_catalog_iff (a b : B4Letter) :
    decodeWord (![a,b,a,b] : Fin 4 → B4Letter) ∈ CandB1 4 41 ↔
      B4CatalogRowAccept
        (![a.1.val+a.2.val,b.1.val+b.2.val,a.1.val+a.2.val,b.1.val+b.2.val] : Fin 4 → ℕ)
        (2*(a.2.val+b.2.val)) := by
  let x : PQ 4 := decodeWord (![a,b,a,b] : Fin 4 → B4Letter)
  have hz : (fun i => x.1 i+x.2 i) =
      (![a.1.val+a.2.val,b.1.val+b.2.val,a.1.val+a.2.val,b.1.val+b.2.val] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hQ : qSum x = 2*(a.2.val+b.2.val) := by
    norm_num [x,decodeWord,qSum,Fin.sum_univ_four]
    omega
  simpa only [hz,hQ] using b4_candidate_catalog_iff x
#print axioms Paper7MomentCanonicalNumeric.b4_two_letter_catalog_iff

theorem b4_type22_budget_bounds (a : B4Type22) :
    (a.val.1.1.val+a.val.1.2.val)+(a.val.2.1.val+a.val.2.2.val)+
      (a.val.1.2.val+a.val.2.2.val) ≤ 18 ∧
      a.val.1.2.val+a.val.2.2.val ≤ 9 := by
  have hc := (b4_two_letter_catalog_iff a.val.1 a.val.2).mp a.property
  have hQ := hc.1
  have hn := hc.2.2.1
  norm_num [Fin.sum_univ_four] at hQ hn
  omega
#print axioms Paper7MomentCanonicalNumeric.b4_type22_budget_bounds

end Paper7MomentCanonicalNumeric
