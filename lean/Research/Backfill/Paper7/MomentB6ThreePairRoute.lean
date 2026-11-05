import Research.Backfill.Paper7.MomentB6TenComplete

/-! Original 2+2+2 candidate fibre, with three independently labelled positions.
The finite bounds below are consequences of the original budget. The sixteen
families are proposed conclusions, not assumptions on the original predicate. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6ThreePairRow (x : PQ 3) : PQ 6 :=
  (![x.1 0,x.1 1,x.1 2,x.1 0,x.1 1,x.1 2],
   ![x.2 0,x.2 1,x.2 2,x.2 0,x.2 1,x.2 2])
#print axioms Paper7MomentCounts.b6ThreePairRow

theorem b6ThreePairRow_features (x : PQ 3) :
    weight (b6ThreePairRow x) = 2 * weight x ∧
    qSum (b6ThreePairRow x) = 2 * qSum x ∧
    theta (b6ThreePairRow x) = 2 * theta x := by
  constructor
  · simp [b6ThreePairRow,weight,pSum,qSum,Fin.sum_univ_succ]
    ring
  constructor
  · simp [b6ThreePairRow,qSum,Fin.sum_univ_succ]
    ring
  · simp [b6ThreePairRow,theta,Fin.sum_univ_succ]
    ring
#print axioms Paper7MomentCounts.b6ThreePairRow_features

def B6ThreePairGuard (z : Fin 3 → ℕ) (Q : ℕ) : Prop :=
  0 < (∑ i,z i)+Q ∧ (∑ i,z i)+Q ≤ 18 ∧ Q ≤ ∑ i,z i ∧
    b6FeatureGuard (2*((∑ i,z i)+Q)) (2*Q)
      (12+6*((∑ i,z i : ℕ) : ℤ)+4*(Q : ℤ)+2*∑ i,(z i : ℤ)^2)
#print axioms Paper7MomentCounts.B6ThreePairGuard

theorem b6_three_pair_zq_accept (x : ZQCoordinates 3) :
    b6ThreePairRow (zqToPQ x) ∈ CandB1 6 42 ↔
      B6ThreePairGuard x.val.1 (∑ i,x.val.2 i) := by
  rw [b6_candB1_iff_guard]
  have hf := b6ThreePairRow_features (zqToPQ x)
  unfold b6CandidateGuard
  rw [hf.1,hf.2.1,hf.2.2,zq_weight,zq_qSum,zq_theta]
  have ht : 2 * ((6 : ℤ)+3*((∑ i,x.val.1 i : ℕ) : ℤ)+
      2*((∑ i,x.val.2 i : ℕ) : ℤ)+∑ i,(x.val.1 i : ℤ)^2) =
      12+6*((∑ i,x.val.1 i : ℕ) : ℤ)+4*((∑ i,x.val.2 i : ℕ) : ℤ)+
        2*∑ i,(x.val.1 i : ℤ)^2 := by ring
  norm_num only [Nat.cast_ofNat]
  rw [ht]
  have hQ : (∑ i,x.val.2 i) ≤ ∑ i,x.val.1 i :=
    Finset.sum_le_sum (fun i _ => x.property i)
  unfold B6ThreePairGuard
  constructor
  · rintro ⟨hp,hb,hg⟩
    exact ⟨by omega,by omega,hQ,hg⟩
  · rintro ⟨hp,hb,_,hg⟩
    exact ⟨by omega,by omega,hg⟩
#print axioms Paper7MomentCounts.b6_three_pair_zq_accept

theorem b6ThreePairGuard_comp_perm (z : Fin 3 → ℕ) (Q : ℕ)
    (e : Equiv.Perm (Fin 3)) : B6ThreePairGuard (z ∘ e) Q ↔ B6ThreePairGuard z Q := by
  have hZ := Equiv.sum_comp e z
  have hR := Equiv.sum_comp e (fun i => (z i : ℤ)^2)
  simp only [B6ThreePairGuard,Function.comp_apply,hZ,hR]
#print axioms Paper7MomentCounts.b6ThreePairGuard_comp_perm

def b6ThreePairReference : Fin 16 → Fin 3 → Fin 19 :=
  ![![5,0,0],![4,1,0],![9,0,0],![11,0,0],![11,0,0],![11,1,0],
    ![12,0,0],![12,1,0],![11,4,2],![12,0,0],![12,1,0],
    ![12,1,1],![12,2,0],![11,5,0],![9,8,0],![17,0,0]]
#print axioms Paper7MomentCounts.b6ThreePairReference

def b6ThreePairNat (j : Fin 16) (i : Fin 3) : ℕ := (b6ThreePairReference j i).val
#print axioms Paper7MomentCounts.b6ThreePairNat

def b6ThreePairQ : Fin 16 → ℕ := ![1,5,9,1,4,2,3,1,0,6,4,2,4,2,1,1]
#print axioms Paper7MomentCounts.b6ThreePairQ

def b6ThreePairSortedAccepted (a b c Q : ℕ) : Bool :=
  let Z := a+b+c
  let T : ℤ := 12+6*(Z : ℤ)+4*(Q : ℤ)+2*((a : ℤ)^2+(b : ℤ)^2+(c : ℤ)^2)
  decide (b ≤ a ∧ c ≤ b ∧ 0 < Z+Q ∧ Z+Q ≤ 18 ∧ Q ≤ Z) &&
    decide (∃ sm ∈ b6FeatureCatalog, sm.2 = T ∧
      sm.1 ≤ (6+2*(Z+Q) : ℤ) ∧ (6+2*(Z+Q) : ℤ)-max (2*Q : ℤ) 2 ≤ sm.1)
#print axioms Paper7MomentCounts.b6ThreePairSortedAccepted

def b6ThreePairSortedClassified (a b c Q : ℕ) : Bool :=
  decide (∃ j : Fin 16, b6ThreePairNat j = ![a,b,c] ∧ b6ThreePairQ j = Q)
#print axioms Paper7MomentCounts.b6ThreePairSortedClassified

theorem b6_three_pair_sorted_certificate_a0 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 0 b.val c.val Q.val =
        b6ThreePairSortedClassified 0 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a0

theorem b6_three_pair_sorted_certificate_a1 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 1 b.val c.val Q.val =
        b6ThreePairSortedClassified 1 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a1

theorem b6_three_pair_sorted_certificate_a2 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 2 b.val c.val Q.val =
        b6ThreePairSortedClassified 2 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a2

theorem b6_three_pair_sorted_certificate_a3 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 3 b.val c.val Q.val =
        b6ThreePairSortedClassified 3 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a3

theorem b6_three_pair_sorted_certificate_a4 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 4 b.val c.val Q.val =
        b6ThreePairSortedClassified 4 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a4

theorem b6_three_pair_sorted_certificate_a5 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 5 b.val c.val Q.val =
        b6ThreePairSortedClassified 5 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a5

theorem b6_three_pair_sorted_certificate_a6 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 6 b.val c.val Q.val =
        b6ThreePairSortedClassified 6 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a6

theorem b6_three_pair_sorted_certificate_a7 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 7 b.val c.val Q.val =
        b6ThreePairSortedClassified 7 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a7

theorem b6_three_pair_sorted_certificate_a8 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 8 b.val c.val Q.val =
        b6ThreePairSortedClassified 8 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a8

theorem b6_three_pair_sorted_certificate_a9 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 9 b.val c.val Q.val =
        b6ThreePairSortedClassified 9 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a9

theorem b6_three_pair_sorted_certificate_a10 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 10 b.val c.val Q.val =
        b6ThreePairSortedClassified 10 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a10

theorem b6_three_pair_sorted_certificate_a11 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 11 b.val c.val Q.val =
        b6ThreePairSortedClassified 11 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a11

theorem b6_three_pair_sorted_certificate_a12 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 12 b.val c.val Q.val =
        b6ThreePairSortedClassified 12 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a12

theorem b6_three_pair_sorted_certificate_a13 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 13 b.val c.val Q.val =
        b6ThreePairSortedClassified 13 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a13

theorem b6_three_pair_sorted_certificate_a14 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 14 b.val c.val Q.val =
        b6ThreePairSortedClassified 14 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a14

theorem b6_three_pair_sorted_certificate_a15 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 15 b.val c.val Q.val =
        b6ThreePairSortedClassified 15 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a15

theorem b6_three_pair_sorted_certificate_a16 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 16 b.val c.val Q.val =
        b6ThreePairSortedClassified 16 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a16

theorem b6_three_pair_sorted_certificate_a17 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 17 b.val c.val Q.val =
        b6ThreePairSortedClassified 17 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a17

theorem b6_three_pair_sorted_certificate_a18 :
    ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      b6ThreePairSortedAccepted 18 b.val c.val Q.val =
        b6ThreePairSortedClassified 18 b.val c.val Q.val := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate_a18

theorem b6_three_pair_sorted_certificate :
    ∀ a : Fin 19, ∀ b : Fin 10, ∀ c : Fin 7, ∀ Q : Fin 10,
      (b.val ≤ a.val ∧ c.val ≤ b.val ∧ B6ThreePairGuard ![a.val,b.val,c.val] Q.val) ↔
      ∃ j : Fin 16, b6ThreePairNat j = ![a.val,b.val,c.val] ∧ b6ThreePairQ j = Q.val := by
  have reflect (a b c Q : ℕ) : b6ThreePairSortedAccepted a b c Q = true ↔
      (b ≤ a ∧ c ≤ b ∧ B6ThreePairGuard ![a,b,c] Q) := by
    simp [b6ThreePairSortedAccepted,B6ThreePairGuard,b6FeatureGuard,Fin.sum_univ_succ,
      Bool.and_eq_true,decide_eq_true_eq,and_assoc,Nat.add_assoc,Int.add_assoc]
  intro a b c Q
  have certificate : b6ThreePairSortedAccepted a.val b.val c.val Q.val =
      b6ThreePairSortedClassified a.val b.val c.val Q.val := by
    fin_cases a
    · exact b6_three_pair_sorted_certificate_a0 b c Q
    · exact b6_three_pair_sorted_certificate_a1 b c Q
    · exact b6_three_pair_sorted_certificate_a2 b c Q
    · exact b6_three_pair_sorted_certificate_a3 b c Q
    · exact b6_three_pair_sorted_certificate_a4 b c Q
    · exact b6_three_pair_sorted_certificate_a5 b c Q
    · exact b6_three_pair_sorted_certificate_a6 b c Q
    · exact b6_three_pair_sorted_certificate_a7 b c Q
    · exact b6_three_pair_sorted_certificate_a8 b c Q
    · exact b6_three_pair_sorted_certificate_a9 b c Q
    · exact b6_three_pair_sorted_certificate_a10 b c Q
    · exact b6_three_pair_sorted_certificate_a11 b c Q
    · exact b6_three_pair_sorted_certificate_a12 b c Q
    · exact b6_three_pair_sorted_certificate_a13 b c Q
    · exact b6_three_pair_sorted_certificate_a14 b c Q
    · exact b6_three_pair_sorted_certificate_a15 b c Q
    · exact b6_three_pair_sorted_certificate_a16 b c Q
    · exact b6_three_pair_sorted_certificate_a17 b c Q
    · exact b6_three_pair_sorted_certificate_a18 b c Q
  rw [← reflect a.val b.val c.val Q.val,certificate]
  simp only [b6ThreePairSortedClassified,decide_eq_true_eq]
#print axioms Paper7MomentCounts.b6_three_pair_sorted_certificate

theorem b6ThreePairReference_accept : ∀ j : Fin 16,
    B6ThreePairGuard (b6ThreePairNat j) (b6ThreePairQ j) := by
  let accepted (j : Fin 16) : Bool :=
    let z := b6ThreePairNat j
    let Q := b6ThreePairQ j
    let Z := ∑ i,z i
    decide (0 < Z+Q ∧ Z+Q ≤ 18 ∧ Q ≤ Z) &&
      decide (∃ sm ∈ b6FeatureCatalog,
        sm.2 = 12+6*(Z : ℤ)+4*(Q : ℤ)+2*∑ i,(z i : ℤ)^2 ∧
        sm.1 ≤ (6+2*(Z+Q) : ℤ) ∧ (6+2*(Z+Q) : ℤ)-max (2*Q : ℤ) 2 ≤ sm.1)
  have cert : ∀ j, accepted j = true := by decide +kernel
  intro j
  simpa only [accepted,Bool.and_eq_true,decide_eq_true_eq,B6ThreePairGuard,
    b6FeatureGuard,and_assoc,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using cert j
#print axioms Paper7MomentCounts.b6ThreePairReference_accept

theorem b6_three_pair_guard_cover (z : Fin 3 → ℕ) (Q : ℕ)
    (h : B6ThreePairGuard z Q) :
    ∃ j : Fin 16, ∃ e : Equiv.Perm (Fin 3),
      z = b6ThreePairNat j ∘ e ∧ Q = b6ThreePairQ j := by
  let e := Tuple.sort (α := OrderDual ℕ) (fun i => (z i : OrderDual ℕ))
  have h10 := Tuple.monotone_sort (α := OrderDual ℕ)
    (fun i => (z i : OrderDual ℕ)) (show (0 : Fin 3) ≤ 1 by decide)
  change z (e 1) ≤ z (e 0) at h10
  have h21 := Tuple.monotone_sort (α := OrderDual ℕ)
    (fun i => (z i : OrderDual ℕ)) (show (1 : Fin 3) ≤ 2 by decide)
  change z (e 2) ≤ z (e 1) at h21
  have hs : z ∘ e = ![z (e 0),z (e 1),z (e 2)] := by
    funext i
    fin_cases i <;> rfl
  have hg := (b6ThreePairGuard_comp_perm z Q e).mpr h
  rw [hs] at hg
  have hb : z (e 0)+z (e 1)+z (e 2)+Q ≤ 18 := by
    simpa [Fin.sum_univ_succ,Nat.add_assoc] using hg.2.1
  have ha : z (e 0) < 19 := by omega
  have hbb : z (e 1) < 10 := by omega
  have hc : z (e 2) < 7 := by omega
  have hcap : Q ≤ z (e 0)+z (e 1)+z (e 2) := by
    simpa [Fin.sum_univ_succ,Nat.add_assoc] using hg.2.2.1
  have hQ : Q < 10 := by omega
  obtain ⟨j,hj,hq⟩ := (b6_three_pair_sorted_certificate
    ⟨_,ha⟩ ⟨_,hbb⟩ ⟨_,hc⟩ ⟨Q,hQ⟩).mp ⟨h10,h21,hg⟩
  refine ⟨j,e.symm,?_,hq.symm⟩
  funext i
  have hi := (congrFun hs (e.symm i)).trans (congrFun hj (e.symm i)).symm
  simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hi
#print axioms Paper7MomentCounts.b6_three_pair_guard_cover

end Paper7MomentCounts
