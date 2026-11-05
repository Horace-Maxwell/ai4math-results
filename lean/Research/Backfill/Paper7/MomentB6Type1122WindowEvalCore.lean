import Research.Backfill.Paper7.MomentB6Type1122WindowArithmetic

/-! Uncompiled primitive arithmetic kernel for one exact1122 window term.
All evaluation definitions are ordinary computable definitions. Only proof
bodies use classical reasoning. No full fixed-type number is supplied. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6R1122EvalResidual (A B Q : ℕ) (M : ℤ) : ℤ :=
  2*M-24-6*(A : ℤ)-12*(B : ℤ)-4*(Q : ℤ)-(A : ℤ)^2-2*(B : ℤ)^2
#print axioms Paper7MomentCounts.b6R1122EvalResidual

def b6R1122EvalSquareE (D : ℕ) (R : ℤ) : ℕ :=
  Nat.sqrt ((R-(D : ℤ)^2).toNat/2)
#print axioms Paper7MomentCounts.b6R1122EvalSquareE

def b6R1122EvalSquareAccept (D B : ℕ) (R : ℤ) : Bool :=
  decide (0≤R-(D : ℤ)^2) &&
    decide ((R-(D : ℤ)^2).toNat%2=0) &&
    decide (b6R1122EvalSquareE D R^2=(R-(D : ℤ)^2).toNat/2) &&
    decide (b6R1122EvalSquareE D R≤B) &&
    decide (b6R1122EvalSquareE D R%2=B%2)
#print axioms Paper7MomentCounts.b6R1122EvalSquareAccept

def b6R1122EvalWeight (A B D E Q : ℕ) : ℕ :=
  (bif decide (D=0) then 1 else 2)*(bif decide (E=0) then 1 else 2)*
    ∑ t ∈ Finset.range (Q/2+1),
      (min ((A+D)/2) (Q-2*t)+1-((Q-2*t)-(A-D)/2))*
        (min ((B+E)/2) t+1-(t-(B-E)/2))
#print axioms Paper7MomentCounts.b6R1122EvalWeight

def b6R1122EvalAtom (A B Q : ℕ) (M : ℤ) (D : ℕ) : ℕ :=
  bif decide (A%2=D%2) then
    bif b6R1122EvalSquareAccept D B (b6R1122EvalResidual A B Q M) then
      b6R1122EvalWeight A B D
        (b6R1122EvalSquareE D (b6R1122EvalResidual A B Q M)) Q
    else 0
  else 0
#print axioms Paper7MomentCounts.b6R1122EvalAtom

def b6R1122EvalTerm (A B Q : ℕ) (M : ℤ) : ℕ :=
  ∑ D ∈ Finset.range (A+1),b6R1122EvalAtom A B Q M D
#print axioms Paper7MomentCounts.b6R1122EvalTerm

/-- A finite offset interval, with no hypothesis or assumed block value. -/
def b6R1122EvalChunk (A B Q : ℕ) (M : ℤ) (start width : ℕ) : ℕ :=
  ∑ k ∈ Finset.range width,b6R1122EvalAtom A B Q M (start+k)
#print axioms Paper7MomentCounts.b6R1122EvalChunk

theorem b6R1122EvalResidual_eq (A B Q : ℕ) (M : ℤ) :
    b6R1122EvalResidual A B Q M=b6Type1122WindowResidual A B Q M := rfl
#print axioms Paper7MomentCounts.b6R1122EvalResidual_eq

theorem b6R1122EvalSquareE_eq (D : ℕ) (R : ℤ) :
    b6R1122EvalSquareE D R=b6Type1122SquareE D R := rfl
#print axioms Paper7MomentCounts.b6R1122EvalSquareE_eq

theorem b6R1122EvalSquareAccept_iff (D B : ℕ) (R : ℤ) :
    b6R1122EvalSquareAccept D B R=true ↔ b6Type1122SquareTest D B R := by
  unfold b6R1122EvalSquareAccept b6Type1122SquareTest
  unfold b6R1122EvalSquareE b6Type1122SquareE
  simp only [Bool.and_eq_true,decide_eq_true_eq,and_assoc]
#print axioms Paper7MomentCounts.b6R1122EvalSquareAccept_iff

theorem b6R1122EvalWeight_eq (A B D E Q : ℕ) :
    b6R1122EvalWeight A B D E Q=b6Type1122WindowWeight A B D E Q := by
  unfold b6R1122EvalWeight b6Type1122WindowWeight
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ =>
    (min ((A+D)/2) (Q-2*t)+1-((Q-2*t)-(A-D)/2))*
      (min ((B+E)/2) t+1-(t-(B-E)/2))) (Q/2+1)]
  by_cases hD : D=0 <;> by_cases hE : E=0 <;>
    simp only [Bool.cond_eq_ite,decide_eq_true_eq,hD,hE,ite_true,ite_false]
#print axioms Paper7MomentCounts.b6R1122EvalWeight_eq

theorem b6R1122EvalAtom_eq (A B Q : ℕ) (M : ℤ) (D : ℕ) :
    b6R1122EvalAtom A B Q M D=
      if A%2=D%2 then
        if b6Type1122SquareTest D B (b6Type1122WindowResidual A B Q M) then
          b6Type1122WindowWeight A B D
            (b6Type1122SquareE D (b6Type1122WindowResidual A B Q M)) Q
        else 0
      else 0 := by
  classical
  unfold b6R1122EvalAtom
  simp only [b6R1122EvalResidual_eq]
  by_cases hp : A%2=D%2
  · have hb : decide (A%2=D%2)=true := decide_eq_true hp
    rw [Bool.cond_eq_ite,ite_eq_left hb,ite_eq_left hp]
    by_cases hs : b6Type1122SquareTest D B (b6Type1122WindowResidual A B Q M)
    · rw [Bool.cond_eq_ite,ite_eq_left ((b6R1122EvalSquareAccept_iff _ _ _).mpr hs),
        ite_eq_left hs,b6R1122EvalWeight_eq,b6R1122EvalSquareE_eq]
    · have hb' : ¬ b6R1122EvalSquareAccept D B
          (b6Type1122WindowResidual A B Q M)=true :=
        fun h => hs ((b6R1122EvalSquareAccept_iff _ _ _).mp h)
      rw [Bool.cond_eq_ite,ite_eq_right hb',ite_eq_right hs]
  · have hb : ¬ decide (A%2=D%2)=true := by
      simpa only [decide_eq_true_eq] using hp
    rw [Bool.cond_eq_ite,ite_eq_right hb,ite_eq_right hp]
#print axioms Paper7MomentCounts.b6R1122EvalAtom_eq

theorem b6R1122EvalTerm_eq (A B Q : ℕ) (M : ℤ) :
    b6R1122EvalTerm A B Q M=b6Type1122WindowTerm A B Q M := by
  classical
  unfold b6R1122EvalTerm b6Type1122WindowTerm
  rw [← Fin.sum_univ_eq_sum_range (fun D : ℕ => b6R1122EvalAtom A B Q M D) (A+1)]
  apply Finset.sum_congr rfl
  intro D _hD
  exact b6R1122EvalAtom_eq A B Q M D.val
#print axioms Paper7MomentCounts.b6R1122EvalTerm_eq

theorem b6R1122EvalChunk_add (A B Q : ℕ) (M : ℤ) (start m n : ℕ) :
    b6R1122EvalChunk A B Q M start (m+n)=
      b6R1122EvalChunk A B Q M start m+b6R1122EvalChunk A B Q M (start+m) n := by
  unfold b6R1122EvalChunk
  rw [Finset.sum_range_add]
  simp only [Nat.add_assoc]
#print axioms Paper7MomentCounts.b6R1122EvalChunk_add

theorem b6R1122EvalTerm_eq_chunks (A B Q : ℕ) (M : ℤ) (m n : ℕ)
    (h : m+n=A+1) :
    b6R1122EvalTerm A B Q M=
      b6R1122EvalChunk A B Q M 0 m+b6R1122EvalChunk A B Q M m n := by
  unfold b6R1122EvalTerm b6R1122EvalChunk
  rw [← h,Finset.sum_range_add]
  simp only [Nat.zero_add]
#print axioms Paper7MomentCounts.b6R1122EvalTerm_eq_chunks

/-- The genuine M84,Z7,B0,Q1 term: only D7 survives, with weight2. -/
theorem b6R1122EvalTerm_M84_Z7_B0_Q1 : b6R1122EvalTerm 7 0 1 84=2 := by
  with_unfolding_all decide
#print axioms Paper7MomentCounts.b6R1122EvalTerm_M84_Z7_B0_Q1

/-- The genuine M84,Z7,B0,Q7 term: only D5 survives, with weight2. -/
theorem b6R1122EvalTerm_M84_Z7_B0_Q7 : b6R1122EvalTerm 7 0 7 84=2 := by
  with_unfolding_all decide
#print axioms Paper7MomentCounts.b6R1122EvalTerm_M84_Z7_B0_Q7

end Paper7MomentCounts
