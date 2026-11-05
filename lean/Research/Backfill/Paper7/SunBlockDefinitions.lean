import Research.Backfill.Paper7.SunGraphAdjacency

set_option autoImplicit false

noncomputable section

namespace Paper7Cleared

open BackfillPaper7.Challenge

abbrev ArmV (b : ℕ) (L : Fin b → List ℕ) : Type :=
  Σ k : Fin b, Σ j : Fin (L k).length, Fin ((L k).get j)

#print axioms Paper7Cleared.ArmV

def pathShift {K : Type*} [CommRing K] (x : K) (t : ℕ) : Matrix (Fin t) (Fin t) K :=
  fun i j => (if i = j then x else 0) -
    (if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0)

#print axioms Paper7Cleared.pathShift

def pendantShift {K : Type*} [CommRing K] (b : ℕ) (L : Fin b → List ℕ) (x : K) :
    Matrix (ArmV b L) (ArmV b L) K :=
  Matrix.blockDiagonal' fun k => Matrix.blockDiagonal' fun j => pathShift x ((L k).get j)

#print axioms Paper7Cleared.pendantShift

def attachment {K : Type*} [CommRing K] (b : ℕ) (L : Fin b → List ℕ) :
    Matrix (Fin b) (ArmV b L) K :=
  fun i a => if a.1 = i ∧ a.2.2.val = 0 then -1 else 0

#print axioms Paper7Cleared.attachment

def cycleShift {K : Type*} [CommRing K] (b : ℕ) (x : K) : Matrix (Fin b) (Fin b) K :=
  x • (1 : Matrix (Fin b) (Fin b) K) - (SimpleGraph.cycleGraph b).adjMatrix K

#print axioms Paper7Cleared.cycleShift

end Paper7Cleared
