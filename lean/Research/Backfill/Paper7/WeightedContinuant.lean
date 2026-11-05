import Research.Backfill.Paper7.AlgebraicContracts

set_option autoImplicit false
noncomputable section
namespace Paper7Schwenk
open Polynomial BackfillPaper7.Challenge.Legacy.Algebra

/-- Each pair records the diagonal R and its row's arm factor L. -/
def continuant {K : Type*} [CommRing K] : List (K × K) → K
  | [] => 1
  | [a] => a.1
  | a :: b :: t => a.1 * continuant (b :: t) - a.2 * b.2 * continuant t
#print axioms Paper7Schwenk.continuant

def continuantBoundary {K : Type*} [CommRing K] : List (K × K) → K
  | [] => 0
  | a :: t => a.2 * continuant t
#print axioms Paper7Schwenk.continuantBoundary

def continuantStep {K : Type*} [CommRing K] (s a : K × K) : K × K :=
  (a.1 * s.1 - a.2 * s.2, a.2 * s.1)
#print axioms Paper7Schwenk.continuantStep

theorem continuant_foldl {K : Type*} [CommRing K] (a : List (K × K)) (A B : K) :
    (a.foldl continuantStep (A,B)).1 = A * continuant a - B * continuantBoundary a := by
  induction a generalizing A B with
  | nil => simp [continuant, continuantBoundary]
  | cons c t ih =>
    rw [List.foldl_cons]
    change (t.foldl continuantStep (c.1*A-c.2*B, c.2*A)).1 = _
    rw [ih]
    cases t with
    | nil => simp [continuant, continuantBoundary]; ring
    | cons d t => simp only [continuant, continuantBoundary]; ring
#print axioms Paper7Schwenk.continuant_foldl

def legData (a : ℕ × ℕ) : Polynomial ℤ × Polynomial ℤ :=
  (rootedLegPolynomial a.1 a.2, legPolynomial a.1 a.2)
#print axioms Paper7Schwenk.legData

theorem foldl_legData (a : List (ℕ × ℕ)) (s : Polynomial ℤ × Polynomial ℤ) :
    (a.map legData).foldl continuantStep s = a.foldl chainStep s := by
  induction a generalizing s with
  | nil => rfl
  | cons c t ih =>
    simp only [List.map_cons, List.foldl_cons]
    exact ih (chainStep s c)
#print axioms Paper7Schwenk.foldl_legData

theorem chainPolynomial_eq_continuant (a : List (ℕ × ℕ)) :
    chainPolynomial a = continuant (a.map legData) := by
  have h := continuant_foldl (a.map legData) (1 : Polynomial ℤ) 0
  rw [foldl_legData] at h
  simpa only [one_mul, zero_mul, sub_zero, chainPolynomial] using h
#print axioms Paper7Schwenk.chainPolynomial_eq_continuant

theorem continuant_map {K R : Type*} [CommRing K] [CommRing R]
    (f : K →+* R) (a : List (K × K)) :
    f (continuant a) = continuant (a.map (fun z => (f z.1, f z.2))) := by
  induction a using List.twoStepInduction with
  | nil => simp [continuant]
  | singleton a => simp [continuant]
  | cons_cons a b t iht ihcons =>
    simp only [continuant, List.map_cons, map_sub, map_mul]
    rw [ihcons b, iht]
    rfl
#print axioms Paper7Schwenk.continuant_map

end Paper7Schwenk
