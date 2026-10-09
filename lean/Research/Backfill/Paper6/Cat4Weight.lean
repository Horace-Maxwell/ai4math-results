import Research.Backfill.Paper6.ChallengeV3

/-!
# Paper 6 V3: weight of a four-block concatenation

The proof first reindexes a sum on binary (n+1)-tuples by `Fin.snocEquiv`,
then applies that structural splitting to Hamming weight. Applying it twice
splits a 14-coordinate function into the four 12-coordinate blocks in the
exact order used by the frozen `cat4` definition. No truth-table enumeration
is needed.

Frozen manifest: statements-v3/FROZEN.json, SHA-256
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
This is a source draft for root-controlled compilation and acceptance.
-/

set_option autoImplicit false

namespace Paper6Cat4Weight

open BackfillPaper6.V3

/-- Split a sum over binary tuples according to the last coordinate. -/
theorem sum_points_snoc {n : ℕ} (f : Pt (n + 1) → ℕ) :
    (∑ y, f y) =
      (∑ x : Pt n, f (Fin.snoc x 0)) +
      (∑ x : Pt n, f (Fin.snoc x 1)) := by
  classical
  calc
    (∑ y, f y) =
        ∑ v : ZMod 2 × Pt n, f (Fin.snoc v.2 v.1) :=
      (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => ZMod 2))
        (fun v : ZMod 2 × Pt n => f (Fin.snoc v.2 v.1)) f
        (fun _ => rfl)).symm
    _ = ∑ b : ZMod 2, ∑ x : Pt n, f (Fin.snoc x b) :=
      Fintype.sum_prod_type _
    _ = _ := by
      rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
      simp

/-- Hamming weight is the sum of the weights of its two final-coordinate slices. -/
theorem hammingNorm_snoc {n : ℕ} (f : BFun (n + 1)) :
    hammingNorm f =
      hammingNorm (fun x : Pt n => f (Fin.snoc x 0)) +
      hammingNorm (fun x : Pt n => f (Fin.snoc x 1)) := by
  classical
  simp only [hammingNorm, Finset.card_filter]
  exact sum_points_snoc (fun y => if f y ≠ 0 then 1 else 0)

/-- Appending two coordinates leaves the frozen first-twelve-coordinate map unchanged. -/
theorem lo12_snoc_snoc (x : Pt 12) (a b : ZMod 2) :
    lo12 (Fin.snoc (Fin.snoc x a) b) = x := by
  funext i
  change (Fin.snoc (Fin.snoc x a : Pt 13) b : Pt 14) i.castSucc.castSucc = x i
  simp only [Fin.snoc_castSucc]

/-- Coordinate 12 is the first appended bit (the paper's x13). -/
theorem snoc_snoc_coord12 (x : Pt 12) (a b : ZMod 2) :
    (Fin.snoc (Fin.snoc x a : Pt 13) b : Pt 14) (12 : Fin 14) = a := by
  change (Fin.snoc (Fin.snoc x a : Pt 13) b : Pt 14) (Fin.last 12).castSucc = a
  rw [Fin.snoc_castSucc, Fin.snoc_last]

/-- Coordinate 13 is the second appended bit (the paper's x14). -/
theorem snoc_snoc_coord13 (x : Pt 12) (a b : ZMod 2) :
    (Fin.snoc (Fin.snoc x a : Pt 13) b : Pt 14) (13 : Fin 14) = b := by
  change (Fin.snoc (Fin.snoc x a : Pt 13) b : Pt 14) (Fin.last 13) = b
  rw [Fin.snoc_last]

/-- The four slices agree with the four arguments in the frozen coset order. -/
theorem cat4_snoc_snoc (f1 f2 f3 f4 : BFun 12)
    (x : Pt 12) (a b : ZMod 2) :
    cat4 f1 f2 f3 f4 (Fin.snoc (Fin.snoc x a) b) =
      if a = 0 then (if b = 0 then f1 x else f3 x)
      else (if b = 0 then f2 x else f4 x) := by
  simp only [cat4, snoc_snoc_coord12, snoc_snoc_coord13, lo12_snoc_snoc]

/-- Exact frozen four-block weight statement. -/
theorem cat4Weight : BackfillPaper6.V3.Cat4Weight := by
  intro f1 f2 f3 f4
  rw [hammingNorm_snoc (n := 13) (cat4 f1 f2 f3 f4),
    hammingNorm_snoc (n := 12)
      (fun x : Pt 13 => cat4 f1 f2 f3 f4 (Fin.snoc x 0)),
    hammingNorm_snoc (n := 12)
      (fun x : Pt 13 => cat4 f1 f2 f3 f4 (Fin.snoc x 1))]
  simp [cat4_snoc_snoc, add_assoc]

/-- Exact type check; this alias does not count as a second mathematical target. -/
theorem check_Cat4Weight : BackfillPaper6.V3.Cat4Weight := cat4Weight

end Paper6Cat4Weight

#print axioms Paper6Cat4Weight.sum_points_snoc
#print axioms Paper6Cat4Weight.hammingNorm_snoc
#print axioms Paper6Cat4Weight.lo12_snoc_snoc
#print axioms Paper6Cat4Weight.snoc_snoc_coord12
#print axioms Paper6Cat4Weight.snoc_snoc_coord13
#print axioms Paper6Cat4Weight.cat4_snoc_snoc
#print axioms Paper6Cat4Weight.cat4Weight
#print axioms Paper6Cat4Weight.check_Cat4Weight
#print Paper6Cat4Weight.check_Cat4Weight
