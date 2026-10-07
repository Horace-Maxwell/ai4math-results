import Research.Backfill.Paper5.Proof.AssocGeometry

set_option autoImplicit false

namespace CodexPaper5.AssocMain

open BackfillPaper5

/-- The specified search depends only on the complete outer reachability relation.
The same ordered list and the same default point are used on both sides. -/
theorem dmul_congr_outer {n : ℕ}
    (a b c d : Challenge.Pt n → Challenge.Pt n)
    (h : ∀ p q : Challenge.Pt n,
      (Challenge.stackGraph a b).Reachable (Challenge.outer p) (Challenge.outer q) ↔
      (Challenge.stackGraph c d).Reachable (Challenge.outer p) (Challenge.outer q)) :
    Challenge.dmul a b = Challenge.dmul c d := by
  funext p
  have hpred :
      (fun q : Challenge.Pt n => decide (q ≠ p ∧
        (Challenge.stackGraph a b).Reachable (Challenge.outer p) (Challenge.outer q))) =
      (fun q : Challenge.Pt n => decide (q ≠ p ∧
        (Challenge.stackGraph c d).Reachable (Challenge.outer p) (Challenge.outer q))) := by
    funext q
    exact Bool.decide_congr (and_congr Iff.rfl (h p q))
  exact congrArg (fun pred : Challenge.Pt n → Bool =>
    ((Challenge.ptList n).find? pred).getD p) hpred

theorem check_PBAssociativity :
    CodexPaper5.AssociativityStatement.PBAssociativity := by
  intro n x y z hx hy hz
  apply dmul_congr_outer
  intro p q
  exact AssocGeometry.check_OuterBracketReachability n x y z hx hy hz p q

theorem check_BAssociativity :
    CodexPaper5.AssociativityStatement.BAssociativity := by
  intro n x y z hx hy hz
  exact check_PBAssociativity n x y z hx.1 hy.1 hz.1

/-- The actual frozen PB carrier, with its actual product and identity. -/
@[instance_reducible]
def pbMonoid (n : ℕ) : Monoid ↥(Challenge.Dset Challenge.Fam.PB n) where
  mul a b := ⟨Challenge.dmul a.val b.val,
    DiagramProduct.dmul_isPB a.property b.property⟩
  one := ⟨Challenge.idD n, DiagramUnits.idD_mem_PB n⟩
  mul_assoc a b c := by
    apply Subtype.ext
    change Challenge.dmul (Challenge.dmul a.val b.val) c.val =
      Challenge.dmul a.val (Challenge.dmul b.val c.val)
    exact check_PBAssociativity n a.val b.val c.val a.property b.property c.property
  one_mul a := by
    apply Subtype.ext
    change Challenge.dmul (Challenge.idD n) a.val = a.val
    exact DiagramUnits.dmul_id_left a.val a.property
  mul_one a := by
    apply Subtype.ext
    change Challenge.dmul a.val (Challenge.idD n) = a.val
    exact DiagramUnits.dmul_id_right a.val a.property

/-- The actual frozen B carrier; no global PB instance is installed. -/
@[instance_reducible]
def bMonoid (n : ℕ) : Monoid ↥(Challenge.Dset Challenge.Fam.B n) where
  mul a b := ⟨Challenge.dmul a.val b.val,
    DiagramProduct.dmul_mem_B a.property b.property⟩
  one := ⟨Challenge.idD n, DiagramUnits.idD_mem_B n⟩
  mul_assoc a b c := by
    apply Subtype.ext
    change Challenge.dmul (Challenge.dmul a.val b.val) c.val =
      Challenge.dmul a.val (Challenge.dmul b.val c.val)
    exact check_BAssociativity n a.val b.val c.val a.property b.property c.property
  one_mul a := by
    apply Subtype.ext
    change Challenge.dmul (Challenge.idD n) a.val = a.val
    exact DiagramUnits.dmul_id_left a.val a.property.1
  mul_one a := by
    apply Subtype.ext
    change Challenge.dmul a.val (Challenge.idD n) = a.val
    exact DiagramUnits.dmul_id_right a.val a.property.1

theorem pbMonoid_mul_val (n : ℕ)
    (a b : ↥(Challenge.Dset Challenge.Fam.PB n)) :
    (@Mul.mul ↥(Challenge.Dset Challenge.Fam.PB n) (pbMonoid n).toMul a b).val =
      Challenge.dmul a.val b.val := rfl

theorem pbMonoid_one_val (n : ℕ) :
    (@One.one ↥(Challenge.Dset Challenge.Fam.PB n) (pbMonoid n).toOne).val =
      Challenge.idD n := rfl

theorem bMonoid_mul_val (n : ℕ)
    (a b : ↥(Challenge.Dset Challenge.Fam.B n)) :
    (@Mul.mul ↥(Challenge.Dset Challenge.Fam.B n) (bMonoid n).toMul a b).val =
      Challenge.dmul a.val b.val := rfl

theorem bMonoid_one_val (n : ℕ) :
    (@One.one ↥(Challenge.Dset Challenge.Fam.B n) (bMonoid n).toOne).val =
      Challenge.idD n := rfl

theorem check_PBMonoidAligned :
    CodexPaper5.AssociativityStatement.PBMonoidAligned := by
  intro n
  refine ⟨pbMonoid n, ?_, ?_⟩
  · intro a b
    exact pbMonoid_mul_val n a b
  · exact pbMonoid_one_val n

theorem check_BMonoidAligned :
    CodexPaper5.AssociativityStatement.BMonoidAligned := by
  intro n
  refine ⟨bMonoid n, ?_, ?_⟩
  · intro a b
    exact bMonoid_mul_val n a b
  · exact bMonoid_one_val n

end CodexPaper5.AssocMain

#print axioms CodexPaper5.AssocMain.dmul_congr_outer
#print axioms CodexPaper5.AssocMain.check_PBAssociativity
#print axioms CodexPaper5.AssocMain.check_BAssociativity
#print axioms CodexPaper5.AssocMain.pbMonoid
#print axioms CodexPaper5.AssocMain.bMonoid
#print axioms CodexPaper5.AssocMain.pbMonoid_mul_val
#print axioms CodexPaper5.AssocMain.pbMonoid_one_val
#print axioms CodexPaper5.AssocMain.bMonoid_mul_val
#print axioms CodexPaper5.AssocMain.bMonoid_one_val
#print axioms CodexPaper5.AssocMain.check_PBMonoidAligned
#print axioms CodexPaper5.AssocMain.check_BMonoidAligned
