import Research.Backfill.Paper7.MomentB6Type1122CatalogS9M72Certificate
import Research.Backfill.Paper7.MomentB6Type1122Catalog1384Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS17M96Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS16M240Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS20M252Certificate
import Research.Backfill.Paper7.MomentB6Type1122Catalog24264Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS25M312Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS29M324Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS33M336Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS34M384Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS38M396Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS42M408Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS25M600Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS29M612Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS33M624Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS34M672Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS38M684Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS42M696Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS41M840Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS36M1260Certificate
import Research.Backfill.Paper7.MomentB6Type1122CatalogS40M1272Certificate

/-! Aggregate of the21 actual certified catalogue-block Value constants.
No block numeral or total is supplied. Future Lean reduction targets only the
small sum of the certified constants, never the original large block functions.
The original reflection count is transported through the pointwise kernel
certificates and the original finite catalogue. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6R1122CertifiedCatalogValue (sm : ℤ × ℤ) : ℕ :=
  if sm = (9,72) then b6R1122CatalogS9M72Value else
  if sm = (13,84) then b6R1122Catalog1384Value else
  if sm = (17,96) then b6R1122CatalogS17M96Value else
  if sm = (16,240) then b6R1122CatalogS16M240Value else
  if sm = (20,252) then b6R1122CatalogS20M252Value else
  if sm = (24,264) then b6R1122Catalog24264Value else
  if sm = (25,312) then b6R1122CatalogS25M312Value else
  if sm = (29,324) then b6R1122CatalogS29M324Value else
  if sm = (33,336) then b6R1122CatalogS33M336Value else
  if sm = (34,384) then b6R1122CatalogS34M384Value else
  if sm = (38,396) then b6R1122CatalogS38M396Value else
  if sm = (42,408) then b6R1122CatalogS42M408Value else
  if sm = (25,600) then b6R1122CatalogS25M600Value else
  if sm = (29,612) then b6R1122CatalogS29M612Value else
  if sm = (33,624) then b6R1122CatalogS33M624Value else
  if sm = (34,672) then b6R1122CatalogS34M672Value else
  if sm = (38,684) then b6R1122CatalogS38M684Value else
  if sm = (42,696) then b6R1122CatalogS42M696Value else
  if sm = (41,840) then b6R1122CatalogS41M840Value else
  if sm = (36,1260) then b6R1122CatalogS36M1260Value else
  if sm = (40,1272) then b6R1122CatalogS40M1272Value else
  0
#print axioms Paper7MomentCounts.b6R1122CertifiedCatalogValue

theorem b6R1122EvalCatalogBlock_eq_certified (sm : ℤ × ℤ)
    (hsm : sm ∈ b6R1122EvalCatalog) :
    b6R1122EvalCatalogBlock sm=b6R1122CertifiedCatalogValue sm := by
  simp only [b6R1122EvalCatalog,Finset.mem_insert,Finset.mem_singleton] at hsm
  rcases hsm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS9M72_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122Catalog1384_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS17M96_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS16M240_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS20M252_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122Catalog24264_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS25M312_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS29M324_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS33M336_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS34M384_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS38M396_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS42M408_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS25M600_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS29M612_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS33M624_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS34M672_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS38M684_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS42M696_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS41M840_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS36M1260_eval_checked
  · simpa [b6R1122CertifiedCatalogValue] using b6R1122CatalogS40M1272_eval_checked
#print axioms Paper7MomentCounts.b6R1122EvalCatalogBlock_eq_certified

def b6R1122CertifiedTotal : ℕ :=
  ∑ sm ∈ b6R1122EvalCatalog,b6R1122CertifiedCatalogValue sm
#print axioms Paper7MomentCounts.b6R1122CertifiedTotal

theorem b6R1122EvalTotal_eq_certifiedTotal :
    b6R1122EvalTotal=b6R1122CertifiedTotal := by
  unfold b6R1122EvalTotal b6R1122CertifiedTotal
  exact Finset.sum_congr rfl (fun sm hsm => b6R1122EvalCatalogBlock_eq_certified sm hsm)
#print axioms Paper7MomentCounts.b6R1122EvalTotal_eq_certifiedTotal

def b6R1122TotalValue : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6R1122CertifiedTotal)) (some (Lean.mkConst ``Nat))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let some n ← Lean.Meta.withTransparency .all <|
        Lean.Meta.withNatValue v (fun n => pure (some n))
      | throwError "Closed certified-sum numeral was not recognized; reduced expression: {v}"
    Lean.Elab.Tactic.closeMainGoal `b6R1122TotalValue (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6R1122TotalValue
#print Paper7MomentCounts.b6R1122TotalValue

theorem b6R1122CertifiedTotal_eq_totalValue :
    b6R1122CertifiedTotal=b6R1122TotalValue := by
  with_unfolding_all rfl
#print axioms Paper7MomentCounts.b6R1122CertifiedTotal_eq_totalValue

end Paper7MomentCounts
namespace Paper7MomentCanonicalSix
open Paper7MomentCounts

theorem b6_reflection_zero_count_eq_totalValue :
    b6FixedCount (b6Reflection 0)=b6R1122TotalValue :=
  b6_reflection_zero_count_eq_eval_total.trans
    (b6R1122EvalTotal_eq_certifiedTotal.trans b6R1122CertifiedTotal_eq_totalValue)
#print axioms Paper7MomentCanonicalSix.b6_reflection_zero_count_eq_totalValue

end Paper7MomentCanonicalSix
