import Research.Backfill.Paper7.MomentB4PairInterval

/-! NEW SOURCE ONLY. Original [a,b,c,b] word constraints and sharp finite
coordinate bounds. The imported PairInterval module is itself pending. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_three_letter_catalog_iff (a b c : B4Letter) :
    decodeWord (![a,b,c,b] : Fin 4 → B4Letter) ∈ CandB1 4 41 ↔
      B4CatalogRowAccept
        (![a.1.val+a.2.val,b.1.val+b.2.val,c.1.val+c.2.val,b.1.val+b.2.val] : Fin 4 → ℕ)
        (a.2.val+2*b.2.val+c.2.val) := by
  let x : PQ 4 := decodeWord (![a,b,c,b] : Fin 4 → B4Letter)
  have hz : (fun i => x.1 i+x.2 i) =
      (![a.1.val+a.2.val,b.1.val+b.2.val,c.1.val+c.2.val,b.1.val+b.2.val] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hQ : qSum x = a.2.val+2*b.2.val+c.2.val := by
    norm_num [x,decodeWord,qSum,Fin.sum_univ_four]
    omega
  simpa only [hz,hQ] using b4_candidate_catalog_iff x
#print axioms Paper7MomentCanonicalNumeric.b4_three_letter_catalog_iff

theorem b4_type112_budget_bounds (w : B4Type112) :
    (w.val.1.1.val+w.val.1.2.val)+2*(w.val.2.1.1.val+w.val.2.1.2.val)+
      (w.val.2.2.1.val+w.val.2.2.2.val)+
      (w.val.1.2.val+2*w.val.2.1.2.val+w.val.2.2.2.val) ≤ 37 ∧
    w.val.1.2.val+2*w.val.2.1.2.val+w.val.2.2.2.val ≤ 18 ∧
    w.val.2.1.1.val+w.val.2.1.2.val ≤ 18 ∧ w.val.2.1.2.val ≤ 9 := by
  have hc := (b4_three_letter_catalog_iff w.val.1 w.val.2.1 w.val.2.2).mp w.property
  have hQ := hc.1
  have hn := hc.2.2.1
  norm_num [Fin.sum_univ_four] at hQ hn
  omega
#print axioms Paper7MomentCanonicalNumeric.b4_type112_budget_bounds

end Paper7MomentCanonicalNumeric
