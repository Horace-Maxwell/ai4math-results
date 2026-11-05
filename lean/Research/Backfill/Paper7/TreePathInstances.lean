import Research.Backfill.Paper7.SchwenkAcyclicStep

/-! Explicit instance transport. Finite enumeration and decision procedures
are subsingleton data; these lemmas transport them by proved equality rather
than asking elaboration to normalize determinant and adjacency expressions. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicSchwenk
open SimpleGraph BackfillPaper7.Challenge.Legacy.Algebra

abbrev explicitGraphCofactor {V : Type} (f : Fintype V) (d : DecidableEq V)
    (G : SimpleGraph V) (a : DecidableRel G.Adj) (v u : V) : Polynomial ℤ :=
  letI : Fintype V := f
  letI : DecidableEq V := d
  letI : DecidableRel G.Adj := a
  (Matrix.charmatrix (G.adjMatrix ℤ)).adjugate v u
#print axioms Paper7UnicyclicSchwenk.explicitGraphCofactor

theorem graphCofactor_instances_eq {V : Type} (f₁ f₂ : Fintype V)
    (d₁ d₂ : DecidableEq V) (G : SimpleGraph V)
    (a₁ a₂ : DecidableRel G.Adj) (v u : V) :
    explicitGraphCofactor f₁ d₁ G a₁ v u = explicitGraphCofactor f₂ d₂ G a₂ v u := by
  have hf : f₁ = f₂ := Subsingleton.elim _ _
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  have ha : a₁ = a₂ := Subsingleton.elim _ _
  cases hf
  cases hd
  cases ha
  rfl
#print axioms Paper7UnicyclicSchwenk.graphCofactor_instances_eq

theorem graphPhi_instances_eq {V : Type} (f₁ f₂ : Fintype V)
    (d₁ d₂ : DecidableEq V) (G : SimpleGraph V) :
    @graphPhi V f₁ d₁ G = @graphPhi V f₂ d₂ G := by
  have hf : f₁ = f₂ := Subsingleton.elim _ _
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hf
  cases hd
  rfl
#print axioms Paper7UnicyclicSchwenk.graphPhi_instances_eq

end Paper7UnicyclicSchwenk
