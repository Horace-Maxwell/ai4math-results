import Research.Backfill.Paper7.RepresentativeG13
import Research.Backfill.Paper7.RepresentativeG20a
import Research.Backfill.Paper7.RepresentativeG20b
import Research.Backfill.Paper7.ControlC42Ten
import Research.Backfill.Paper7.GraphIsoIntegral

/-! The complete reverse direction of the original b=4,N=49 control.
All characteristic factors are retained. This does not classify other graphs. -/
set_option autoImplicit false
noncomputable section
namespace Paper7ControlB4
open Polynomial BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7ThreeRepresentatives Paper7Control44

def g13IntegerRoots : List ℤ := List.replicate 9 0 ++ [2, -2, 3, -3]
#print axioms Paper7ControlB4.g13IntegerRoots

def g20IntegerRoots : List ℤ :=
  List.replicate 2 0 ++ List.replicate 7 1 ++
    List.replicate 7 (-1) ++ [2, -2, 3, -3]
#print axioms Paper7ControlB4.g20IntegerRoots

theorem g13_root_product :
    (g13IntegerRoots.map (fun z => X - C z)).prod =
      X ^ 9 * (X ^ 2 - 4) * (X ^ 2 - 9) := by
  have h4 : (X ^ 2 - 4 : Polynomial ℤ) = (X - 2) * (X + 2) := by ring
  have h9 : (X ^ 2 - 9 : Polynomial ℤ) = (X - 3) * (X + 3) := by ring
  rw [h4, h9]
  simp only [g13IntegerRoots, List.map_append, List.prod_append,
    List.map_replicate, List.prod_replicate]
  norm_num
  simp only [mul_assoc]
#print axioms Paper7ControlB4.g13_root_product

theorem g20_root_product :
    (g20IntegerRoots.map (fun z => X - C z)).prod =
      X ^ 2 * (X ^ 2 - 1) ^ 7 * (X ^ 2 - 4) * (X ^ 2 - 9) := by
  have h1 : (X ^ 2 - 1 : Polynomial ℤ) = (X - 1) * (X + 1) := by ring
  have h4 : (X ^ 2 - 4 : Polynomial ℤ) = (X - 2) * (X + 2) := by ring
  have h9 : (X ^ 2 - 9 : Polynomial ℤ) = (X - 3) * (X + 3) := by ring
  rw [h1, h4, h9, mul_pow]
  simp only [g20IntegerRoots, List.map_append, List.prod_append,
    List.map_replicate, List.prod_replicate]
  norm_num
  exact control_factor_blocks (X ^ 2) ((X - 1) ^ 7) ((X + 1) ^ 7)
    (X - 2) (X + 2) (X - 3) (X + 3)
#print axioms Paper7ControlB4.g20_root_product

theorem g13_integral : IsIntegralGraph (sunGraph 4 G13) :=
  integral_of_integer_factor_list (sunGraph 4 G13) g13IntegerRoots
    (g13_graphPhi.trans g13_root_product.symm)
#print axioms Paper7ControlB4.g13_integral

theorem g20a_integral : IsIntegralGraph (sunGraph 4 G20a) :=
  integral_of_integer_factor_list (sunGraph 4 G20a) g20IntegerRoots
    (g20a_graphPhi.trans g20_root_product.symm)
#print axioms Paper7ControlB4.g20a_integral

theorem g20b_integral : IsIntegralGraph (sunGraph 4 G20b) :=
  integral_of_integer_factor_list (sunGraph 4 G20b) g20IntegerRoots
    (g20b_graphPhi.trans g20_root_product.symm)
#print axioms Paper7ControlB4.g20b_integral

/-- Exactly the four graph-isomorphism alternatives of the frozen contract. -/
def FourNamed {V : Type} (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g sunGraph 4 G13) ∨
  Nonempty (G ≃g sunGraph 4 G20a) ∨
  Nonempty (G ≃g sunGraph 4 G20b) ∨
  Nonempty (G ≃g sunGraph 4 C42Ten)
#print axioms Paper7ControlB4.FourNamed

theorem fourNamed_iso_iff {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : G ≃g H) : FourNamed G ↔ FourNamed H := by
  unfold FourNamed
  constructor
  · rintro (⟨f⟩ | ⟨f⟩ | ⟨f⟩ | ⟨f⟩)
    · exact Or.inl ⟨e.symm.trans (Classical.choice f)⟩
    · exact Or.inr (Or.inl ⟨e.symm.trans (Classical.choice f)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans (Classical.choice f)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨e.symm.trans (Classical.choice f)⟩))
  · rintro (⟨f⟩ | ⟨f⟩ | ⟨f⟩ | ⟨f⟩)
    · exact Or.inl ⟨e.trans (Classical.choice f)⟩
    · exact Or.inr (Or.inl ⟨e.trans (Classical.choice f)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e.trans (Classical.choice f)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨e.trans (Classical.choice f)⟩))
#print axioms Paper7ControlB4.fourNamed_iso_iff

theorem fourNamed_integral {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : FourNamed G) : IsIntegralGraph G := by
  unfold FourNamed at h
  rcases h with ⟨e⟩ | ⟨e⟩ | ⟨e⟩ | ⟨e⟩
  · exact Paper7Normalize.graphIso_integral (sunGraph 4 G13) G (Classical.choice e).symm g13_integral
  · exact Paper7Normalize.graphIso_integral (sunGraph 4 G20a) G (Classical.choice e).symm g20a_integral
  · exact Paper7Normalize.graphIso_integral (sunGraph 4 G20b) G (Classical.choice e).symm g20b_integral
  · exact Paper7Normalize.graphIso_integral (sunGraph 4 C42Ten) G (Classical.choice e).symm control_integral
#print axioms Paper7ControlB4.fourNamed_integral

/-- Full reverse implication, requiring neither a size restriction nor a
positive-pendant hypothesis. The original forward direction remains G1. -/
theorem control_b4_reverse (L : Fin 4 → List ℕ) :
    (Nonempty (sunGraph 4 L ≃g sunGraph 4 G13) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 G20a) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 G20b) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 C42Ten)) →
    IsIntegralGraph (sunGraph 4 L) := fourNamed_integral (sunGraph 4 L)
#print axioms Paper7ControlB4.control_b4_reverse

end Paper7ControlB4
