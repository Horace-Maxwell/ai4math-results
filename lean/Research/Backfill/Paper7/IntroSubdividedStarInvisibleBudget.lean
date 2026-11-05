import Research.Backfill.Paper7.IntroUnicyclicInvisibleFourthMoment

/-! Construct the actual leaf image of a subdivided star and prove that it
is invisible to walks of lengths zero, one and two from the cycle neighbour.
The resulting fourth-moment budget has no numerical moment or arm-count
hypothesis. All vertices and neighborhoods belong to the original graph. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroStarInvisible
open SimpleGraph Matrix BackfillPaper7.Challenge
open Paper7IntroTwoWalkCollision Paper7IntroPendantFour

theorem subdivided_star_leaf_image_invisible
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a c : V) (Y : Finset V) (leaf : Y → V)
    (hinj : Function.Injective leaf)
    (hca : c ≠ a) (hcY : ∀ i : Y, c ≠ i.val)
    (hcL : ∀ i : Y, c ≠ leaf i)
    (hNy : ∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a ∨ z = leaf i)
    (hNl : ∀ (i : Y) (z : V), G.Adj (leaf i) z ↔ z = i.val) :
    ((Finset.univ : Finset Y).image leaf).card = Y.card ∧
      ∀ l ∈ (Finset.univ : Finset Y).image leaf,
        l ≠ c ∧ ¬G.Adj c l ∧ ((G.adjMatrix ℝ) ^ 2) c l = 0 := by
  constructor
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
  · intro l hl
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hl
    have hci : ¬G.Adj c i.val := by
      intro h
      rcases (hNy i c).mp h.symm with h | h
      · exact hca h
      · exact hcL i h
    have hcl : ¬G.Adj c (leaf i) := by
      intro h
      exact hcY i ((hNl i c).mp h.symm)
    refine ⟨Ne.symm (hcL i), hcl, ?_⟩
    have hempty : (G.neighborFinset c).filter (fun x => G.Adj x (leaf i)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hxN, hxl⟩ := Finset.mem_filter.mp hx
      have hcx : G.Adj c x := (G.mem_neighborFinset c x).mp hxN
      have hxi : x = i.val := (hNl i x).mp hxl.symm
      exact hci (hxi ▸ hcx)
    rw [adjacency_square_common_card, hempty]
    norm_num
#print axioms Paper7IntroStarInvisible.subdivided_star_leaf_image_invisible

theorem unicyclic_subdivided_star_fourth_moment_budget
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (htriangle : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj k i → False)
    (a c : V) (Y : Finset V) (leaf : Y → V)
    (hinj : Function.Injective leaf)
    (hca : c ≠ a) (hcY : ∀ i : Y, c ≠ i.val)
    (hcL : ∀ i : Y, c ≠ leaf i)
    (hNy : ∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a ∨ z = leaf i)
    (hNl : ∀ (i : Y) (z : V), G.Adj (leaf i) z ↔ z = i.val) :
    ((G.adjMatrix ℝ) ^ 4) c c + (G.degree c : ℝ) + 1 + Y.card ≤
      (G.degree c : ℝ) ^ 2 + Fintype.card V + 3 := by
  obtain ⟨hcard, hE⟩ := subdivided_star_leaf_image_invisible G a c Y leaf hinj hca hcY hcL hNy hNl
  have hbudget := unicyclic_fourth_moment_invisible_bound G b hG htriangle c
    ((Finset.univ : Finset Y).image leaf) hE
  rw [hcard] at hbudget
  exact hbudget
#print axioms Paper7IntroStarInvisible.unicyclic_subdivided_star_fourth_moment_budget

end Paper7IntroStarInvisible
