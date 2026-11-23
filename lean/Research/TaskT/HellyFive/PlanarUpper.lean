import Research.TaskT.HellyFive.PlanarTable
import Research.TaskT.HellyFive.PlanarObstruction
import Research.TaskT.HellyFive.UpperGeom

namespace TaskT.HellyFive.PlanarUpper
open UpperFive FiniteGeometry
open scoped BigOperators

theorem count_five {s X : Finset (Grid 2)} (incl : X ⊆ s) (hk : X.card ≤ 5)
    (cl : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → sameParity a b → gridMid a b ∈ X) :
    s.card ≤ 12 := by
  classical
  by_cases h5 : X.card = 5
  · let e₀ : Fin 5 ≃ X := (Fintype.equivFinOfCardEq (by simpa using h5)).symm
    let e : Fin 5 ↪ Grid 2 := e₀.toEmbedding.trans (Function.Embedding.subtype _)
    let f : Fin 5 → Color 2 := fun i => residue (e i)
    have hi : Finset.univ.map e = X := by
      ext p
      constructor
      · intro hp
        obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hp
        exact (e₀ i).property
      · intro hp
        exact Finset.mem_map.mpr ⟨e₀.symm ⟨p,hp⟩, Finset.mem_univ _, congrArg Subtype.val (e₀.apply_symm_apply ⟨p,hp⟩)⟩
    have hf (r : Color 2) : PlanarData.freq f r = (fiber X r).card := by
      rw [← hi]
      simp only [fiber,Finset.filter_map,Finset.card_map]
      rfl
    have each (r : Color 2) : (fiber s r).card ≤ PlanarData.cap f r := by
      apply card_le_capacity _ (indexedWeight_le_ten f r)
      exact (charge r cl).trans_eq (hi ▸ weight_map e r)
    have total := Finset.sum_le_sum (s := Finset.univ) (fun r _ => each r)
    rw [← card_sum_fibers] at total
    rcases PlanarData.classify f with bound | ⟨bound,lo,big,small⟩
    · exact total.trans bound
    · by_contra! hbad
      have eqcap (r : Color 2) : (fiber s r).card = PlanarData.cap f r := by
        apply le_antisymm (each r)
        by_contra! lt
        have hlt := Finset.sum_lt_sum (s := Finset.univ)
          (fun a _ => each a) ⟨r,Finset.mem_univ _,lt⟩
        rw [← card_sum_fibers] at hlt
        omega
      apply PlanarObstruction.obstruction incl h5 cl (fun r => hf r ▸ small r)
        (fun r => (eqcap r).symm ▸ lo r)
      obtain ⟨r,hr⟩ := big
      exact ⟨r,(eqcap r).symm ▸ hr⟩
  · have h4 : X.card ≤ 4 := by omega
    have htot := all_dimensional_bound cl
    have hC : X.card.choose 3 ≤ 4 := (Nat.choose_le_choose 3 h4).trans_eq (by decide)
    omega

theorem upper (V : Finset (Grid 2)) (hk : (otherGrid V).ncard ≤ 5) :
    ((poly V).extremePoints ℝ).ncard + (otherGrid V).ncard ≤ 12 := by
  classical
  rw [card_decomposition]
  let s := (allGrid_finite V).toFinset
  let X := (otherGrid_finite V).toFinset
  have es : (allGrid V).ncard = s.card := Set.ncard_eq_toFinset_card _ _
  have ex : (otherGrid V).ncard = X.card := Set.ncard_eq_toFinset_card _ _
  rw [es]
  apply count_five (X := X)
  · intro z hz
    exact (allGrid_finite V).mem_toFinset.mpr ((otherGrid_finite V).mem_toFinset.mp hz).1
  · exact ex ▸ hk
  · intro a ha b hb hab h
    exact (otherGrid_finite V).mem_toFinset.mpr <| gridMid_mem_nonvertices
      (convex_convexHull ℝ _) ((allGrid_finite V).mem_toFinset.mp ha)
      ((allGrid_finite V).mem_toFinset.mp hb) hab h

end TaskT.HellyFive.PlanarUpper
