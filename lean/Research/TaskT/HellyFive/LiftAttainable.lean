import Research.TaskT.HellyFive.LiftLayers

namespace TaskT.HellyFive.Lift
open Set FiniteGeometry FiberProjection

def join {α : Type} (r : ℕ) : ((Fin 4 → α) × (Fin r → α)) ≃ (Fin (4+r) → α) where
  toFun v := Fin.append v.1 v.2
  invFun f := (fun i => f (Fin.castAdd r i), fun i => f (Fin.natAdd 4 i))
  left_inv v := Prod.ext (by funext i; exact Fin.append_left _ _ _) (by funext i; exact Fin.append_right _ _ _)
  right_inv _ := Fin.append_castAdd_natAdd

def joinReal (r : ℕ) : (Space 4 × Space r) ≃ₗ[ℝ] Space (4+r) where
  toEquiv := join r
  map_add' a b := by
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp [join,Fin.append_left,Fin.append_right]
  map_smul' a b := by
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp [join,Fin.append_left,Fin.append_right]

theorem join_embed {r : ℕ} (v : Grid 4 × Grid r) :
    joinReal r (pairEmbed v) = embed (join r v) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp [joinReal,join,embed,pairEmbed]

def latticeVertices (r : ℕ) : Finset (Grid (4+r)) := (seeds r).map (join r).toEmbedding

private theorem vertex_image (r : ℕ) :
    (joinReal r) '' (pairEmbed '' (seeds r : Set (Grid 4 × Grid r))) =
      embed '' (latticeVertices r : Set (Grid (4+r))) := by
  ext x
  constructor
  · rintro ⟨_,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨join r v, Finset.mem_map.mpr ⟨v,hv,rfl⟩,(join_embed v).symm⟩
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
    exact ⟨pairEmbed v,⟨v,hv,rfl⟩,join_embed v⟩

theorem joined_poly (r : ℕ) :
    poly (latticeVertices r) = (joinReal r) '' lifted r := by
  unfold poly
  rw [← hull_seeds, ← vertex_image]
  exact ((joinReal r).toLinearMap.image_convexHull _).symm

theorem joined_extreme (r : ℕ) :
    (poly (latticeVertices r)).extremePoints ℝ = embed '' (latticeVertices r : Set (Grid (4+r))) := by
  rw [joined_poly,← image_extremePoints,extreme_lifted_eq,vertex_image]

def centersJoined (r : ℕ) : Finset (Grid (4+r)) :=
  (WitnessFour.centers ×ˢ ({0} : Finset (Grid r))).map (join r).toEmbedding

theorem joined_nonvertex (r : ℕ) :
    {y : Grid (4+r) | embed y ∈ poly (latticeVertices r) ∧
      embed y ∉ (poly (latticeVertices r)).extremePoints ℝ} = (centersJoined r : Set _) := by
  ext y
  obtain ⟨⟨x,z⟩,rfl⟩ := (join (α := ℤ) r).surjective y
  change (embed (join r (x,z)) ∈ poly (latticeVertices r) ∧
    embed (join r (x,z)) ∉ (poly (latticeVertices r)).extremePoints ℝ) ↔ _
  rw [← join_embed,joined_poly,← image_extremePoints]
  simp only [(joinReal r).injective.mem_set_image]
  change ((embed x,embed z) ∈ lifted r ∧ (embed x,embed z) ∉ (lifted r).extremePoints ℝ) ↔ _
  rw [nonvertex_grid_iff]
  change _ ↔ join r (x,z) ∈ (WitnessFour.centers ×ˢ ({0} : Finset (Grid r))).map (join r).toEmbedding
  have eqm : (join r) (x,z) ∈ (WitnessFour.centers ×ˢ ({0} : Finset (Grid r))).map (join r).toEmbedding ↔
      (x,z) ∈ WitnessFour.centers ×ˢ ({0} : Finset (Grid r)) := Finset.mem_map' (join r).toEmbedding
  rw [eqm,Finset.mem_product,Finset.mem_singleton]
  tauto

theorem attainable_add (r : ℕ) : value (4+r) ∈ attainableCounts (4+r) := by
  refine ⟨latticeVertices r, ?_, ?_⟩
  · change ((poly _).extremePoints ℝ).encard = _
    rw [joined_extreme,Set.InjOn.encard_image embed_inj.injOn,Set.encard_coe_eq_coe_finsetCard]
    apply congrArg (fun t : ℕ => (t : ℕ∞))
    change ((seeds r).map _).card = _
    rw [Finset.card_map,seed_card]
    have hv : value (4+r) = 2^((4+r)+1)+5 := by
      simp [value, show 4+r≠1 by omega, show 4+r≠2 by omega, show 4+r≠3 by omega]
    rw [hv,show 4+r+1=r+5 by omega,pow_add]
    have hpos : 0 < 2^r := by positivity
    omega
  · change ({y : Grid (4+r) | embed y ∈ poly (latticeVertices r) ∧
        embed y ∉ (poly (latticeVertices r)).extremePoints ℝ} : Set _).encard = 5
    rw [joined_nonvertex,Set.encard_coe_eq_coe_finsetCard]
    simp [centersJoined,WitnessFour.counts.2]

theorem attainable_ge_four (n : ℕ) (hn : 4 ≤ n) : value n ∈ attainableCounts n := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hn
  exact attainable_add r

end TaskT.HellyFive.Lift
