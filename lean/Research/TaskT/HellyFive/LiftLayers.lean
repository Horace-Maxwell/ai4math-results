import Research.TaskT.HellyFive.FiberProjection

namespace TaskT.HellyFive.Lift
open Set FiniteGeometry FiberProjection

private def bits (r : ℕ) : (Fin r → Bool) ↪ Grid r where
  toFun b i := if b i then 1 else 0
  inj' := by
    intro a b he
    funext i
    have hi := congrFun he i
    change (if a i then (1 : ℤ) else 0) = (if b i then 1 else 0) at hi
    cases ha : a i <;> cases hb : b i <;> simp_all

def plus (r : ℕ) : Finset (Grid r) := (Finset.univ.map (bits r)).erase 0

def minus (r : ℕ) : Finset (Grid r) := (plus r).image Neg.neg

theorem plus_spec {r : ℕ} {z : Grid r} : z ∈ plus r ↔ positiveCorner z := by
  simp only [plus,Finset.mem_erase,Finset.mem_map,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hn,b,rfl⟩
    refine ⟨hn,fun i => ?_⟩
    change (if b i then (1:ℤ) else 0) = 0 ∨ (if b i then (1:ℤ) else 0) = 1
    cases b i <;> decide
  · rintro ⟨hn,hz⟩
    refine ⟨hn,fun i => decide (z i = 1),?_⟩
    funext i
    change (if decide (z i = 1) then (1 : ℤ) else 0) = z i
    rcases hz i with h | h <;> simp [h]

theorem minus_spec {r : ℕ} {z : Grid r} : z ∈ minus r ↔ positiveCorner (-z) := by
  simp only [minus, Finset.mem_image]
  constructor
  · rintro ⟨a,ha,rfl⟩
    simpa using plus_spec.mp ha
  · intro h; exact ⟨-z,plus_spec.mpr h,neg_neg z⟩

theorem plus_card (r : ℕ) : (plus r).card = 2^r-1 := by
  have h0 : (0 : Grid r) ∈ Finset.univ.map (bits r) := by
    refine Finset.mem_map.mpr ⟨fun _ => false,Finset.mem_univ _,?_⟩
    rfl
  rw [plus,Finset.card_erase_of_mem h0,Finset.card_map]
  simp

theorem minus_card (r : ℕ) : (minus r).card = 2^r-1 := by
  rw [minus,Finset.card_image_of_injective _ neg_injective,plus_card]

def seeds (r : ℕ) : Finset (Grid 4 × Grid r) :=
  (WitnessFour.vertices ×ˢ {0}) ∪ (CorePositive.vertices ×ˢ plus r) ∪
    (CoreNegative.vertices ×ˢ minus r)

theorem seed_spec {r : ℕ} {x : Grid 4} {z : Grid r} : (x,z) ∈ seeds r ↔
    (x ∈ WitnessFour.vertices ∧ z=0) ∨
    (x ∈ CorePositive.vertices ∧ positiveCorner z) ∨
    (x ∈ CoreNegative.vertices ∧ positiveCorner (-z)) := by
  simp [seeds, plus_spec, minus_spec, eq_comm]

private theorem opposite {r : ℕ} {z : Grid r} (h : positiveCorner z)
    (hm : positiveCorner (-z)) : False := by
  apply h.1
  funext i
  have ha := h.2 i
  have hb := hm.2 i
  change -z i=0 ∨ -z i=1 at hb
  change z i = 0
  omega

theorem seed_card (r : ℕ) : (seeds r).card = 37+32*(2^r-1) := by
  let A := WitnessFour.vertices ×ˢ ({0}:Finset (Grid r))
  let B := CorePositive.vertices ×ˢ plus r
  let C := CoreNegative.vertices ×ˢ minus r
  have ab : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    rintro ⟨x,z⟩ ha hb
    have h : z=0 := Finset.mem_singleton.mp (Finset.mem_product.mp ha).2
    exact (plus_spec.mp (Finset.mem_product.mp hb).2).1 h
  have ac : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    rintro ⟨x,z⟩ ha hc
    have h : z=0 := Finset.mem_singleton.mp (Finset.mem_product.mp ha).2
    exact (minus_spec.mp (Finset.mem_product.mp hc).2).1 (by simp [h])
  have bc : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    rintro ⟨x,z⟩ hb hc
    exact opposite (plus_spec.mp (Finset.mem_product.mp hb).2) (minus_spec.mp (Finset.mem_product.mp hc).2)
  change ((A ∪ B) ∪ C).card = _
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨ac,bc⟩),
    Finset.card_union_of_disjoint ab]
  simp [A,B,C,WitnessFour.counts.1,CorePositive.counts.1,CoreNegative.counts.1,
    plus_card,minus_card]
  omega

def pairEmbed {r : ℕ} (v : Grid 4 × Grid r) : Space 4 × Space r := (embed v.1,embed v.2)

theorem pairEmbed_inj {r : ℕ} : Function.Injective (@pairEmbed r) := by
  intro a b h
  exact Prod.ext (embed_inj (congrArg Prod.fst h)) (embed_inj (congrArg Prod.snd h))

private theorem zero_embed {r : ℕ} : embed (0 : Grid r) = 0 := by ext i; simp [embed]

theorem seeds_extreme {r : ℕ} {v : Grid 4 × Grid r} (hv : v ∈ seeds r) :
    pairEmbed v ∈ (lifted r).extremePoints ℝ := by
  obtain ⟨x,z⟩ := v
  rcases seed_spec.mp hv with ⟨hx,rfl⟩ | ⟨hx,hz⟩ | ⟨hx,hz⟩
  · change (embed x,embed (0 : Grid r)) ∈ _
    rw [zero_embed]
    apply central_extreme
    rw [WitnessFour.geometry.1]
    exact ⟨x,hx,rfl⟩
  · apply positive_lattice_extreme hz
    exact (positive_fiber hz _).2 (positive_grid.mpr hx)
  · apply negative_lattice_extreme hz
    exact (negative_fiber hz _).2 (negative_grid.mpr hx)

private theorem lift_at {r : ℕ} (s : Finset (Grid 4)) (z : Space r)
    {D : Set (Space 4 × Space r)} (hD : Convex ℝ D)
    (hs : ∀ p ∈ s, (embed p,z) ∈ D) {x : Space 4} (hx : x ∈ poly s) : (x,z) ∈ D := by
  let f : Space 4 →ᵃ[ℝ] Space 4 × Space r := (AffineMap.id ℝ (Space 4)).prod (AffineMap.const ℝ _ z)
  apply convexHull_min (t := f ⁻¹' D) _ (hD.affine_preimage f) hx
  rintro _ ⟨p,hp,rfl⟩
  exact hs p hp

theorem hull_seeds (r : ℕ) :
    convexHull ℝ (pairEmbed '' (seeds r : Set (Grid 4 × Grid r))) = lifted r := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨v,hv,rfl⟩
    exact (seeds_extreme hv).1
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro ⟨x,z⟩ (⟨hx,hz⟩ | ⟨hx,t,ht,hz⟩ | ⟨hx,t,ht,hz⟩)
    · change z = 0 at hz; subst z
      apply lift_at _ _ (convex_convexHull ℝ _) _ hx
      intro p hp
      exact subset_convexHull ℝ _ ⟨(p,0),seed_spec.mpr (Or.inl ⟨hp,rfl⟩),Prod.ext rfl zero_embed⟩
    · change z = embed t at hz; subst z
      apply lift_at _ _ (convex_convexHull ℝ _) _ hx
      intro p hp
      exact subset_convexHull ℝ _ ⟨(p,t),seed_spec.mpr (Or.inr (Or.inl ⟨hp,ht⟩)),rfl⟩
    · change z = embed t at hz; subst z
      apply lift_at _ _ (convex_convexHull ℝ _) _ hx
      intro p hp
      exact subset_convexHull ℝ _ ⟨(p,t),seed_spec.mpr (Or.inr (Or.inr ⟨hp,ht⟩)),rfl⟩

theorem extreme_lifted_eq (r : ℕ) :
    (lifted r).extremePoints ℝ = pairEmbed '' (seeds r : Set (Grid 4 × Grid r)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rw [←hull_seeds]; exact extremePoints_convexHull_subset
  · rintro _ ⟨v,hv,rfl⟩
    exact seeds_extreme hv

end TaskT.HellyFive.Lift
