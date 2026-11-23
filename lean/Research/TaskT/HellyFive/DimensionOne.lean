import Research.TaskT.HellyFive.FiniteGeometry

namespace TaskT.HellyFive.DimensionOne
open Set FiniteGeometry

def pt (z : ℤ) : Grid 1 := fun _ => z

theorem one_ext {α : Type*} {x y : Fin 1 → α} (h : x 0 = y 0) : x = y := by
  funext i
  fin_cases i
  exact h

theorem between {a b x : Space 1} (ha : a 0 ≤ x 0) (hb : x 0 ≤ b 0) :
    x ∈ segment ℝ a b := by
  have hr : x 0 ∈ segment ℝ (a 0) (b 0) := by
    rw [segment_eq_uIcc, Set.uIcc_of_le (ha.trans hb)]
    exact ⟨ha,hb⟩
  obtain ⟨c,d,hc,hd,hcd,eq⟩ := hr
  exact ⟨c,d,hc,hd,hcd,one_ext eq⟩

theorem extreme_card_le (V : Finset (Grid 1)) : ((poly V).extremePoints ℝ).ncard ≤ 2 := by
  classical
  by_cases h : V.Nonempty
  · obtain ⟨a,ha,ham⟩ := V.exists_min_image (fun z => z 0) h
    obtain ⟨b,hb,hbm⟩ := V.exists_max_image (fun z => z 0) h
    have gen (v) (hv : v ∈ V) : embed v ∈ poly V := subset_convexHull ℝ _ ⟨v,hv,rfl⟩
    have sub : (poly V).extremePoints ℝ ⊆ {embed a,embed b} := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := extremePoints_convexHull_subset hx
      have hs : embed p ∈ segment ℝ (embed a) (embed b) :=
        between (by change (a 0 : ℝ) ≤ (p 0 : ℝ); exact_mod_cast ham p hp) (by change (p 0 : ℝ) ≤ (b 0 : ℝ); exact_mod_cast hbm p hp)
      rcases (mem_extremePoints_iff_forall_segment.mp hx).2 (embed a) (gen a ha) (embed b) (gen b hb) hs with h₁ | h₂
      · exact Or.inl h₁.symm
      · exact Or.inr h₂.symm
    exact (Set.ncard_le_ncard sub (by simp)).trans (by
      by_cases he : embed a = embed b
      · simp [he]
      · exact (Set.ncard_pair he).le)
  · simp [Finset.not_nonempty_iff_eq_empty.mp h, poly]

def vertices : Finset (Grid 1) := {pt 0,pt 6}
def centers : Finset (Grid 1) := [pt 1,pt 2,pt 3,pt 4,pt 5].toFinset

theorem poly_iff (z : Grid 1) : embed z ∈ poly vertices ↔ 0 ≤ z 0 ∧ z 0 ≤ 6 := by
  have hP : Convex ℝ (poly vertices) := convex_convexHull ℝ _
  have gen (q) (hq : q ∈ vertices) : embed q ∈ poly vertices := subset_convexHull ℝ _ ⟨q,hq,rfl⟩
  constructor
  · intro hz
    have hsub : poly vertices ⊆ {u : Space 1 | (0:ℝ) ≤ u 0} ∩ {u | u 0 ≤ 6} := by
      apply convexHull_min _ ((convex_halfSpace_ge (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).isLinear 0).inter
        (convex_halfSpace_le (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).isLinear 6))
      rintro x ⟨p,hp,rfl⟩
      change p ∈ vertices at hp
      simp only [vertices, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> constructor <;> norm_num [pt,embed]
    have hr : (0:ℝ) ≤ z 0 ∧ (z 0 : ℝ) ≤ 6 := hsub hz
    exact_mod_cast hr
  · rintro ⟨hl,hr⟩
    apply hP.segment_subset (gen (pt 0) (by simp [vertices])) (gen (pt 6) (by simp [vertices]))
    apply between
    · simpa [embed,pt] using (show (0:ℝ) ≤ (z 0 : ℝ) by exact_mod_cast hl)
    · simpa [embed,pt] using (show (z 0 : ℝ) ≤ (6 : ℝ) by exact_mod_cast hr)

theorem extremes : (poly vertices).extremePoints ℝ = embed '' (vertices : Set (Grid 1)) := by
  refine Set.Subset.antisymm extremePoints_convexHull_subset ?_
  rintro _ ⟨p,hp,rfl⟩
  rcases (show p = pt 0 ∨ p = pt 6 by simpa [vertices] using hp) with rfl | rfl
  · apply extremal_of_unique_row (h := pt (-1)) hp
    exact (show ∀ q ∈ vertices, q ≠ pt 0 → zdot (pt (-1)) q < zdot (pt (-1)) (pt 0) by decide)
  · apply extremal_of_unique_row (h := pt 1) hp
    exact (show ∀ q ∈ vertices, q ≠ pt 6 → zdot (pt 1) q < zdot (pt 1) (pt 6) by decide)

theorem attainable : 2 ∈ attainableCounts 1 := by
  classical
  have hnon : {z : Grid 1 | embed z ∈ poly vertices ∧ embed z ∉ (poly vertices).extremePoints ℝ} = (centers : Set _) := by
    apply Set.ext
    intro z
    change (embed z ∈ poly vertices ∧ embed z ∉ (poly vertices).extremePoints ℝ) ↔ z ∈ centers
    have eqpt (j : ℤ) : z = pt j ↔ z 0 = j := ⟨fun h => congrFun h 0, fun e => one_ext (y := pt j) e⟩
    rw [poly_iff, extremes, embed_inj.mem_set_image]
    change ((0 ≤ z 0 ∧ z 0 ≤ 6) ∧ z ∉ vertices) ↔ z ∈ centers
    simp only [
      vertices, centers, Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset,
      List.mem_cons, List.not_mem_nil, or_false, eqpt]
    omega
  refine ⟨vertices, ?_, ?_⟩
  · change ((poly vertices).extremePoints ℝ).encard = _
    rw [extremes, Set.InjOn.encard_image embed_inj.injOn, Set.encard_coe_eq_coe_finsetCard, (show vertices.card = 2 by decide)]
  · change ({z : Grid 1 | embed z ∈ poly vertices ∧ embed z ∉ (poly vertices).extremePoints ℝ} : Set _).encard = _
    rw [hnon,Set.encard_coe_eq_coe_finsetCard,(show centers.card = 5 by decide)]
    rfl

end TaskT.HellyFive.DimensionOne
