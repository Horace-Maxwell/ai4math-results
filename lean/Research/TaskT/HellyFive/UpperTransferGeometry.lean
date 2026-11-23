import Research.TaskT.HellyFive.FiniteGeometry

namespace TaskT.HellyFive.UpperTransfer
open Set FiniteGeometry

theorem poly_mem {n : ℕ} {A : Finset (Grid n)} {x : Grid n} (hx : x ∈ A) :
    embed x ∈ poly A := subset_convexHull ℝ _ ⟨x, hx, rfl⟩

theorem poly_mono {n : ℕ} {A B : Finset (Grid n)} (h : A ⊆ B) :
    poly A ⊆ poly B := convexHull_mono (Set.image_mono h)

theorem compact_poly {n : ℕ} (A : Finset (Grid n)) : IsCompact (poly A) :=
  (A.finite_toSet.image embed).isCompact_convexHull ℝ

/-- Grid-convexity relative to a finite set of possible points. -/
def ClosedIn {n : ℕ} (box A : Finset (Grid n)) : Prop :=
  A ⊆ box ∧ ∀ z ∈ box, embed z ∈ poly A → z ∈ A

theorem grid_poly_finite {n : ℕ} (A : Finset (Grid n)) :
    {z : Grid n | embed z ∈ poly A}.Finite := by
  classical
  obtain ⟨a, ha⟩ := (compact_poly A).isBounded.bddBelow
  obtain ⟨b, hb⟩ := (compact_poly A).isBounded.bddAbove
  refine (Set.finite_Icc (fun i => ⌊a i⌋ : Grid n) (fun i => ⌈b i⌉ : Grid n)).subset ?_
  intro z hz
  exact ⟨fun i => Int.cast_le.mp ((Int.floor_le (a i)).trans (ha hz i)),
         fun i => Int.cast_le.mp ((hb hz i).trans (Int.le_ceil _))⟩

theorem extreme_generated {n : ℕ} (A : Finset (Grid n)) :
    convexHull ℝ ((poly A).extremePoints ℝ) = poly A := by
  have hf : ((poly A).extremePoints ℝ).Finite :=
    (A.finite_toSet.image embed).subset extremePoints_convexHull_subset
  rw [← (hf.isCompact_convexHull ℝ).isClosed.closure_eq]
  exact closure_convexHull_extremePoints (compact_poly A) (convex_convexHull ℝ _)

theorem extend_closed {n : ℕ} {box A : Finset (Grid n)} (hA : ClosedIn box A)
    (hproper : A ≠ box) :
    ∃ z ∈ box, z ∉ A ∧ ClosedIn box (insert z A) ∧
      embed z ∈ (poly (insert z A)).extremePoints ℝ := by
  classical
  let choices := box.powerset.filter fun T => ClosedIn box T ∧ A ⊂ T
  have hbx : box ∈ choices := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr Subset.rfl, ⟨Subset.rfl, fun _ h _ => h⟩,
      Finset.ssubset_iff_subset_ne.mpr ⟨hA.1, hproper⟩⟩
  obtain ⟨T, hT, hmin⟩ := choices.exists_min_image Finset.card ⟨box, hbx⟩
  obtain ⟨hTc, hAT⟩ := (Finset.mem_filter.mp hT).2
  have hx : ∃ z ∈ T, z ∉ A ∧ embed z ∈ (poly T).extremePoints ℝ := by
    by_contra! h
    have he : (poly T).extremePoints ℝ ⊆ poly A := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := extremePoints_convexHull_subset hx
      by_contra hn
      exact h z hz (fun ha => hn (poly_mem ha)) hx
    have hsub : poly T ⊆ poly A := by
      rw [← extreme_generated T]
      exact convexHull_min he (convex_convexHull ℝ _)
    exact hAT.not_ge (fun z hz => hA.2 z (hTc.1 hz) (hsub (poly_mem hz)))
  obtain ⟨z, hzT, hzA, hzext⟩ := hx
  have her : ClosedIn box (T.erase z) := by
    refine ⟨(Finset.erase_subset z T).trans hTc.1, ?_⟩
    intro q hq hp
    have hconv := ((convex_convexHull ℝ _).mem_extremePoints_iff_convex_sdiff.mp hzext).2
    have he : poly (T.erase z) ⊆ poly T \ {embed z} := by
      apply convexHull_min _ hconv
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp ha
      exact ⟨poly_mem hmem, fun hh => hne (embed_inj (Set.mem_singleton_iff.mp hh))⟩
    obtain ⟨hpoly,hne⟩ := he hp
    exact Finset.mem_erase.mpr ⟨fun hh => hne (Set.mem_singleton_iff.mpr (congrArg embed hh)), hTc.2 _ hq hpoly⟩
  have hAT' : A ⊆ T.erase z := by
    intro q hq
    exact Finset.mem_erase.mpr ⟨fun hh => hzA (hh ▸ hq), hAT.le hq⟩
  have hEq : A = T.erase z := by
    by_contra hn
    have hc := hmin (T.erase z) (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr her.1, her, Finset.ssubset_iff_subset_ne.mpr ⟨hAT',hn⟩⟩)
    exact (Finset.card_erase_lt_of_mem hzT).not_ge hc
  have hins : insert z A = T := hEq ▸ Finset.insert_erase hzT
  exact ⟨z, hTc.1 hzT, hzA, hins ▸ hTc, hins ▸ hzext⟩

end TaskT.HellyFive.UpperTransfer
