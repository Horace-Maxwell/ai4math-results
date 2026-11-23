import Research.TaskT.HellyFive.UpperWeights

namespace TaskT.HellyFive.UpperFive
open FiniteGeometry Set

def allGrid {n : ℕ} (V : Finset (Grid n)) : Set (Grid n) := {z | embed z ∈ poly V}
def otherGrid {n : ℕ} (V : Finset (Grid n)) : Set (Grid n) :=
  {z | embed z ∈ poly V ∧ embed z ∉ (poly V).extremePoints ℝ}

theorem allGrid_finite {n : ℕ} (V : Finset (Grid n)) : (allGrid V).Finite := by
  classical
  let B : ℕ := ∑ p ∈ V, ∑ i, (p i).natAbs
  have bound (p : Grid n) (hp : p ∈ V) (i : Fin n) : (p i).natAbs ≤ B :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (p j).natAbs) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun q _ => Nat.zero_le (∑ j, (q j).natAbs)) hp)
  apply (Set.finite_Icc (fun _ : Fin n => -(B : ℤ)) (fun _ : Fin n => (B : ℤ))).subset
  intro z hz
  have coord (i : Fin n) : -(B : ℤ) ≤ z i ∧ z i ≤ B := by
    let f : Space n →ₗ[ℝ] ℝ := LinearMap.proj i
    have h : Convex ℝ ({y | -(B:ℝ) ≤ f y} ∩ {y | f y ≤ (B : ℝ)}) :=
      (convex_halfSpace_ge f.isLinear _).inter (convex_halfSpace_le f.isLinear _)
    have sub : embed '' (V : Set _) ⊆ ({y | -(B:ℝ) ≤ f y} ∩ {y | f y ≤ (B:ℝ)}) := by
      rintro _ ⟨p,hp,rfl⟩
      change -(B:ℝ) ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ (B:ℝ)
      have hbp := bound p hp i
      exact_mod_cast (show -(B:ℤ) ≤ p i ∧ p i ≤ B by omega)
    have hr := convexHull_min sub h hz
    change -(B:ℝ) ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ B at hr
    exact_mod_cast hr
  exact ⟨fun i => (coord i).1, fun i => (coord i).2⟩

theorem otherGrid_finite {n : ℕ} (V : Finset (Grid n)) : (otherGrid V).Finite :=
  (allGrid_finite V).subset fun _ h => h.1

theorem card_decomposition {n : ℕ} (V : Finset (Grid n)) :
    ((poly V).extremePoints ℝ).ncard + (otherGrid V).ncard = (allGrid V).ncard := by
  classical
  let A := allGrid V
  let X := otherGrid V
  let E := (poly V).extremePoints ℝ
  have es : embed '' (A \ X) = E := by
    ext y; constructor
    · rintro ⟨z,⟨hz,hx⟩,rfl⟩
      by_contra hn
      exact hx ⟨hz,hn⟩
    · intro hy
      obtain ⟨z,hz,rfl⟩ := (extremePoints_convexHull_subset hy : y ∈ embed '' (V : Set _))
      exact ⟨z,⟨(show embed z ∈ poly V from hy.1),fun h => h.2 hy⟩,rfl⟩
  change E.ncard + X.ncard = A.ncard
  rw [← es, Set.ncard_image_of_injective _ embed_inj]
  exact Set.ncard_sdiff_add_ncard_of_subset (fun _ h => h.1) (allGrid_finite V)

theorem apply_bound {n b : ℕ} (V : Finset (Grid n)) (hk : (otherGrid V).ncard ≤ 5)
    (h : ∀ s X : Finset (Grid n), X.card ≤ 5 →
      (∀ a ∈ s, ∀ c ∈ s, a ≠ c → sameParity a c → gridMid a c ∈ X) → s.card ≤ b) :
    ((poly V).extremePoints ℝ).ncard + (otherGrid V).ncard ≤ b := by
  classical
  rw [card_decomposition]
  let s := (allGrid_finite V).toFinset
  let X := (otherGrid_finite V).toFinset
  have e : (allGrid V).ncard = s.card := Set.ncard_eq_toFinset_card _ _
  have ex : (otherGrid V).ncard = X.card := Set.ncard_eq_toFinset_card _ _
  rw [e]
  apply h s X (ex ▸ hk)
  intro a ha c hc hac hab
  apply (otherGrid_finite V).mem_toFinset.mpr
  exact gridMid_mem_nonvertices (convex_convexHull ℝ _) ((allGrid_finite V).mem_toFinset.mp ha)
    ((allGrid_finite V).mem_toFinset.mp hc) hac hab

theorem high_upper {n : ℕ} (V : Finset (Grid n)) (hk : (otherGrid V).ncard ≤ 5) :
    ((poly V).extremePoints ℝ).ncard + (otherGrid V).ncard ≤ 2 ^ (n+1) + 10 := by
  apply apply_bound V hk
  intro s X hx h
  have h₁ := all_dimensional_bound h
  have h₂ : X.card.choose 3 ≤ 10 := (Nat.choose_le_choose 3 hx).trans_eq (by decide)
  rw [pow_succ]
  omega

end TaskT.HellyFive.UpperFive
