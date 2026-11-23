import Research.TaskT.HellyFive.FiniteGeometry

namespace TaskT.HellyFive.FiniteGeometry.WitnessTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def vertices : Finset (Grid 2) := [![-1, -1], ![-1, 0], ![0, 2], ![1, -1], ![1, 2], ![2, 0], ![2, 1]].toFinset
def centers : Finset (Grid 2) := [![0, -1], ![0, 0], ![0, 1], ![1, 0], ![1, 1]].toFinset

def exposer (p : Grid 2) : Grid 2 :=
  match p 0, p 1 with
  | -1, -1 => ![-6, -6]
  | -1, 0 => ![-6, 1]
  | 0, 2 => ![-6, 4]
  | 1, -1 => ![1, -6]
  | 1, 2 => ![1, 2]
  | 2, 0 => ![2, -1]
  | 2, 1 => ![2, 1]
  | _, _ => 0

def firstMid (p : Grid 2) : Grid 2 :=
  match p 0, p 1 with
  | 0, -1 => ![-1, -1]
  | 0, 0 => ![-1, 0]
  | 0, 1 => ![-1, 0]
  | 1, 0 => ![-1, 0]
  | 1, 1 => ![0, 2]
  | _, _ => 0

def secondMid (p : Grid 2) : Grid 2 :=
  match p 0, p 1 with
  | 0, -1 => ![1, -1]
  | 0, 0 => ![2, 0]
  | 0, 1 => ![1, 2]
  | 1, 0 => ![2, 0]
  | 1, 1 => ![2, 0]
  | _, _ => 0

def separatingRow (p : Grid 2) : Grid 2 :=
  match p 0, p 1 with
  | -1, 1 => ![-2, 1]
  | -1, 2 => ![-1, 1]
  | 2, -1 => ![1, -1]
  | 2, 2 => ![1, 1]
  | _, _ => 0

theorem counts : vertices.card = 7 ∧ centers.card = 5 := by decide
private theorem bounds : ∀ p ∈ vertices, ∀ i, -1 ≤ p i ∧ p i ≤ 2 := by decide
private theorem exposed : ∀ p ∈ vertices, ∀ q ∈ vertices, q ≠ p → zdot (exposer p) q < zdot (exposer p) p := by decide
private theorem excluded : ∀ b : Fin 2 → Fin 4,
    cubeGrid b ∈ vertices ∨ cubeGrid b ∈ centers ∨
    ∀ q ∈ vertices, zdot (separatingRow (cubeGrid b)) q < zdot (separatingRow (cubeGrid b)) (cubeGrid b) := by decide
theorem geometry : (poly vertices).extremePoints ℝ = embed '' (vertices : Set (Grid 2)) ∧
    {z : Grid 2 | embed z ∈ poly vertices ∧ embed z ∉ (poly vertices).extremePoints ℝ} = (centers : Set _) := by
  classical
  have e : (poly vertices).extremePoints ℝ = embed '' (vertices : Set (Grid 2)) := by
    refine Set.Subset.antisymm extremePoints_convexHull_subset ?_
    rintro _ ⟨p,hp,rfl⟩
    exact extremal_of_unique_row hp (exposed p hp)
  have gen (p) (hp : p ∈ vertices) : embed p ∈ poly vertices :=
    subset_convexHull ℝ _ ⟨p,hp,rfl⟩
  refine ⟨e, Set.ext fun p => ⟨?_, ?_⟩⟩
  · rintro ⟨hp,hn⟩
    obtain ⟨q,rfl⟩ := cube_repr (grid_box hp bounds)
    rcases excluded q with hv | hx | hs
    · exact (hn (e.symm ▸ ⟨_,hv,rfl⟩)).elim
    · exact hx
    · exact (strictly_separated hs hp).elim
  · intro hp
    have hnot : p ∉ vertices := (show ∀ q ∈ centers, q ∉ vertices by decide) p hp
    refine ⟨?_, ?_⟩
    · change p ∈ centers at hp
      simp only [centers, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · have h := (convex_convexHull ℝ _) (gen ![-1, -1] (by decide)) (gen ![1, -1] (by decide))
            (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2+1/2=1)
        have eq : ((1:ℝ)/2) • embed ![-1, -1] + ((1:ℝ)/2) • embed ![1, -1] = embed ![0, -1] := by
          funext i; fin_cases i <;> norm_num [embed]
        rwa [eq] at h
      · have h := (convex_convexHull ℝ _) (gen ![-1, 0] (by decide)) (gen ![2, 0] (by decide))
            (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num : (2:ℝ)/3+1/3=1)
        have eq : ((2:ℝ)/3) • embed ![-1, 0] + ((1:ℝ)/3) • embed ![2, 0] = embed ![0, 0] := by
          funext i; fin_cases i <;> norm_num [embed]
        rwa [eq] at h
      · have h := (convex_convexHull ℝ _) (gen ![-1, 0] (by decide)) (gen ![1, 2] (by decide))
            (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2+1/2=1)
        have eq : ((1:ℝ)/2) • embed ![-1, 0] + ((1:ℝ)/2) • embed ![1, 2] = embed ![0, 1] := by
          funext i; fin_cases i <;> norm_num [embed]
        rwa [eq] at h
      · have h := (convex_convexHull ℝ _) (gen ![-1, 0] (by decide)) (gen ![2, 0] (by decide))
            (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num : (1:ℝ)/3+2/3=1)
        have eq : ((1:ℝ)/3) • embed ![-1, 0] + ((2:ℝ)/3) • embed ![2, 0] = embed ![1, 0] := by
          funext i; fin_cases i <;> norm_num [embed]
        rwa [eq] at h
      · have h := (convex_convexHull ℝ _) (gen ![0, 2] (by decide)) (gen ![2, 0] (by decide))
            (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2+1/2=1)
        have eq : ((1:ℝ)/2) • embed ![0, 2] + ((1:ℝ)/2) • embed ![2, 0] = embed ![1, 1] := by
          funext i; fin_cases i <;> norm_num [embed]
        rwa [eq] at h
    · rw [e]
      rintro ⟨q,hq,he⟩
      exact hnot (embed_inj he ▸ hq)

theorem attainable : 7 ∈ attainableCounts 2 := by
  refine ⟨vertices, ?_, ?_⟩
  · change ((poly vertices).extremePoints ℝ).encard = _
    rw [geometry.1, Set.InjOn.encard_image embed_inj.injOn, Set.encard_coe_eq_coe_finsetCard, counts.1]
  · change ({z : Grid 2 | embed z ∈ poly vertices ∧ embed z ∉ (poly vertices).extremePoints ℝ} : Set _).encard = 5
    rw [geometry.2, Set.encard_coe_eq_coe_finsetCard, counts.2]
    rfl
end TaskT.HellyFive.FiniteGeometry.WitnessTwo
