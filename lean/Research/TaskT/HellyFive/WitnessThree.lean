import Research.TaskT.HellyFive.FiniteGeometry

namespace TaskT.HellyFive.FiniteGeometry.WitnessThree
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def vertices : Finset (Grid 3) := [![-1, -1, 1], ![-1, 0, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 0], ![0, -1, 1], ![0, 0, -1], ![0, 1, -1], ![0, 1, 1], ![0, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, 1], ![1, 1, -1], ![1, 1, 1], ![1, 2, 0], ![2, 0, 0], ![2, 1, 0]].toFinset
def centers : Finset (Grid 3) := [![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0]].toFinset

def exposer (p : Grid 3) : Grid 3 :=
  match p 0, p 1, p 2 with
  | -1, -1, 1 => ![-1, -1, 0]
  | -1, 0, 0 => ![-3, -1, -2]
  | -1, 0, 1 => ![-2, 1, 2]
  | -1, 1, 0 => ![-2, 1, -1]
  | 0, -1, 0 => ![-1, -3, -2]
  | 0, -1, 1 => ![1, -2, 2]
  | 0, 0, -1 => ![-1, -1, -2]
  | 0, 1, -1 => ![-1, 1, -2]
  | 0, 1, 1 => ![-1, 2, 3]
  | 0, 2, 0 => ![-1, 2, -1]
  | 1, -1, 0 => ![1, -2, -1]
  | 1, 0, -1 => ![1, -1, -2]
  | 1, 0, 1 => ![2, -1, 3]
  | 1, 1, -1 => ![1, 1, -2]
  | 1, 1, 1 => ![1, 1, 2]
  | 1, 2, 0 => ![1, 2, -1]
  | 2, 0, 0 => ![2, -1, -1]
  | 2, 1, 0 => ![2, 1, -1]
  | _, _, _ => 0

def firstMid (p : Grid 3) : Grid 3 :=
  match p 0, p 1, p 2 with
  | 0, 0, 0 => ![-1, -1, 1]
  | 0, 0, 1 => ![-1, -1, 1]
  | 0, 1, 0 => ![-1, 0, 0]
  | 1, 0, 0 => ![0, -1, 0]
  | 1, 1, 0 => ![0, 2, 0]
  | _, _, _ => 0

def secondMid (p : Grid 3) : Grid 3 :=
  match p 0, p 1, p 2 with
  | 0, 0, 0 => ![1, 1, -1]
  | 0, 0, 1 => ![1, 1, 1]
  | 0, 1, 0 => ![1, 2, 0]
  | 1, 0, 0 => ![2, 1, 0]
  | 1, 1, 0 => ![2, 0, 0]
  | _, _, _ => 0

def separatingRow (p : Grid 3) : Grid 3 :=
  match p 0, p 1, p 2 with
  | -1, -1, -1 => ![-1, -1, -1]
  | -1, -1, 0 => ![-1, -1, -1]
  | -1, -1, 2 => ![-1, -1, 1]
  | -1, 0, -1 => ![-1, -1, -1]
  | -1, 0, 2 => ![-1, 0, 1]
  | -1, 1, -1 => ![-1, 0, -1]
  | -1, 1, 1 => ![-1, 1, 1]
  | -1, 1, 2 => ![-1, 0, 1]
  | -1, 2, -1 => ![-1, 0, -1]
  | -1, 2, 0 => ![-1, 1, -1]
  | -1, 2, 1 => ![-1, 1, 0]
  | -1, 2, 2 => ![-1, 0, 1]
  | 0, -1, -1 => ![-1, -1, -1]
  | 0, -1, 2 => ![0, -1, 1]
  | 0, 0, 2 => ![0, 0, 1]
  | 0, 1, 2 => ![-1, 1, 1]
  | 0, 2, -1 => ![-1, 1, -1]
  | 0, 2, 1 => ![-1, 1, 1]
  | 0, 2, 2 => ![-1, 1, 1]
  | 1, -1, -1 => ![0, -1, -1]
  | 1, -1, 1 => ![1, -1, 1]
  | 1, -1, 2 => ![0, -1, 1]
  | 1, 0, 2 => ![0, 0, 1]
  | 1, 1, 2 => ![0, 0, 1]
  | 1, 2, -1 => ![0, 1, -1]
  | 1, 2, 1 => ![0, 1, 1]
  | 1, 2, 2 => ![-1, 1, 1]
  | 2, -1, -1 => ![0, -1, -1]
  | 2, -1, 0 => ![1, -1, -1]
  | 2, -1, 1 => ![1, -1, 0]
  | 2, -1, 2 => ![0, -1, 1]
  | 2, 0, -1 => ![1, -1, -1]
  | 2, 0, 1 => ![1, -1, 1]
  | 2, 0, 2 => ![0, 0, 1]
  | 2, 1, -1 => ![1, 0, -1]
  | 2, 1, 1 => ![1, 0, 1]
  | 2, 1, 2 => ![0, 0, 1]
  | 2, 2, -1 => ![0, 1, -1]
  | 2, 2, 0 => ![1, 1, -1]
  | 2, 2, 1 => ![0, 1, 1]
  | 2, 2, 2 => ![0, 0, 1]
  | _, _, _ => 0

theorem counts : vertices.card = 18 ∧ centers.card = 5 := by decide
private theorem bounds : ∀ p ∈ vertices, ∀ i, -1 ≤ p i ∧ p i ≤ 2 := by decide
private theorem exposed : ∀ p ∈ vertices, ∀ q ∈ vertices, q ≠ p → zdot (exposer p) q < zdot (exposer p) p := by decide
private theorem midpoint_checks : ∀ p ∈ centers, p ∉ vertices ∧ firstMid p ∈ vertices ∧ secondMid p ∈ vertices ∧ ∀ i, firstMid p i + secondMid p i = 2 * p i := by decide
private theorem excluded : ∀ b : Fin 3 → Fin 4,
    cubeGrid b ∈ vertices ∨ cubeGrid b ∈ centers ∨
    ∀ q ∈ vertices, zdot (separatingRow (cubeGrid b)) q < zdot (separatingRow (cubeGrid b)) (cubeGrid b) := by decide
theorem geometry : (poly vertices).extremePoints ℝ = embed '' (vertices : Set (Grid 3)) ∧
    {z : Grid 3 | embed z ∈ poly vertices ∧ embed z ∉ (poly vertices).extremePoints ℝ} = (centers : Set _) := by
  apply realization bounds
  · exact fun p hp => ⟨exposer p, exposed p hp⟩
  · intro p hp
    obtain ⟨hn, ha, hb, he⟩ := midpoint_checks p hp
    exact ⟨hn, firstMid p, ha, secondMid p, hb, he⟩
  · intro b
    rcases excluded b with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨_,h⟩)
theorem attainable : 18 ∈ attainableCounts 3 := by
  refine ⟨vertices, ?_, ?_⟩
  · change ((poly vertices).extremePoints ℝ).encard = _
    rw [geometry.1, Set.InjOn.encard_image embed_inj.injOn, Set.encard_coe_eq_coe_finsetCard, counts.1]
  · change ({z : Grid 3 | embed z ∈ poly vertices ∧ embed z ∉ (poly vertices).extremePoints ℝ} : Set _).encard = 5
    rw [geometry.2, Set.encard_coe_eq_coe_finsetCard, counts.2]
    rfl
end TaskT.HellyFive.FiniteGeometry.WitnessThree
