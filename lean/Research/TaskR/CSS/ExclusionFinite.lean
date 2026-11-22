import Research.TaskR.CSS.Challenge

namespace TaskR.CSS.Exclusion
open TaskR.CSS.Challenge
open scoped BigOperators

/-- The six possible lattice points in the simplex. -/
def points : Finset Lattice := {0, -weight, e 0, e 1, e 2, e 3}

private theorem coord_cases (a b c d : ℤ) (s : ℤ) (hs : s = a + b + c + d)
    (h : s ≤ 1) (h0 : 0 ≤ 6*a+2*(1-s)) (h1 : 0 ≤ 6*b+1-s)
    (h2 : 0 ≤ 6*c+1-s) (h3 : 0 ≤ 6*d+1-s) :
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨
    (a = -2 ∧ b = -1 ∧ c = -1 ∧ d = -1) ∨
    (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨
    (a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 0) ∨
    (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 0) ∨
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 1) := by
  have hlo : -5 ≤ s := by omega
  interval_cases s <;> omega

theorem finite_classification (z : Lattice) (s : ℤ) (hs : s = z 0 + z 1 + z 2 + z 3)
    (h : s ≤ 1) (h0 : 0 ≤ 6*z 0+2*(1-s)) (h1 : 0 ≤ 6*z 1+1-s)
    (h2 : 0 ≤ 6*z 2+1-s) (h3 : 0 ≤ 6*z 3+1-s) : z ∈ points := by
  have hh := coord_cases _ _ _ _ _ hs h h0 h1 h2 h3
  simpa [points, funext_iff, Fin.forall_fin_succ, e, weight, Pi.single_apply] using hh

/-- A subset of size at least two fails divisibility in some coordinate,
so its centroid is not a lattice point. The finite search has 64 subsets. -/
private theorem nonintegral_subsets :
    ∀ s ∈ points.powerset, 2 ≤ s.card →
      ∃ i : Fin 4, (∑ z ∈ s, z i) % (s.card : ℤ) ≠ 0 := by
  decide +kernel

theorem no_translated_leaf (s : Finset Lattice) (t : Lattice) (hc : 2 ≤ s.card)
    (hs : ∑ z ∈ s, z = 0) (hp : ∀ z ∈ s, t + z ∈ points) : False := by
  let u := s.image (fun z => t + z)
  have subset : u ⊆ points := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact hp z hz
  have inject : Function.Injective (fun z : Lattice => t + z) := add_right_injective t
  have size : u.card = s.card := Finset.card_image_of_injective s inject
  obtain ⟨i, bad⟩ := nonintegral_subsets u (Finset.mem_powerset.mpr subset) (size.symm ▸ hc)
  have hsi : (∑ z ∈ s, z i) = 0 := by
    simpa [Finset.sum_apply] using congrFun hs i
  have hi : (∑ z ∈ u, z i) = (s.card : ℤ) * t i := by
    dsimp only [u]
    rw [Finset.sum_image (fun _ _ _ _ h => inject h)]
    simp [Finset.sum_add_distrib, hsi]
  exact bad (by rw [hi, size]; simp)

end TaskR.CSS.Exclusion
