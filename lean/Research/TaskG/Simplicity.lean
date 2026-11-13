import Research.TaskG.Data

set_option autoImplicit false

namespace TaskG.Proof
open AxialMSZ.Challenge

private theorem simple_coordinates (u : V) : u = ∑ j : Fin 4, u j • e j := by
  funext k
  fin_cases k <;> simp [e, Pi.single_apply]

/-- A polynomial in left multiplication is the individual coordinate projection. -/
def coordinateProjector (i : Fin 4) : V →ₗ[K] V :=
  (3 : K) • ((μ (e i)).comp ((μ (e i)).comp (μ (e i)))) +
    (3 : K) • μ (e i) + (6 : K) • LinearMap.id

private theorem coordinateProjector_basis (i j : Fin 4) :
    coordinateProjector i (e j) = (e j i) • e i := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem coordinateProjector_apply (i : Fin 4) (u : V) :
    coordinateProjector i u = u i • e i := by
  calc
    coordinateProjector i u = coordinateProjector i (∑ j : Fin 4, u j • e j) :=
      congrArg (coordinateProjector i) (simple_coordinates u)
    _ = ∑ j : Fin 4, u j • coordinateProjector i (e j) := by simp
    _ = ∑ j : Fin 4, u j • ((e j i) • e i) := by simp_rw [coordinateProjector_basis]
    _ = u i • e i := by
      fin_cases i <;> simp [e, Pi.single_apply]

/-- Left multiplication by any basis axis is invertible. -/
def inverseCombination (i : Fin 4) : V →ₗ[K] V :=
  (6 : K) •
    ((((μ (e i)).comp ((μ (e i)).comp ((μ (e i)).comp (μ (e i))))) -
      ((μ (e i)).comp ((μ (e i)).comp (μ (e i))))) +
      ((μ (e i)).comp (μ (e i))) + μ (e i))

private theorem inverseCombination_basis (i j : Fin 4) :
    inverseCombination i (e j) = e j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem inverseCombination_apply (i : Fin 4) (u : V) :
    inverseCombination i u = u := by
  calc
    inverseCombination i u = inverseCombination i (∑ j : Fin 4, u j • e j) :=
      congrArg (inverseCombination i) (simple_coordinates u)
    _ = ∑ j : Fin 4, u j • inverseCombination i (e j) := by simp
    _ = ∑ j : Fin 4, u j • e j := by simp_rw [inverseCombination_basis]
    _ = u := (simple_coordinates u).symm

theorem basis_mem_of_coordinate {I : Submodule K V} (hI : IsIdeal μ I)
    {u : V} (hu : u ∈ I) (i : Fin 4) (hi : u i ≠ 0) : e i ∈ I := by
  have h1 := (hI (e i) u hu).1
  have h2 := (hI (e i) (μ (e i) u) h1).1
  have h3 := (hI (e i) (μ (e i) (μ (e i) u)) h2).1
  have hp : coordinateProjector i u ∈ I := by
    change (3 : K) • μ (e i) (μ (e i) (μ (e i) u)) +
      (3 : K) • μ (e i) u + (6 : K) • u ∈ I
    exact I.add_mem (I.add_mem (I.smul_mem 3 h3) (I.smul_mem 3 h1)) (I.smul_mem 6 hu)
  rw [coordinateProjector_apply] at hp
  have hs := I.smul_mem (u i)⁻¹ hp
  simpa [smul_smul, inv_mul_cancel₀ hi] using hs

theorem ideal_top_of_basis {I : Submodule K V} (hI : IsIdeal μ I)
    (i : Fin 4) (hi : e i ∈ I) : I = ⊤ := by
  have hall (v : V) : μ (e i) v ∈ I := (hI v (e i) hi).2
  rw [eq_top_iff]
  intro u _
  have hp : inverseCombination i u ∈ I := by
    change (6 : K) •
      (μ (e i) (μ (e i) (μ (e i) (μ (e i) u))) -
        μ (e i) (μ (e i) (μ (e i) u)) +
        μ (e i) (μ (e i) u) + μ (e i) u) ∈ I
    exact I.smul_mem 6 (I.add_mem (I.add_mem
      (I.sub_mem (hall _) (hall _)) (hall _)) (hall _))
  simpa only [inverseCombination_apply] using hp

theorem simple : IsSimpleAlg μ := by
  constructor
  · refine ⟨e 0, e 0, ?_⟩
    decide +kernel
  · intro I hI
    by_cases ht : I = ⊤
    · exact Or.inr ht
    · left
      rw [Submodule.eq_bot_iff]
      intro u hu
      by_contra hn
      have hi : ∃ i : Fin 4, u i ≠ 0 := by
        by_contra ha
        push Not at ha
        exact hn (funext ha)
      obtain ⟨i, hi⟩ := hi
      exact ht (ideal_top_of_basis hI i (basis_mem_of_coordinate hI hu i hi))

theorem directlyIndecomposable : TaskG.Challenge.DirectlyIndecomposable μ := by
  intro I J hI _ hd _
  rcases simple.2 I hI with h | h
  · exact Or.inl h
  · right
    simpa [h] using hd

theorem hasNoIdentity : TaskG.Challenge.HasNoIdentity μ := by
  rintro ⟨z, hz⟩
  have h1 := congrFun (hz (e 1)).1 1
  have h3 := congrFun (hz (e 3)).1 3
  norm_num [μ_apply, e, Pi.single_apply] at h1 h3
  have hc := congrFun (hz (e 0)).1 2
  norm_num [μ_apply, e, Pi.single_apply, h1, h3] at hc
  exact (by decide +kernel : (2 : K) ≠ 0) hc

#print axioms coordinateProjector_apply
#print axioms inverseCombination_apply
#print axioms basis_mem_of_coordinate
#print axioms ideal_top_of_basis
#print axioms simple
#print axioms directlyIndecomposable
#print axioms hasNoIdentity

end TaskG.Proof
