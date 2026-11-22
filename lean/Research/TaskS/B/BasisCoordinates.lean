import Research.TaskS.B.Challenge

open scoped BigOperators
open Finset

namespace TaskS.B.Coordinates
open Challenge

noncomputable def iv (n : ℕ) : Fin (n+1) → Lattice n :=
  Fin.cases (fun _ => -1) (fun j => Pi.single j 1)

theorem vertex_eq (n : ℕ) (j : Fin (n+1)) : vertex n j = embed (iv n j) := by
  induction j using Fin.cases with
  | zero => ext; simp [vertex, iv, embed]
  | succ j =>
    ext k
    simp [vertex, iv, embed, Pi.single_apply]

theorem decompose (n : ℕ) (t : Space n) :
    ∃ a : Fin (n+1) → ℝ, ∑ j, a j • vertex n j = t := by
  refine ⟨Fin.cons 0 t, ?_⟩
  ext k
  simp [Fin.sum_univ_succ, vertex, Pi.single_apply]

theorem intcoords {n i : ℕ} (p : Space n →ₗ[ℝ] Space i) (hp : LatticeProjection p) :
    ∃ (b : Module.Basis (Fin i) ℝ (Space i)) (A : Matrix (Fin i) (Fin (n+1)) ℤ),
      ∀ j k, b.repr (p (vertex n j)) k = (A k j : ℝ) := by
  obtain ⟨_, b, he⟩ := hp
  have hw (j : Fin (n+1)) : ∃ w : Lattice i, (∑ k, (w k : ℝ) • b k) = p (vertex n j) := by
    change p (vertex n j) ∈ Set.range (fun w : Lattice i => ∑ k, (w k : ℝ) • b k)
    rw [← he, vertex_eq]
    exact Set.mem_range_self _
  choose w hw using hw
  refine ⟨b, fun k j => w j k, fun j k => ?_⟩
  rw [← hw j]
  simp [Finsupp.single_apply]

theorem balanced {n i : ℕ} (p : Space n →ₗ[ℝ] Space i)
    (b : Module.Basis (Fin i) ℝ (Space i)) (A : Matrix (Fin i) (Fin (n+1)) ℤ)
    (he : ∀ j k, b.repr (p (vertex n j)) k = (A k j : ℝ))
    (hv : ∑ j, vertex n j = 0) (k : Fin i) : ∑ j, A k j = 0 := by
  have hh := congrArg (fun y => b.repr (p y) k) hv
  simp only [map_sum, Finsupp.finsetSum_apply, map_zero, Finsupp.zero_apply] at hh
  simp only [he] at hh
  exact_mod_cast hh

theorem annihilates {n i : ℕ} (p : Space n →ₗ[ℝ] Space i)
    (b : Module.Basis (Fin i) ℝ (Space i)) (A : Matrix (Fin i) (Fin (n+1)) ℤ)
    (he : ∀ j k, b.repr (p (vertex n j)) k = (A k j : ℝ))
    (h : Fin (n+1) → ℝ) (hh : ∀ k, ∑ j, (A k j : ℝ) * h j = 0) :
    p (∑ j, h j • vertex n j) = 0 := by
  apply b.repr.injective
  ext k
  simpa [he, mul_comm] using hh k

theorem lift_int {n : ℕ} (f : Fin (n+1) → ℤ) :
    ∃ z : Lattice n, embed z = ∑ j, (f j : ℝ) • vertex n j := by
  refine ⟨fun k => ∑ j, f j * iv n j k, ?_⟩
  ext k
  simp [embed, Finset.sum_apply, vertex_eq]

end TaskS.B.Coordinates
