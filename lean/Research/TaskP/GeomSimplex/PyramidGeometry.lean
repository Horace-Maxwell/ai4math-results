import Research.TaskP.GeomSimplex.Packing

namespace TaskP.GeomSimplex.Proof

open TaskP.GeomSimplex.Challenge

/-- Nonnegative barycentric coefficients whose total weight is s. This includes
the zero-mass slice without division or a distinguished vertex. -/
def mass {d : ℕ} (v : Fin (d + 1) → Lattice d) (s : ℝ) (x : Space d) : Prop :=
  ∃ w : Fin (d + 1) → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = s ∧
    ∑ i, w i • realPoint (v i) = x

theorem mass_nonneg {d : ℕ} {v : Fin (d + 1) → Lattice d} {s : ℝ} {x : Space d}
    (h : mass v s x) : 0 ≤ s := by
  obtain ⟨w, hw, rfl, _⟩ := h
  exact Finset.sum_nonneg fun i _ => hw i

theorem mass_vertex {d : ℕ} (v : Fin (d + 1) → Lattice d) (i : Fin (d + 1)) :
    mass v 1 (realPoint (v i)) := by
  refine ⟨fun j => if j = i then 1 else 0, fun j => by by_cases h : j = i <;> simp [h],
    by simp, ?_⟩
  simp [ite_smul]

theorem mass_add {d : ℕ} {v : Fin (d + 1) → Lattice d} {s t : ℝ} {x y : Space d}
    (h : mass v s x) (g : mass v t y) : mass v (s + t) (x + y) := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  obtain ⟨f, hf, rfl, rfl⟩ := g
  exact ⟨fun i => w i + f i, fun i => add_nonneg (hw i) (hf i), Finset.sum_add_distrib,
    by simp [add_smul, Finset.sum_add_distrib]⟩

theorem mass_smul {d : ℕ} {v : Fin (d + 1) → Lattice d} {s a : ℝ} {x : Space d}
    (ha : 0 ≤ a) (hx : mass v s x) : mass v (a * s) (a • x) := by
  obtain ⟨w, hw, rfl, rfl⟩ := hx
  refine ⟨fun i => a * w i, fun i => mul_nonneg ha (hw i), (Finset.mul_sum ..).symm, ?_⟩
  simp [mul_smul, Finset.smul_sum]

theorem mass_zero_iff {d : ℕ} (v : Fin (d + 1) → Lattice d) (x : Space d) :
    mass v 0 x ↔ x = 0 := by
  constructor
  · rintro ⟨w, hw, hs, rfl⟩
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i (_ : i ∈ Finset.univ) => hw i).mp hs
    simp [fun i => hz i (Finset.mem_univ i)]
  · rintro rfl
    exact ⟨0, by simp, by simp, by simp⟩

theorem mem_simplex_mass {d : ℕ} (v : Fin (d + 1) → Lattice d) (x : Space d) :
    x ∈ simplex v ↔ mass v 1 x := by
  constructor
  · have hc : Convex ℝ {p : Space d | mass v 1 p} := by
      intro p hp q hq a b ha hb hab
      have z := mass_add (mass_smul ha hp) (mass_smul hb hq)
      simpa [hab] using z
    apply convexHull_min _ hc
    rintro _ ⟨i, rfl⟩
    exact mass_vertex v i
  · rintro ⟨w, hw, hs, hx⟩
    exact mem_convexHull_of_exists_fintype w (realPoint ∘ v) hw hs (fun i => ⟨i,rfl⟩) hx

theorem mem_dilate_mass {d : ℕ} (v : Fin (d + 1) → Lattice d) (t : ℕ) (ht : 0 < t)
    (x : Space d) : x ∈ dilate t (simplex v) ↔ mass v (t : ℝ) x := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using mass_smul ht'.le ((mem_simplex_mass v y).mp hy)
  · intro hx
    refine ⟨(t : ℝ)⁻¹ • x, (mem_simplex_mass _ _).mpr ?_, ?_⟩
    · simpa [ht'.ne'] using mass_smul (inv_nonneg.mpr ht'.le) hx
    · change (t : ℝ) • ((t : ℝ)⁻¹ • x) = x
      simp [smul_smul, ht'.ne']

/-- The apex occupies the first vertex and first coordinate. -/
def pyrVertices {d : ℕ} (v : Fin (d + 1) → Lattice d) : Fin ((d + 1) + 1) → Challenge.Lattice (d + 1) :=
  Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (v i))

theorem mass_pyramid {d : ℕ} (v : Fin (d + 1) → Lattice d) (t : ℝ) (x : Space (d + 1)) :
    mass (pyrVertices v) t x ↔ 0 ≤ x 0 ∧ mass v (t - x 0) (fun i => x i.succ) := by
  constructor
  · rintro ⟨w, hw, hs, hx⟩
    have hx₀ := congrFun hx 0
    simp [Fin.sum_univ_succ, pyrVertices, realPoint, Finset.sum_apply] at hx₀
    refine ⟨hx₀ ▸ hw 0, fun i => w i.succ, fun i => hw _, ?_, ?_⟩
    · rw [Fin.sum_univ_succ] at hs
      linarith
    · ext j
      have hh := congrFun hx j.succ
      simpa [Fin.sum_univ_succ, pyrVertices, realPoint, Finset.sum_apply] using hh
  · rintro ⟨hx₀, w, hw, hs, hx⟩
    refine ⟨Fin.cons (x 0) w, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases (by simpa using hx₀) (fun j => by simpa using hw j) i
    · rw [Fin.sum_univ_succ]
      simp [hs]
    · ext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [Fin.sum_univ_succ, realPoint, pyrVertices, Finset.sum_apply]
      · have hh := congrFun hx i
        simpa [Fin.sum_univ_succ, realPoint, pyrVertices, Finset.sum_apply] using hh

theorem full_pyramid {d : ℕ} (v : Fin (d + 1) → Lattice d) (hv : fullSimplex v) :
    fullSimplex (pyrVertices v) := by
  rw [fullSimplex, affineIndependent_iff_of_fintype] at hv ⊢
  intro w hs hx
  rw [Finset.weightedVSub_eq_linear_combination _ hs] at hx
  have h₀ := congrFun hx 0
  simp [Fin.sum_univ_succ, pyrVertices, realPoint, Finset.sum_apply] at h₀
  rw [Fin.sum_univ_succ, h₀, zero_add] at hs
  have hh : ∑ i, w i.succ • (realPoint ∘ v) i = 0 := by
    ext j
    have hj := congrFun hx j.succ
    simpa [Fin.sum_univ_succ, pyrVertices, realPoint, Finset.sum_apply] using hj
  have ind := hv (fun i => w i.succ) hs (by rwa [Finset.weightedVSub_eq_linear_combination _ hs])
  exact Fin.cases h₀ ind

end TaskP.GeomSimplex.Proof
