import Research.TaskT.HellyFive.Challenge

namespace TaskT.HellyFive

def gridMid {n : ℕ} (x y : Grid n) : Grid n := fun i => (x i + y i) / 2

def sameParity {n : ℕ} (x y : Grid n) : Prop := ∀ i, x i % 2 = y i % 2

theorem double_gridMid {n : ℕ} {x y : Grid n} (h : sameParity x y) (i : Fin n) :
    2 * gridMid x y i = x i + y i := by
  have hi := h i
  unfold gridMid
  omega

theorem embed_gridMid {n : ℕ} {x y : Grid n} (h : sameParity x y) :
    embed (gridMid x y) = midpoint ℝ (embed x) (embed y) := by
  rw [midpoint_eq_smul_add]
  funext i
  have hi : (2 : ℝ) * (gridMid x y i : ℝ) = (x i : ℝ) + (y i : ℝ) := by
    exact_mod_cast double_gridMid h i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, embed, invOf_eq_inv]
  linarith

/-- The midpoint charge belongs to the actual five-point set for every admissible polytope. -/
theorem gridMid_mem_nonvertices {n : ℕ} {P : Set (Space n)} (hP : Convex ℝ P)
    {x y : Grid n} (hx : embed x ∈ P) (hy : embed y ∈ P)
    (hxy : x ≠ y) (h : sameParity x y) :
    embed (gridMid x y) ∈ P ∧ embed (gridMid x y) ∉ P.extremePoints ℝ := by
  rw [embed_gridMid h]
  refine ⟨hP.midpoint_mem hx hy, ?_⟩
  intro he
  have hseg := (mem_extremePoints.mp he).2 (embed x) hx (embed y) hy
    (midpoint_mem_openSegment (𝕜 := ℝ) (embed x) (embed y))
  have eq := hseg.1.trans hseg.2.symm
  apply hxy
  funext i
  have hi : (x i : ℝ) = (y i : ℝ) := congrFun eq i
  exact_mod_cast hi

/-- Recover each vertex of a same-parity triangle from its three lattice midpoints. -/
theorem recover_vertex {n : ℕ} {x y z : Grid n}
    (hxy : sameParity x y) (hxz : sameParity x z) (hyz : sameParity y z) :
    gridMid x y + gridMid x z - gridMid y z = x := by
  funext i
  have h₁ := double_gridMid hxy i
  have h₂ := double_gridMid hxz i
  have h₃ := double_gridMid hyz i
  change gridMid x y i + gridMid x z i - gridMid y z i = x i
  omega

end TaskT.HellyFive
