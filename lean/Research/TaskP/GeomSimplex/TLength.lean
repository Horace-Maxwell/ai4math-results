import Research.TaskP.GeomSimplex.TCoordinates

namespace TaskP.GeomSimplex.Proof

open TaskP.GeomSimplex.Challenge

/-- A linear functional used only to hash the eight lattice points. A negative
table test in the image rules out a cube in the original lattice. -/
private def key (p : Lattice 3) : ℤ := p 0 + 32 * p 1 + 1024 * p 2

private def keys : Fin 8 → ℤ := ![1025, 1123, 3074, 3168, 2081, 2113, 2082, 2114]

private def valid (x : ℤ) : Bool :=
  [1025, 1123, 3074, 3168, 2081, 2113, 2082, 2114].contains x

private theorem key_point (i : Fin 8) : key (tpoints i) = keys i := by fin_cases i <;> decide

private theorem valid_point {p : Lattice 3} (h : realPoint p ∈ simplex verticesT) :
    valid (key p) = true := by
  obtain ⟨i, rfl⟩ := points_of_T h
  rw [key_point]
  fin_cases i <;> decide

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
private theorem noCubeTable : ∀ i j k l : Fin 8, i ≠ j → i ≠ k → i ≠ l →
    valid (keys j + keys k - keys i) = true →
    valid (keys j + keys l - keys i) = true →
    valid (keys k + keys l - keys i) = true →
    valid (keys j + keys k + keys l - 2*keys i) = true → False := by decide

private theorem no_cube (p u v w : Lattice 3) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : ∀ s r t : Bool, realPoint (p + (if s then u else 0) +
      (if r then v else 0) + (if t then w else 0)) ∈ simplex verticesT) : False := by
  have h₀ := h false false false
  have h₁ := h true false false
  have h₂ := h false true false
  have h₃ := h false false true
  have h₁₂ := valid_point (h true true false)
  have h₁₃ := valid_point (h true false true)
  have h₂₃ := valid_point (h false true true)
  have h₁₂₃ := valid_point (h true true true)
  simp at h₀ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ h₁₂₃
  obtain ⟨i, hi⟩ := points_of_T h₀
  obtain ⟨j, hj⟩ := points_of_T h₁
  obtain ⟨k, hk⟩ := points_of_T h₂
  obtain ⟨l, hl⟩ := points_of_T h₃
  have distinct {a : Lattice 3} {m : Fin 8} (ha : a ≠ 0) (hm : p + a = tpoints m) : i ≠ m := by
    rintro rfl
    rw [← hi] at hm
    exact ha (by simpa using hm)
  apply noCubeTable i j k l (distinct hu hj) (distinct hv hk) (distinct hw hl)
  all_goals simp only [← key_point, ← hi, ← hj, ← hk, ← hl]
  · convert h₁₂ using 2
    simp [key]
    ring
  · convert h₁₃ using 2
    simp [key]
    ring
  · convert h₂₃ using 2
    simp [key]
    ring
  · convert h₁₂₃ using 2
    simp [key]
    ring

theorem upperT {k : ℕ} (hp : packs (simplex verticesT) k) : k ≤ 2 := by
  by_contra! hk
  obtain ⟨l, rfl⟩ : ∃ l, k = 3 + l := ⟨k-3, by omega⟩
  obtain ⟨a, b, hn, hc⟩ := pack_endpoints hp
  let A (i : Fin 3) := a (Fin.castAdd l i)
  let B (i : Fin 3) := b (Fin.castAdd l i)
  let tail : Lattice 3 := ∑ i : Fin l, a (Fin.natAdd 3 i)
  let p := A 0 + A 1 + A 2 + tail
  apply no_cube p (B 0 - A 0) (B 1 - A 1) (B 2 - A 2)
  any_goals exact sub_ne_zero.mpr (hn _).symm
  intro s r t
  have h := hc (Fin.addCases (![s,r,t]) (fun _ => false))
  rw [Fin.sum_univ_add] at h
  convert h using 2
  cases s <;> cases r <;> cases t <;>
    simp [p, A, B, tail, Fin.sum_univ_succ] <;> abel

theorem lowerT : packs (simplex verticesT) 2 := by
  let a : Fin 2 → Lattice 3 := ![![1,1,2], ![0,0,0]]
  let b : Fin 2 → Lattice 3 := ![![2,1,2], ![0,1,0]]
  apply pack_of_endpoints (convex_convexHull ..) a b (by decide)
  intro e
  apply (simplexT_int _).mpr
  generalize h0 : e 0 = s
  generalize h1 : e 1 = t
  simp only [Fin.sum_univ_two, h0, h1]
  cases s <;> cases t <;> decide

end TaskP.GeomSimplex.Proof
