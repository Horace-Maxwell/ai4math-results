import Research.TaskP.GeomSimplex.UUpper
import Research.TaskP.GeomSimplex.ULower

namespace TaskP.GeomSimplex.Proof

open TaskP.GeomSimplex.Challenge

private theorem only_vertices {p : Lattice 3} (hp : realPoint p ∈ simplex verticesU) :
    ∃ i : Fin 4, p = verticesU i := by
  have hp' : realPoint p ∈ dilate 1 (simplex verticesU) := by simpa [dilate] using hp
  have h := (dilateU_int 1 (by decide) p).1 hp'
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  have h₃ := h 3
  norm_num [budget, uform] at h₀ h₁ h₂ h₃
  have hv :
      (p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0) ∨ (p 0 = 1 ∧ p 1 = 0 ∧ p 2 = 0) ∨
      (p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 1) ∨ (p 0 = 13 ∧ p 1 = 18 ∧ p 2 = 1) := by
    have hz : p 2 = 0 ∨ p 2 = 1 := by omega
    rcases hz with hz | hz
    · omega
    · have hy : p 1 ≤ 18 := by omega
      interval_cases h' : p 1 <;> omega
  rcases hv with h | h | h | h
  · exact ⟨0, funext <| by intro j; fin_cases j <;> tauto⟩
  · exact ⟨1, funext <| by intro j; fin_cases j <;> tauto⟩
  · exact ⟨2, funext <| by intro j; fin_cases j <;> tauto⟩
  · exact ⟨3, funext <| by intro j; fin_cases j <;> tauto⟩

private theorem no_parallelogram {a b c d : Lattice 3}
    (ha : realPoint a ∈ simplex verticesU) (hb : realPoint b ∈ simplex verticesU)
    (hc : realPoint c ∈ simplex verticesU) (hd : realPoint d ∈ simplex verticesU)
    (hab : a ≠ b) (hac : a ≠ c) (heq : a + d = b + c) : False := by
  obtain ⟨i, rfl⟩ := only_vertices ha
  obtain ⟨j, rfl⟩ := only_vertices hb
  obtain ⟨k, rfl⟩ := only_vertices hc
  obtain ⟨l, rfl⟩ := only_vertices hd
  have table : ∀ i j k l : Fin 4, verticesU i ≠ verticesU j → verticesU i ≠ verticesU k →
      verticesU i + verticesU l ≠ verticesU j + verticesU k := by decide
  exact table i j k l hab hac heq

theorem length_oneU : lengthIs (simplex verticesU) 1 := by
  constructor
  · apply pack_of_endpoints (convex_convexHull ..) (fun _ => verticesU 0) (fun _ => verticesU 1)
    · intro _
      decide
    · intro e
      simp only [Fin.sum_univ_one]
      split <;> exact vertex_mem _ _
  · intro k hp
    by_contra! hk
    obtain ⟨l, rfl⟩ : ∃ l, k = 2 + l := ⟨k-2, by omega⟩
    obtain ⟨a, b, hn, h⟩ := pack_endpoints hp
    let a₀ := a (Fin.castAdd l (0 : Fin 2))
    let a₁ := a (Fin.castAdd l (1 : Fin 2))
    let b₀ := b (Fin.castAdd l (0 : Fin 2))
    let b₁ := b (Fin.castAdd l (1 : Fin 2))
    let tail : Lattice 3 := ∑ i : Fin l, a (Fin.natAdd 2 i)
    have hc (s r : Bool) : realPoint
        (((if s then b₀ else a₀) + (if r then b₁ else a₁)) + tail) ∈ simplex verticesU := by
      have hw := h (Fin.addCases (![s,r]) (fun _ => false))
      rw [Fin.sum_univ_add] at hw
      cases s <;> cases r <;> simpa [Fin.sum_univ_two, tail, a₀, a₁, b₀, b₁] using hw
    apply no_parallelogram (hc false false) (hc true false) (hc false true) (hc true true)
    · simpa [a₀, b₀] using hn (Fin.castAdd l (0 : Fin 2))
    · simpa [a₁, b₁] using hn (Fin.castAdd l (1 : Fin 2))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      abel

theorem TetrahedronDilations : TetrahedronDilations := by
  have ht (t : ℕ) (h : 2 ≤ t) : lengthIs (dilate t (simplex verticesU)) (3*t) :=
    ⟨lowerU h, fun _ hp => upperU (by omega) hp⟩
  exact ⟨fullU, length_oneU, ht, not_quasiLinear length_oneU ht⟩

end TaskP.GeomSimplex.Proof
