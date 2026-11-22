import Research.TaskP.GeomSimplex.PyramidGeometry

namespace TaskP.GeomSimplex.Proof

open TaskP.GeomSimplex.Challenge

theorem pyramid_base_mem {d : ℕ} (v : Fin (d + 1) → Lattice d) {q : Lattice d}
    (hq : realPoint q ∈ simplex v) :
    realPoint (Fin.cons 0 q) ∈ simplex (pyrVertices v) := by
  rw [mem_simplex_mass, mass_pyramid]
  have e₀ : realPoint (Fin.cons 0 q) 0 = 0 := by simp [realPoint]
  have et : (fun i : Fin d => realPoint (Fin.cons 0 q) i.succ) = realPoint q := by
    ext i
    simp [realPoint]
  rw [e₀, et, sub_zero]
  exact ⟨le_rfl, (mem_simplex_mass _ _).mp hq⟩

theorem pyramid_lattice_cases {d : ℕ} (v : Fin (d + 1) → Lattice d)
    {p : Challenge.Lattice (d + 1)} (h : realPoint p ∈ simplex (pyrVertices v)) :
    (∃ q : Lattice d, p = Fin.cons 0 q ∧ realPoint q ∈ simplex v) ∨
      p = Fin.cons 1 0 := by
  rw [mem_simplex_mass, mass_pyramid] at h
  have hl : (0 : ℝ) ≤ p 0 := h.1
  have hu : (0 : ℝ) ≤ 1 - (p 0 : ℝ) := mass_nonneg h.2
  have hlow : 0 ≤ p 0 := by exact_mod_cast hl
  have hupp : p 0 ≤ 1 := by exact_mod_cast (show (p 0 : ℝ) ≤ 1 by linarith)
  have hz : p 0 = 0 ∨ p 0 = 1 := by omega
  rcases hz with h₀ | h₁
  · left
    refine ⟨fun i => p i.succ, ?_, (mem_simplex_mass _ _).2 ?_⟩
    · ext i
      exact Fin.cases (by simpa using h₀) (fun _ => rfl) i
    · have eh : realPoint p 0 = 0 := by simp [realPoint, h₀]
      have target := h.2
      rw [eh, sub_zero] at target
      exact target
  · right
    have hzero := (mass_zero_iff v (fun i => realPoint p i.succ)).1
      (by simpa [realPoint, h₁] using h.2)
    ext i
    refine Fin.cases (by simpa using h₁) (fun j => ?_) i
    have hz := congrFun hzero j
    exact_mod_cast (show (p j.succ : ℝ) = 0 from hz)

private theorem tail_collinear {d : ℕ} {a b c : Challenge.Lattice (d + 1)}
    (h : Collinear ℝ ({realPoint a, realPoint b, realPoint c} : Set (Space (d + 1)))) :
    Collinear ℝ ({realPoint (fun i => a i.succ), realPoint (fun i => b i.succ),
                 realPoint (fun i => c i.succ)} : Set (Space d)) := by
  obtain ⟨o, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp h
  apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
  refine ⟨fun i => o i.succ, fun i => v i.succ, ?_⟩
  have lift (x : Challenge.Lattice (d + 1)) (hx : realPoint x ∈
      ({realPoint a, realPoint b, realPoint c} : Set (Space (d + 1)))) :
      ∃ r : ℝ, realPoint (fun i => x i.succ) =
        r • (fun i : Fin d => v i.succ) +ᵥ (fun i : Fin d => o i.succ) := by
    obtain ⟨r, hr⟩ := hv _ hx
    exact ⟨r, funext fun i => congrFun hr i.succ⟩
  intro x hx
  rcases hx with rfl | rfl | hx
  · exact lift a (by simp)
  · exact lift b (by simp)
  · rw [Set.mem_singleton_iff] at hx
    subst x
    exact lift c (by simp)

private theorem base_eq_on_apex_line {d : ℕ} (a b : Lattice d)
    {S : Set (Space (d + 1))} (hs : Collinear ℝ S)
    (ha : realPoint (Fin.cons 0 a) ∈ S) (hb : realPoint (Fin.cons 0 b) ∈ S)
    (ht : realPoint (Fin.cons 1 (0 : Lattice d)) ∈ S) : a = b := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem ht).mp hs
  obtain ⟨r, hr⟩ := hv _ ha
  obtain ⟨s, hs⟩ := hv _ hb
  have er := congrFun hr 0
  have es := congrFun hs 0
  simp [realPoint] at er es
  have hn : v 0 ≠ 0 := by rintro h; rw [h] at er; linarith
  have hrs : r = s := (mul_right_cancel₀ hn) (by linarith : r * v 0 = s * v 0)
  rw [hrs, ← hs] at hr
  ext i
  exact_mod_cast (show (a i : ℝ) = (b i : ℝ) from congrFun hr i.succ)

theorem diameter_pyramid {d : ℕ} (v : Fin (d + 1) → Lattice d)
    (h : diameterOne (simplex v)) : diameterOne (simplex (pyrVertices v)) := by
  obtain ⟨a,b,hab,ha,hb⟩ := h.1
  refine ⟨⟨Fin.cons 0 a, Fin.cons 0 b, ?_, pyramid_base_mem v ha, pyramid_base_mem v hb⟩, ?_⟩
  · intro he
    exact hab (funext fun i => congrFun he i.succ)
  intro x y z hx hy hz hcol
  rcases pyramid_lattice_cases v hx with ⟨x, rfl, hxBase⟩ | rfl <;>
    rcases pyramid_lattice_cases v hy with ⟨y, rfl, hyBase⟩ | rfl <;>
    rcases pyramid_lattice_cases v hz with ⟨z, rfl, hzBase⟩ | rfl
  · have ht := tail_collinear hcol
    have hh := h.2 x y z hxBase hyBase hzBase ht
    rcases hh with rfl | rfl | rfl <;> simp
  · have he := base_eq_on_apex_line x y hcol (by simp) (by simp) (by simp)
    simp [he]
  · have he := base_eq_on_apex_line x z hcol (by simp) (by simp) (by simp)
    simp [he]
  · simp
  · have he := base_eq_on_apex_line y z hcol (by simp) (by simp) (by simp)
    simp [he]
  all_goals simp

end TaskP.GeomSimplex.Proof
