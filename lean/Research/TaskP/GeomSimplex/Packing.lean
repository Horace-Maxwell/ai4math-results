import Research.TaskP.GeomSimplex.Challenge

namespace TaskP.GeomSimplex.Proof

open TaskP.GeomSimplex.Challenge
open scoped Pointwise

theorem length_unique {d n m : ℕ} {P : Set (Space d)}
    (hn : lengthIs P n) (hm : lengthIs P m) : n = m :=
  Nat.le_antisymm (hm.2 _ hn.1) (hn.2 _ hm.1)

theorem not_quasiLinear {d : ℕ} {P : Set (Space d)} (h : lengthIs P 1)
    (ht : ∀ t : ℕ, 2 ≤ t → lengthIs (dilate t P) (3 * t)) : ¬ quasiLinearLengths P := by
  rintro ⟨k, hk, f, g, hq⟩
  obtain ⟨n₀, h₀, e₀⟩ := hq 1 (by decide)
  obtain ⟨n₁, h₁, e₁⟩ := hq (1 + k) (by omega)
  obtain ⟨n₂, h₂, e₂⟩ := hq ((1 + k) + k) (by omega)
  have hp : dilate 1 P = P := by simp [dilate]
  rw [hp] at h₀
  rw [length_unique h₀ h] at e₀
  rw [length_unique h₁ (ht _ (by omega))] at e₁
  rw [length_unique h₂ (ht _ (by omega))] at e₂
  simp only [Nat.add_mod_right, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_ofNat, mul_one] at e₀ e₁ e₂
  linarith

theorem vertex_mem {d : ℕ} (v : Fin (d + 1) → Lattice d) (i : Fin (d + 1)) :
    realPoint (v i) ∈ simplex v :=
  subset_convexHull ℝ _ ⟨i, rfl⟩

theorem vertex_in_polytope {d : ℕ} {s : Finset (Lattice d)} {a : Lattice d} (ha : a ∈ s) :
    realPoint a ∈ polytope s := subset_convexHull ℝ _ ⟨a, ha, rfl⟩

theorem realPoint_sum {d k : ℕ} (a : Fin k → Lattice d) :
    realPoint (∑ i, a i) = ∑ i, realPoint (a i) := by
  ext j
  simp [realPoint, Finset.sum_apply]

theorem pack_endpoints {d k : ℕ} {P : Set (Space d)} (h : packs P k) :
    ∃ a b : Fin k → Lattice d, (∀ i, a i ≠ b i) ∧
      ∀ e : Fin k → Bool, realPoint (∑ i, if e i then b i else a i) ∈ P := by
  classical
  obtain ⟨v, hv, hP⟩ := h
  choose a b ha hb hab using fun i => Finset.one_lt_card_iff.mp (hv i)
  refine ⟨a, b, hab, fun e => ?_⟩
  rw [realPoint_sum]
  apply hP
  intro i
  apply vertex_in_polytope
  split <;> solve_by_elim

theorem pack_of_endpoints {d k : ℕ} {P : Set (Space d)} (hP : Convex ℝ P)
    (a b : Fin k → Lattice d) (hab : ∀ i, a i ≠ b i)
    (corners : ∀ e : Fin k → Bool, realPoint (∑ i, if e i then b i else a i) ∈ P) :
    packs P k := by
  classical
  let V (i : Fin k) : Finset (Lattice d) := {a i, b i}
  refine ⟨V, fun i => by simp [V, hab i], fun x hx => ?_⟩
  let A (i : Fin k) := realPoint '' (V i : Set (Lattice d))
  have contained : (∑ i, A i) ⊆ P := by
    intro z hz
    obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_sum _ _).mp hz
    have hs (i : Fin k) : g i = realPoint (a i) ∨ g i = realPoint (b i) := by
      obtain ⟨c, hc, he⟩ := hg i
      rcases (show c = a i ∨ c = b i by simpa [V] using hc) with rfl | rfl <;> tauto
    let e (i : Fin k) := decide (g i = realPoint (b i))
    convert corners e using 1
    rw [realPoint_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : g i = realPoint (b i)
    · simp [e, h]
    · simpa [e, h] using (hs i).resolve_right h
  have hHull := convexHull_min contained hP
  rw [convexHull_sum] at hHull
  apply hHull
  exact (Set.mem_fintype_sum _ _).mpr ⟨x, hx, rfl⟩

end TaskP.GeomSimplex.Proof
