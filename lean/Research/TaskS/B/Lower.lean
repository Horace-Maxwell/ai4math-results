import Research.TaskS.B.Challenge
import Research.TaskS.Shared.Sawtooth

namespace TaskS.B
open Challenge
open scoped BigOperators

private def coordProjection {n i : ℕ} (h : i ≤ n) : Space n →ₗ[ℝ] Space i :=
  LinearMap.pi fun j => LinearMap.proj (Fin.castLE h j)

private theorem coord_admissible {n i : ℕ} (h : i ≤ n) :
    LatticeProjection (coordProjection h) := by
  classical
  let extend {α : Type} [Zero α] (f : Fin i → α) (a : Fin n) :=
    if ha : a.val < i then f ⟨a.val,ha⟩ else 0
  have he {α : Type} [Zero α] (f : Fin i → α) (a : Fin i) :
      extend f (Fin.castLE h a) = f a := by simp [extend,a.isLt]
  have hb (w : Challenge.Lattice i) : (∑ j, (w j : ℝ) • Pi.basisFun ℝ (Fin i) j) = embed w := by
    exact (Pi.basisFun ℝ (Fin i)).sum_repr (embed w)
  refine ⟨fun x => ⟨extend x, funext (he x)⟩, Pi.basisFun ℝ (Fin i), ?_⟩
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨fun j => z (Fin.castLE h j), hb _⟩
  · rintro ⟨w,rfl⟩
    refine ⟨extend w, ?_⟩
    dsimp only; rw [hb]; funext j
    change ((extend w (Fin.castLE h j) : ℤ) : ℝ) = _
    rw [he]; rfl

private theorem terminal_weights {n : ℕ} {y : Space n} (hy : y ∈ terminal n) :
    ∃ w : Fin (n+1) → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
      ∀ k, y k = w k.succ - w 0 := by
  classical
  rw [terminal, convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨s,v,hv,hs,hy⟩ := hy
  let w (j : Fin (n+1)) := if j ∈ s then v j else 0
  have hw : ∑ j, w j = 1 := by simpa [w] using hs
  refine ⟨w, fun j => by dsimp [w]; split_ifs <;> simp_all, hw, ?_⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hy
  have hy' : ∑ j, w j • vertex n j = y := by simpa [w,ite_smul] using hy
  intro k
  rw [← hy',Fin.sum_univ_succ]
  simp [vertex,Finset.sum_apply,Pi.single_apply,sub_eq_add_neg,add_comm]

private theorem fract_le_id (a : ℝ) (ha : 0 ≤ a) : Int.fract a ≤ a := by
  have hf : 0 ≤ (⌊a⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr ha
  simp only [Int.fract]; linarith

/-- The standard coordinate projection requires radius at least `i/2` at an
explicit coset with evenly spaced coordinates. -/
theorem exists_projection_lower (n i : ℕ) (_hi : 0 < i) (hin : i ≤ n) :
    ∃ p : Space n →ₗ[ℝ] Space i, LatticeProjection p ∧
      ∀ r : ℝ, 0 ≤ r → Covers p r → (i : ℝ)/2 ≤ r := by
  classical
  refine ⟨coordProjection hin,coord_admissible hin,?_⟩
  intro r hr hcover
  let N := i+1
  let x : Space i := fun k => (k.succ.val : ℝ) / N
  obtain ⟨z,y,hy,hx⟩ := hcover x
  obtain ⟨w,hw,hs,hwy⟩ := terminal_weights hy
  let a := r*w 0
  let hN : N ≤ n+1 := Nat.succ_le_succ hin
  let e : Fin N ↪ Fin (n+1) := Fin.castLEEmb hN
  have hterm (j : Fin N) : Int.fract (a + (j : ℝ)/N) ≤ r * w (e j) := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa [e,a] using fract_le_id (r*w 0) (mul_nonneg hr (hw 0))
    · let t := Fin.castLE hin k
      have heq : a + (k.succ.val : ℝ)/N = r*w t.succ + (z t : ℝ) := by
        have hxh := congrFun hx k
        change (k.succ.val : ℝ)/N = (z t : ℝ) + r * y t at hxh
        rw [hwy] at hxh
        change r*w 0 + (k.succ.val : ℝ)/N = _
        linarith only [hxh]
      rw [heq, Int.fract_add_intCast]
      exact fract_le_id _ (mul_nonneg hr (hw _))
  have hb : (∑ j : Fin N, r*w (e j)) ≤ r := by
    calc
      _ = ∑ k ∈ Finset.univ.map e, r*w k := (Finset.sum_map _ _ _).symm
      _ ≤ ∑ k, r*w k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => mul_nonneg hr (hw k))
      _ = _ := by rw [← Finset.mul_sum, hs, mul_one]
  have htot := (Finset.sum_le_sum (fun j _ => hterm j)).trans hb
  rw [TaskS.Shared.grid_sum N (Nat.succ_pos i) a] at htot
  have hnon := Int.fract_nonneg ((N : ℝ)*a)
  simp only [N,Nat.cast_add,Nat.cast_one] at htot hnon
  linarith

end TaskS.B
