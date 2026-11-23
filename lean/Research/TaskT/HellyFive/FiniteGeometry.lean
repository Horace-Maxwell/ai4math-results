import Research.TaskT.HellyFive.Challenge

namespace TaskT.HellyFive.FiniteGeometry
open Set

/-- An integer row used as a supporting or separating linear form. -/
def zdot {n : ℕ} (a p : Grid n) : ℤ := ∑ i, a i * p i

def linearRow {n : ℕ} (a : Grid n) : Space n →ₗ[ℝ] ℝ :=
  ∑ i, (a i : ℝ) • LinearMap.proj i

@[simp] theorem linearRow_apply {n : ℕ} (a : Grid n) (x : Space n) :
    linearRow a x = ∑ i, (a i : ℝ) * x i := by
  simp [linearRow, LinearMap.sum_apply]

@[simp] theorem linearRow_embed {n : ℕ} (a z : Grid n) :
    linearRow a (embed z) = (zdot a z : ℝ) := by simp [zdot, embed]

def poly {n : ℕ} (v : Finset (Grid n)) : Set (Space n) :=
  convexHull ℝ (embed '' (v : Set (Grid n)))

theorem embed_inj {n : ℕ} : Function.Injective (@embed n) := by
  intro p q h
  funext i
  have he : (p i : ℝ) = (q i : ℝ) := congrFun h i
  exact_mod_cast he

theorem dot_bound {n : ℕ} {v : Finset (Grid n)} {h : Grid n} {b : ℤ}
    (hv : ∀ p ∈ v, zdot h p ≤ b) {x : Space n} (hx : x ∈ poly v) :
    linearRow h x ≤ (b : ℝ) := by
  refine convexHull_min (t := {y | linearRow h y ≤ (b : ℝ)}) ?_
    (convex_halfSpace_le (linearRow h).isLinear b) hx
  rintro _ ⟨p, hp, rfl⟩
  change linearRow h (embed p) ≤ (b : ℝ)
  rw [linearRow_embed]
  exact_mod_cast hv p hp

theorem strictly_separated {n : ℕ} {v : Finset (Grid n)} {h z : Grid n}
    (hv : ∀ p ∈ v, zdot h p < zdot h z) : embed z ∉ poly v := by
  intro hz
  have hi : ∀ p ∈ v, zdot h p ≤ zdot h z - 1 := by
    intro p hp
    have := hv p hp
    omega
  have hb := dot_bound hi hz
  rw [linearRow_embed] at hb
  norm_cast at hb
  omega

theorem extremal_of_unique_row {n : ℕ} {v : Finset (Grid n)} {p h : Grid n}
    (hp : p ∈ v) (hv : ∀ q ∈ v, q ≠ p → zdot h q < zdot h p) :
    embed p ∈ (poly v).extremePoints ℝ := by
  let f := linearRow h
  let b := (zdot h p : ℝ)
  let T : Set (Space n) := {x | x = embed p ∨ f x < b}
  have hfp : f (embed p) = b := linearRow_embed h p
  have ht : Convex ℝ T := by
    intro x hx y hy a c ha hc hs
    change x = embed p ∨ f x < b at hx
    change y = embed p ∨ f y < b at hy
    change a • x + c • y = embed p ∨ f (a • x + c • y) < b
    rcases eq_or_lt_of_le ha with haz | ha'
    · have he : a = 0 := haz.symm
      subst a
      simp_all
    rcases eq_or_lt_of_le hc with hcz | hc'
    · have he : c = 0 := hcz.symm
      subst c
      simp_all
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · left; rw [← add_smul, hs, one_smul]
    · right; simp only [map_add, map_smul, smul_eq_mul, hfp]
      nlinarith [congrArg (fun t : ℝ => t * b) hs, mul_lt_mul_of_pos_left hy hc']
    · right; simp only [map_add, map_smul, smul_eq_mul, hfp]
      nlinarith [congrArg (fun t : ℝ => t * b) hs, mul_lt_mul_of_pos_left hx ha']
    · right; simp only [map_add, map_smul, smul_eq_mul]
      nlinarith [congrArg (fun t : ℝ => t * b) hs, mul_lt_mul_of_pos_left hx ha', mul_lt_mul_of_pos_left hy hc']
  have hT : poly v ⊆ T := by
    apply convexHull_min _ ht
    rintro _ ⟨q,hq,rfl⟩
    change embed q = embed p ∨ f (embed q) < b
    by_cases hqp : q=p
    · exact Or.inl (congrArg embed hqp)
    · right; change linearRow h (embed q) < (zdot h p : ℝ)
      rw [linearRow_embed]; exact_mod_cast hv q hq hqp
  refine ⟨subset_convexHull ℝ _ ⟨p,hp,rfl⟩, ?_⟩
  intro x hx y hy hs
  rcases hT hx with hxp | hfx
  · exact hxp
  have hfy : f y ≤ b := by
    rcases hT hy with rfl | hfy
    · exact hfp.le
    · exact hfy.le
  obtain ⟨a,c,ha,hc,hs,hxy⟩ := hs
  have eq := congrArg f hxy
  simp only [map_add, map_smul, smul_eq_mul, hfp] at eq
  nlinarith [congrArg (fun t : ℝ => t * b) hs, mul_lt_mul_of_pos_left hfx ha, mul_le_mul_of_nonneg_left hfy hc.le]

/-- Coordinate bounds are inherited by all points of the convex hull. -/
theorem grid_box {n : ℕ} {v : Finset (Grid n)} {z : Grid n} (hz : embed z ∈ poly v)
    (bounds : ∀ p ∈ v, ∀ i, -1 ≤ p i ∧ p i ≤ 2) :
    ∀ i, -1 ≤ z i ∧ z i ≤ 2 := by
  intro i
  let f : Space n →ₗ[ℝ] ℝ := LinearMap.proj i
  have h : Convex ℝ ({y | (-1 : ℝ) ≤ f y} ∩ {y | f y ≤ (2 : ℝ)}) :=
    (convex_halfSpace_ge f.isLinear _).inter (convex_halfSpace_le f.isLinear _)
  have sub : embed '' (v : Set _) ⊆ ({y | (-1 : ℝ) ≤ f y} ∩ {y | f y ≤ (2 : ℝ)}) := by
    rintro _ ⟨p, hp, rfl⟩
    change (-1 : ℝ) ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ 2
    exact_mod_cast bounds p hp i
  have hr := convexHull_min sub h hz
  change (-1 : ℝ) ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ 2 at hr
  exact_mod_cast hr

theorem midpoint_mem {n : ℕ} {v : Finset (Grid n)} {a b z : Grid n}
    (ha : a ∈ v) (hb : b ∈ v) (mid : ∀ i, a i + b i = 2 * z i) :
    embed z ∈ poly v := by
  have h := (convex_convexHull ℝ (embed '' (v : Set _)))
      (subset_convexHull ℝ _ ⟨a, ha, rfl⟩) (subset_convexHull ℝ _ ⟨b, hb, rfl⟩)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : 1/2 + 1/2 = (1 : ℝ))
  have he : (1/2 : ℝ) • embed a + (1/2 : ℝ) • embed b = embed z := by
    funext i
    change (1/2 : ℝ) * a i + (1/2 : ℝ) * b i = z i
    have hm : (a i : ℝ) + b i = 2 * z i := by exact_mod_cast mid i
    linarith
  rwa [he] at h

abbrev cubeGrid {n : ℕ} (b : Fin n → Fin 4) : Grid n := fun i => (b i : ℕ) - (1 : ℤ)

theorem cube_repr {n : ℕ} {z : Grid n} (hz : ∀ i, -1 ≤ z i ∧ z i ≤ 2) :
    ∃ b : Fin n → Fin 4, cubeGrid b = z := by
  let b : Fin n → Fin 4 := fun i => ⟨(z i+1).toNat, by have := hz i; omega⟩
  refine ⟨b, ?_⟩
  funext i
  have := hz i
  change ((z i + 1).toNat : ℤ) - 1 = z i
  omega

theorem realization {n : ℕ} {v x : Finset (Grid n)}
    (bounds : ∀ p ∈ v, ∀ i, -1 ≤ p i ∧ p i ≤ 2)
    (exp : ∀ p ∈ v, ∃ h, ∀ q ∈ v, q ≠ p → zdot h q < zdot h p)
    (mid : ∀ z ∈ x, z ∉ v ∧ ∃ a ∈ v, ∃ b ∈ v, ∀ i, a i + b i = 2 * z i)
    (cuts : ∀ b : Fin n → Fin 4, cubeGrid b ∈ v ∨ cubeGrid b ∈ x ∨
      ∃ h, ∀ q ∈ v, zdot h q < zdot h (cubeGrid b)) :
    (poly v).extremePoints ℝ = embed '' (v : Set (Grid n)) ∧
    {z : Grid n | embed z ∈ poly v ∧ embed z ∉ (poly v).extremePoints ℝ} = (x : Set _) := by
  have e : (poly v).extremePoints ℝ = embed '' (v : Set (Grid n)) := by
    refine Set.Subset.antisymm extremePoints_convexHull_subset ?_
    rintro _ ⟨p,hp,rfl⟩
    obtain ⟨h,hh⟩ := exp p hp
    exact extremal_of_unique_row hp hh
  refine ⟨e, Set.ext fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨hz,hn⟩
    obtain ⟨b,rfl⟩ := cube_repr (grid_box hz bounds)
    rcases cuts b with hv | hx | ⟨h,hh⟩
    · exact (hn (e.symm ▸ ⟨_,hv,rfl⟩)).elim
    · exact hx
    · exact (strictly_separated hh hz).elim
  · intro hx
    obtain ⟨hn,a,ha,b,hb,hh⟩ := mid z hx
    refine ⟨midpoint_mem ha hb hh, ?_⟩
    rw [e]
    rintro ⟨q,hq,he⟩
    exact hn (embed_inj he ▸ hq)

end TaskT.HellyFive.FiniteGeometry
