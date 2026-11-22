import Research.TaskP.GeomSimplex.PyramidCorners
import Research.TaskP.GeomSimplex.PyramidGeometry
namespace TaskP.GeomSimplex.Proof
open TaskP.GeomSimplex.Challenge

private theorem convex_dilate {d : ℕ} (v : Fin (d+1) → Lattice d) (t : ℕ) :
    Convex ℝ (dilate t (simplex v)) := by
  exact (show Convex ℝ (simplex v) from convex_convexHull ℝ _).linear_image
    ((t : ℝ) • (LinearMap.id : Space d →ₗ[ℝ] Space d))

private theorem lift_pack {d k t : ℕ} (v : Fin (d+1) → Lattice d) (ht : 0 < t)
    (h : packs (dilate t (simplex v)) k) :
    packs (dilate t (simplex (pyrVertices v))) k := by
  obtain ⟨a,b,hab,he⟩ := pack_endpoints h
  let base (z : Lattice d) : Challenge.Lattice (d+1) := Fin.cons 0 z
  apply pack_of_endpoints (convex_dilate _ _) (fun i => base (a i)) (fun i => base (b i))
  · intro i eq
    exact hab i (funext fun j => congrFun eq j.succ)
  · intro e
    let x := ∑ i, if e i then base (b i) else base (a i)
    change realPoint x ∈ _
    rw [mem_dilate_mass _ _ ht,mass_pyramid]
    have h₀ : realPoint x 0 = 0 := by
      simp [realPoint,x,base,Finset.sum_apply,ite_apply]
    rw [h₀,sub_zero]
    refine ⟨le_rfl,?_⟩
    convert (mem_dilate_mass _ _ ht _).mp (he e) using 2
    simp [realPoint,x,base,Finset.sum_apply,ite_apply]

private theorem cast_translate {d : ℕ} (z u v : Lattice d) (L R : ℤ) :
    realPoint (z + (L • u + R • v)) =
      realPoint z + ((L : ℝ) • realPoint u + (R : ℝ) • realPoint v) := by
  ext i
  simp [realPoint,Pi.add_apply,Pi.smul_apply,zsmul_eq_mul]

private theorem descend_pack {d k t : ℕ} (v : Fin (d+1) → Lattice d)
    (i j : Fin (d+1)) (hne : v i ≠ v j) (ht : 0<t) (hk : 0<k)
    (h : packs (dilate t (simplex (pyrVertices v))) k) : packs (dilate t (simplex v)) k := by
  obtain ⟨a,b,hab,he⟩ := pack_endpoints h
  have slice (e : Fin k → Bool) :=
    (mass_pyramid v _ _).mp ((mem_dilate_mass _ _ ht _).mp (he e))
  have floor' (e : Fin k → Bool) : 0 ≤ corner a b e 0 := by
    have h₀ : (0 : ℝ) ≤ ((corner a b e 0 : ℤ) : ℝ) := (slice e).1
    exact_mod_cast h₀
  obtain ⟨H,A,B,hd,go⟩ := replace_rising a b hab floor' _ _ hne
  apply translated_pack hk (convex_dilate _ _) (H • v i) A B hd
  intro e
  obtain ⟨e',r,hr,hR,hh,eq⟩ := go e
  rw [mem_dilate_mass _ _ ht,eq,cast_translate]
  have old := (slice e').2
  change mass v ((t:ℝ) - ((corner a b e' 0:ℤ):ℝ)) (realPoint (tailPoint (corner a b e'))) at old
  rw [hh] at old
  have lo := mass_smul (a:=((H-r:ℤ):ℝ)) (by exact_mod_cast sub_nonneg.mpr hR) (mass_vertex v i)
  have hi := mass_smul (a:=(r:ℝ)) (by exact_mod_cast hr) (mass_vertex v j)
  have all := mass_add old (mass_add lo hi)
  convert all using 1
  push_cast
  ring

theorem pyramid_length {d n t : ℕ} (v : Fin (d+1) → Lattice d) (hd : 0 < d)
    (hv : fullSimplex v) (ht : 0 < t) (h : lengthIs (dilate t (simplex v)) n) :
    lengthIs (dilate t (simplex (pyrVertices v))) n := by
  refine ⟨lift_pack v ht h.1,fun k hk => ?_⟩
  by_cases hzero : k=0
  · omega
  let j := Fin.last d
  have hj : (0 : Fin (d+1)) ≠ j := by
    intro eq
    have := congrArg Fin.val eq
    simp [j] at this
    omega
  have hne : v 0 ≠ v j := fun eq => hj (hv.injective (congrArg realPoint eq))
  exact h.2 _ (descend_pack v 0 j hne ht (by omega) hk)

end TaskP.GeomSimplex.Proof
