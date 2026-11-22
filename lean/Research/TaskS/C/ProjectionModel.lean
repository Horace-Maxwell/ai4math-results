import Research.TaskS.C.ProjectionLattice
import Research.TaskS.C.ProjectionBody
import Research.TaskS.C.SimplexMeasure
import Research.TaskS.C.Proof

noncomputable section
namespace TaskS.C.MeasureModel

open Challenge Set
open scoped ENNReal BigOperators

/-- Project in lattice coordinates by applying a unimodular coordinate change and
forgetting the first coordinate. -/
def project {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) :
    Space (n+1) →ₗ[ℝ] Space n :=
  LinearMap.pi fun j => (LinearMap.proj j.succ).comp (A.map fun z => (z : ℝ)).toLin'

private theorem project_embed {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (z : Challenge.Lattice (n+1)) :
    project A (embed z) = embed (Fin.tail (A.mulVec z)) := by
  ext j
  change (∑ k, (A j.succ k : ℝ) * (z k : ℝ)) = ((∑ k, A j.succ k * z k : ℤ) : ℝ)
  push_cast
  rfl

private theorem projection_surj {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (hdet : |A.det| = 1) : Function.Surjective (project A) := by
  let B := A.map fun z => (z : ℝ)
  have hB : IsUnit B.det := by
    have h : |B.det| = 1 := by
      change |(A.map fun z => (z : ℝ)).det| = 1
      rw [← Int.cast_det]
      exact_mod_cast hdet
    exact isUnit_iff_ne_zero.mpr (fun he => by simp [he] at h)
  intro x
  obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det B).mpr hB) (Fin.cons (0 : ℝ) x)
  refine ⟨y, ?_⟩
  ext j
  exact congrFun hy j.succ

private theorem projection_lattice {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (hdet : |A.det| = 1) :
    project A '' range (@embed (n+1)) = range (@embed n) := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨_, (project_embed A z).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det A).mpr (Int.isUnit_iff_abs_eq.mpr hdet))
      (Fin.cons (0 : ℤ) z)
    refine ⟨embed y, mem_range_self y, ?_⟩
    rw [project_embed, hy]
    simp

/-- Identify the frozen facet determinant with the normalized Lebesgue measure of
the actual projection of the entire convex hull in adapted quotient coordinates. -/
theorem projection_measure {n : ℕ} (u : Fin (n+2) → Challenge.Lattice (n+1))
    (ω : Fin (n+2) → ℝ) (hi : (0 : Space (n+1)) ∈ interior (simplex (vertices u ω)))
    (i : Fin (n+2)) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (hdet : |A.det| = 1)
    (hu : A.mulVec (u i) = Pi.single 0 1) :
    project A (vertices u ω i) = 0 ∧
    MeasureTheory.volume (project A '' simplex (vertices u ω)) / MeasureTheory.volume (unit n) =
      ENNReal.ofReal (projectedVolume (vertices u ω) u i) := by
  let v := vertices u ω
  let p := project A
  have hp : p (v i) = 0 := by
    change project A (ω i • embed (u i)) = 0
    rw [map_smul, project_embed, hu]
    ext j
    simp [embed,Fin.tail]
  refine ⟨hp, ?_⟩
  let w := fun j => p (v (i.succAbove j))
  have himage : p '' simplex v = simplex w := by
    rw [image_simplex_eq_image_opposite v hi i p hp, p.image_convexHull, ← range_comp]
    rfl
  have hedge : edges w = Matrix.of (fun k j : Fin n =>
      ((A.map fun z => (z : ℝ)).mulVec (v (i.succAbove k.succ) - v (i.succAbove 0))) j.succ) := by
    ext k j
    change (p (v (i.succAbove k.succ)) - p (v (i.succAbove 0))) j =
      p (v (i.succAbove k.succ) - v (i.succAbove 0)) j
    rw [map_sub]
  change MeasureTheory.volume (p '' simplex v) / _ = _
  rw [himage, normalized_measure, volume_edges, hedge]
  exact congrArg ENNReal.ofReal
    (ProjectionLattice.edge_determinant _ _ A hdet hu).symm

/-- The original covering bound with Lebesgue measures of actual projected sets,
normalized by the standard unimodular simplex of the respective lattice. -/
theorem measured_conjectureC {n : ℕ} (u : Fin (n+2) → Challenge.Lattice (n+1))
    (ω : Fin (n+2) → ℝ) (hprim : ∀ i, Primitive (u i)) (hω : ∀ i, 0 < ω i)
    (hv : 0 < volume (vertices u ω)) (hi : (0 : Space (n+1)) ∈ interior (simplex (vertices u ω))) :
    ∃ p : Fin (n+2) → Space (n+1) →ₗ[ℝ] Space n,
      (∀ i, Function.Surjective (p i)) ∧ (∀ i, p i (vertices u ω i) = 0) ∧
      (∀ i, p i '' range (@embed (n+1)) = range (@embed n)) ∧
      (∀ i, MeasureTheory.volume (p i '' simplex (vertices u ω)) / MeasureTheory.volume (unit n) =
        ENNReal.ofReal (projectedVolume (vertices u ω) u i)) ∧
      Covers (simplex (vertices u ω))
        ((∑ i, (MeasureTheory.volume (p i '' simplex (vertices u ω)) /
          MeasureTheory.volume (unit n)).toReal) /
          (2 * (MeasureTheory.volume (simplex (vertices u ω)) /
            MeasureTheory.volume (unit (n+1))).toReal)) := by
  choose A hA he using fun i => ProjectionLattice.exists_adapted (u i) (hprim i)
  have h := fun i => projection_measure u ω hi i (A i) (hA i) (he i)
  refine ⟨fun i => project (A i), fun i => projection_surj (A i) (hA i), fun i => (h i).1,
    fun i => projection_lattice (A i) (hA i), fun i => (h i).2, ?_⟩
  simp_rw [(h _).2, normalized_measure]
  have hp0 (i) : 0 ≤ projectedVolume (vertices u ω) u i := abs_nonneg _
  simp only [ENNReal.toReal_ofReal (hp0 _), ENNReal.toReal_ofReal hv.le]
  exact Proof.conjectureC n u ω hprim hω hv hi

#print axioms measured_conjectureC

end TaskS.C.MeasureModel
