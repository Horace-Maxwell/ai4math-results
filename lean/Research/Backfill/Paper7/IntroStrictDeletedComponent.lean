import Research.Backfill.Paper7.IntroOnePositiveNeutralKernel
import Research.Backfill.Paper7.IntroCoordinateBilinear
import Research.Backfill.Paper7.IntroDeletedHighBranch

/-! At a connected graph's actual vertex cut, one component strictly above two
forces every other component strictly below two when Ngt G 2 is at most one. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroStrictCut
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7Comparison Paper7IntroCutGap
  Paper7IntroHighBranch

theorem adjacency_shift_quadratic_of_unit_eigenvector
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r t : ℝ) (x : V → ℝ)
    (hxnorm : x ⬝ᵥ x = 1) (he : G.adjMatrix ℝ *ᵥ x = r • x) :
    x ⬝ᵥ (G.adjMatrix ℝ - Matrix.scalar V t) *ᵥ x = r - t := by
  have he' : (G.adjMatrix ℝ - Matrix.scalar V t) *ᵥ x = (r - t) • x := by
    rw [Matrix.sub_mulVec, he, Matrix.scalar_apply]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
    ring
  rw [he', dotProduct_smul, hxnorm]
  exact mul_one (r - t)
#print axioms Paper7IntroStrictCut.adjacency_shift_quadratic_of_unit_eigenvector

theorem connected_neutral_zero_coordinate_impossible
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hN : Ngt G 2 ≤ 1) (x y : V → ℝ)
    (hx : 0 < x ⬝ᵥ (G.adjMatrix ℝ - Matrix.scalar V 2) *ᵥ x)
    (hy : y ⬝ᵥ (G.adjMatrix ℝ - Matrix.scalar V 2) *ᵥ y = 0)
    (hxy : x ⬝ᵥ (G.adjMatrix ℝ - Matrix.scalar V 2) *ᵥ y = 0)
    (hyNN : ∀ i, 0 ≤ y i) (hynorm : y ⬝ᵥ y = 1) (v : V) (hyv : y v = 0) : False := by
  have hM : (G.adjMatrix ℝ - Matrix.scalar V 2).IsHermitian :=
    (Paper7Spectrum.realAdjHermitian G).sub
      (by simpa only [Matrix.scalar_apply] using Matrix.isHermitian_diagonal (fun _ : V => (2 : ℝ)))
  have hpos : nPos (G.adjMatrix ℝ - Matrix.scalar V 2) ≤ 1 := by
    rwa [nPos_shift_eq_Ngt]
  have hz := one_positive_neutral_orthogonal_kernel
    (G.adjMatrix ℝ - Matrix.scalar V 2) hM hpos x y hx hy hxy
  have he : G.adjMatrix ℝ *ᵥ y = (2 : ℝ) • y := by
    rw [Matrix.sub_mulVec] at hz
    calc
      G.adjMatrix ℝ *ᵥ y = Matrix.scalar V 2 *ᵥ y := sub_eq_zero.mp hz
      _ = (2 : ℝ) • y := by
        funext i
        simp only [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  have hp := Paper7Admissible.graph_eigenvector_strictly_positive G hG 2 y hyNN hynorm he v
  rw [hyv] at hp
  exact (lt_irrefl (0 : ℝ)) hp
#print axioms Paper7IntroStrictCut.connected_neutral_zero_coordinate_impossible

theorem deleted_component_no_two_of_complement_Ngt_positive
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hN : Ngt G 2 ≤ 1)
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (hK : 0 < Ngt ((vertexDeletedGraph G v).induce
      (C.suppᶜ : Set {w : V // w ≠ v})) 2) :
    (2 : ℝ) ∉ spec ((vertexDeletedGraph G v).induce C.supp) := by
  intro htwo
  let H := vertexDeletedGraph G v
  let F := H.induce C.supp
  let K := H.induce (C.suppᶜ : Set {w : V // w ≠ v})
  have hbudget := deleted_component_threshold_budget G v C 2
  have hzero : Ngt F 2 = 0 := by change Ngt ((vertexDeletedGraph G v).induce C.supp) 2 = 0; omega
  have hF : F.Connected := C.connected_toSimpleGraph
  let : Nonempty C.supp := hF.nonempty
  obtain ⟨r, hr, y, hy, hynorm, heY, _hr0, _hsimple, _hupper, hdom⟩ :=
    Paper7Admissible.connected_perron F hF
  have hrle := Ngt_zero_spectrum_le F 2 hzero r hr
  have hrge := hdom 2 htwo
  have hr2 : r = 2 := by norm_num at hrge; linarith
  rw [hr2] at heY
  obtain ⟨s, hs⟩ := Multiset.card_pos_iff_exists_mem.mp hK
  obtain ⟨hsmem, hs2⟩ := Multiset.mem_filter.mp hs
  obtain ⟨x, hxnorm, heX⟩ := Paper7Admissible.eigs_unit_eigenvector
    (K.adjMatrix ℝ) (Paper7Spectrum.realAdjHermitian K) s hsmem
  let f : C.supp → V := fun i => i.val.val
  let g : ↥(C.suppᶜ : Set {w : V // w ≠ v}) → V := fun i => i.val.val
  have hf : Function.Injective f := by
    intro i j h
    exact Subtype.ext (Subtype.ext h)
  have hg : Function.Injective g := by
    intro i j h
    exact Subtype.ext (Subtype.ext h)
  let M := G.adjMatrix ℝ - Matrix.scalar V 2
  have hMF : M.submatrix f f = F.adjMatrix ℝ - Matrix.scalar C.supp 2 :=
    induced_adjacency_shift G F f hf (by intro i j; rfl) 2
  have hMK : M.submatrix g g = K.adjMatrix ℝ -
      Matrix.scalar ↥(C.suppᶜ : Set {w : V // w ≠ v}) (2 : ℝ) :=
    induced_adjacency_shift G K g hg (by intro i j; rfl) 2
  have hcross : M.submatrix g f = 0 := by
    ext i j
    have hne : g i ≠ f j := by
      intro hij
      apply i.property
      have hv : i.val = j.val := Subtype.ext hij
      rw [hv]
      exact j.property
    have hno : ¬G.Adj (g i) (f j) := by
      intro hij
      have hji : H.Adj j.val i.val := hij.symm
      exact i.property (C.mem_supp_of_adj_mem_supp j.property hji)
    change (if G.Adj (g i) (f j) then (1 : ℝ) else 0) -
      (if g i = f j then 2 else 0) = 0
    rw [ite_eq_right hno, ite_eq_right hne, sub_self]
  let X := coordinateInclusion g *ᵥ x
  let Y := coordinateInclusion f *ᵥ y
  have hX : 0 < X ⬝ᵥ M *ᵥ X := by
    change 0 < (coordinateInclusion g *ᵥ x) ⬝ᵥ M *ᵥ (coordinateInclusion g *ᵥ x)
    rw [coordinateInclusion_bilinear, hMK,
      adjacency_shift_quadratic_of_unit_eigenvector K s 2 x hxnorm heX]
    exact sub_pos.mpr hs2
  have hY : Y ⬝ᵥ M *ᵥ Y = 0 := by
    change (coordinateInclusion f *ᵥ y) ⬝ᵥ M *ᵥ (coordinateInclusion f *ᵥ y) = 0
    rw [coordinateInclusion_bilinear, hMF,
      adjacency_shift_quadratic_of_unit_eigenvector F 2 2 y hynorm heY, sub_self]
  have hXY : X ⬝ᵥ M *ᵥ Y = 0 := by
    change (coordinateInclusion g *ᵥ x) ⬝ᵥ M *ᵥ (coordinateInclusion f *ᵥ y) = 0
    rw [coordinateInclusion_bilinear, hcross, Matrix.zero_mulVec, dotProduct_zero]
  have hYNN : ∀ i, 0 ≤ Y i := coordinateInclusion_nonnegative f y (fun i => (hy i).le)
  have hYnorm : Y ⬝ᵥ Y = 1 := (coordinateInclusion_dot_self f hf y).trans hynorm
  have hYv : Y v = 0 := coordinateInclusion_outside_zero f y v (fun i => Ne.symm i.val.property)
  exact connected_neutral_zero_coordinate_impossible G hG hN X Y hX hY hXY hYNN hYnorm v hYv
#print axioms Paper7IntroStrictCut.deleted_component_no_two_of_complement_Ngt_positive

theorem deleted_component_spectrum_lt_two_of_complement_Ngt_positive
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hN : Ngt G 2 ≤ 1)
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (hK : 0 < Ngt ((vertexDeletedGraph G v).induce
      (C.suppᶜ : Set {w : V // w ≠ v})) 2) :
    ∀ r ∈ spec ((vertexDeletedGraph G v).induce C.supp), r < 2 := by
  have hbudget := deleted_component_threshold_budget G v C 2
  have hzero : Ngt ((vertexDeletedGraph G v).induce C.supp) 2 = 0 := by omega
  have hno := deleted_component_no_two_of_complement_Ngt_positive G hG hN v C hK
  intro r hr
  have hrle := Ngt_zero_spectrum_le ((vertexDeletedGraph G v).induce C.supp) 2 hzero r hr
  exact lt_of_le_of_ne hrle (fun h => hno (h ▸ hr))
#print axioms Paper7IntroStrictCut.deleted_component_spectrum_lt_two_of_complement_Ngt_positive

end Paper7IntroStrictCut
