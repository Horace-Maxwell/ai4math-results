import Research.Backfill.Paper7.IntroStrictDeletedComponent
import Research.Backfill.Paper7.IntroR3HighVertexSeparation

/-! Strict cut constraints retain an original high vertex even when it is adjacent
to the deleted vertex. These are universal helpers, not a complete classification. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroStrictCut
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7IntroCutGap Paper7IntroHighBranch
  Paper7IntroHighVertex Paper7OddIntegral

theorem deleted_component_degree_le_three_of_complement_Ngt_positive
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hN : Ngt G 2 ≤ 1)
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (hK : 0 < Ngt ((vertexDeletedGraph G v).induce
      (C.suppᶜ : Set {w : V // w ≠ v})) 2) :
    ∀ i, ((vertexDeletedGraph G v).induce C.supp).degree i ≤ 3 := by
  have hC : ((vertexDeletedGraph G v).induce C.supp).Connected := C.connected_toSimpleGraph
  let : Nonempty C.supp := hC.nonempty
  obtain ⟨r, hr, x, hx, _hnorm, he, hr0, _hsimple, _hupper, _hdom⟩ :=
    Paper7Admissible.connected_perron ((vertexDeletedGraph G v).induce C.supp) hC
  have hr2 := deleted_component_spectrum_lt_two_of_complement_Ngt_positive
    G hG hN v C hK r hr
  intro i
  have hd := positive_eigenvector_degree_le_square
    ((vertexDeletedGraph G v).induce C.supp) r x hx he i
  have hd4 : (((vertexDeletedGraph G v).induce C.supp).degree i : ℝ) < 4 := by nlinarith
  have hdNat : ((vertexDeletedGraph G v).induce C.supp).degree i < 4 := by exact_mod_cast hd4
  omega
#print axioms Paper7IntroStrictCut.deleted_component_degree_le_three_of_complement_Ngt_positive

theorem high_original_component_complement_Ngt_two_zero
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hN : Ngt G 2 ≤ 1)
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (i : C.supp) (hi : 5 ≤ G.degree i.val.val) :
    Ngt ((vertexDeletedGraph G v).induce
      (C.suppᶜ : Set {w : V // w ≠ v})) 2 = 0 := by
  by_contra hne
  have hp : 0 < Ngt ((vertexDeletedGraph G v).induce
      (C.suppᶜ : Set {w : V // w ≠ v})) 2 := Nat.pos_of_ne_zero hne
  have hd := deleted_component_degree_le_three_of_complement_Ngt_positive G hG hN v C hp i
  have hrestore := deleted_component_original_degree_restore G v C i
  split_ifs at hrestore <;> omega
#print axioms Paper7IntroStrictCut.high_original_component_complement_Ngt_two_zero

theorem high_original_component_two_regular_no_boundary
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hN : Ngt G 2 ≤ 1)
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (i : C.supp) (hi : 5 ≤ G.degree i.val.val)
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (f : W → {u : {w : V // w ≠ v} // u ∉ C.supp})
    (hf : Function.Injective f)
    (hAdj : ∀ a b, H.Adj a b ↔
      ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).Adj (f a) (f b))
    (hd : ∀ a, H.degree a = 2)
    (z : {u : {w : V // w ≠ v} // u ∉ C.supp}) (hz : ∀ a, z ≠ f a) (w : W) :
    ¬((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).Adj z (f w) := by
  exact Ngt_two_zero_two_regular_no_boundary
    ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v}))
    (high_original_component_complement_Ngt_two_zero G hG hN v C i hi)
    H f hf hAdj hd z hz w
#print axioms Paper7IntroStrictCut.high_original_component_two_regular_no_boundary

theorem intro21_even_decorated_core_branch_degree_le_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (S : Set {u : {w : V // w ≠ v} // u ∉ C.supp})
    (hd : ∀ i, (((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).induce S).degree i = 2)
    (z : {u : {w : V // w ≠ v} // u ∉ C.supp}) (hz : z ∉ S) (w : S)
    (hzw : ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).Adj z w.val) :
    ∀ i, ((vertexDeletedGraph G v).induce C.supp).degree i ≤ 3 := by
  have hp : 0 < Ngt ((vertexDeletedGraph G v).induce
      (C.suppᶜ : Set {w : V // w ≠ v})) 2 := by
    by_contra hnp
    have hz0 : Ngt ((vertexDeletedGraph G v).induce
        (C.suppᶜ : Set {w : V // w ≠ v})) 2 = 0 := by omega
    apply Ngt_two_zero_two_regular_no_boundary
      ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})) hz0
      (((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).induce S) Subtype.val
      Subtype.val_injective (by intro a b; rfl) hd z
      (fun j h => hz (h.symm ▸ j.property)) w
    exact hzw
  exact deleted_component_degree_le_three_of_complement_Ngt_positive G hG.1
    (intro21_even_Ngt_two_le_one G b hG hI hn hb) v C hp
#print axioms Paper7IntroStrictCut.intro21_even_decorated_core_branch_degree_le_three

theorem intro21_even_radius_three_high_vertex_complement_zero
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (hthree : (integerSpectrum G).count 3 = 1) :
    ∃ u : V, 5 ≤ G.degree u ∧
      ∀ (v : V) (huv : u ≠ v)
        (C : (vertexDeletedGraph G v).ConnectedComponent),
        (⟨u, huv⟩ : {w : V // w ≠ v}) ∈ C.supp →
        Ngt ((vertexDeletedGraph G v).induce
          (C.suppᶜ : Set {w : V // w ≠ v})) 2 = 0 := by
  obtain ⟨u, hu⟩ := intro21_even_radius_three_exists_degree_ge_five G b hG hI hn hb hthree
  refine ⟨u, hu, ?_⟩
  intro v huv C huC
  exact high_original_component_complement_Ngt_two_zero G hG.1
    (intro21_even_Ngt_two_le_one G b hG hI hn hb) v C ⟨⟨u, huv⟩, huC⟩ hu
#print axioms Paper7IntroStrictCut.intro21_even_radius_three_high_vertex_complement_zero

end Paper7IntroStrictCut
