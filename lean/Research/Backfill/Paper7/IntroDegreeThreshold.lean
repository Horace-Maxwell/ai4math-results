import Research.Backfill.Paper7.IntroPrincipalGapBudget
import Research.Backfill.Paper7.ConnectedPerron
import Research.Backfill.Paper7.C61PerronDegreeBound

/-! Degree restrictions from the actual number of eigenvalues above two. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix

namespace Paper7IntroHighBranch
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7IntroCutGap

theorem positive_eigenvector_degree_le_square
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ) (x : V → ℝ)
    (hx : ∀ i, 0 < x i) (he : G.adjMatrix ℝ *ᵥ x = r • x) (i : V) :
    (G.degree i : ℝ) ≤ r ^ 2 := by
  have hrow (j : V) : (∑ k ∈ G.neighborFinset j, x k) = r * x j := by
    simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun he j
  have hneighbor (j : V) (hj : j ∈ G.neighborFinset i) : x i ≤ r * x j := by
    have hi : i ∈ G.neighborFinset j :=
      (G.mem_neighborFinset j i).mpr ((G.mem_neighborFinset i j).mp hj).symm
    have h := Finset.single_le_sum (fun k _ => (hx k).le) hi
    rwa [hrow j] at h
  have hsum := Finset.sum_le_sum hneighbor
  have hbound : (G.degree i : ℝ) * x i ≤ r ^ 2 * x i := by
    calc
      (G.degree i : ℝ) * x i = ∑ j ∈ G.neighborFinset i, x i := by
        simp only [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
      _ ≤ ∑ j ∈ G.neighborFinset i, r * x j := hsum
      _ = r * (∑ j ∈ G.neighborFinset i, x j) := (Finset.mul_sum _ _ _).symm
      _ = r ^ 2 * x i := by rw [hrow i]; ring
  exact (mul_le_mul_iff_left₀ (hx i)).mp hbound
#print axioms Paper7IntroHighBranch.positive_eigenvector_degree_le_square

theorem induced_Ngt_le
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (f : W → V)
    (hf : Function.Injective f) (hAdj : ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j))
    (t : ℝ) : Ngt H t ≤ Ngt G t := by
  have hc := Fintype.card_le_of_injective f hf
  exact (induced_threshold_budget G H f hf hAdj
    (Fintype.card V - Fintype.card W) (by omega) t).1
#print axioms Paper7IntroHighBranch.induced_Ngt_le

theorem component_degree_eq
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : G.ConnectedComponent) (i : C.supp) :
    (G.induce C.supp).degree i = G.degree i.val := by
  apply SimpleGraph.degree_induce_of_neighborSet_subset
  intro j hj
  exact C.mem_supp_of_adj_mem_supp i.property hj
#print axioms Paper7IntroHighBranch.component_degree_eq

theorem Ngt_zero_spectrum_le
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (ht : Ngt G t = 0) :
    ∀ x ∈ spec G, x ≤ t := by
  intro x hx
  by_contra hn
  have hmem : x ∈ (spec G).filter (fun y => t < y) :=
    Multiset.mem_filter.mpr ⟨hx, lt_of_not_ge hn⟩
  have hp : 0 < ((spec G).filter (fun y => t < y)).count x :=
    Multiset.count_pos.mpr hmem
  have hc := Multiset.count_le_card x ((spec G).filter (fun y => t < y))
  change ((spec G).filter (fun y => t < y)).card = 0 at ht
  omega
#print axioms Paper7IntroHighBranch.Ngt_zero_spectrum_le

theorem Ngt_two_zero_degree_le_four
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hzero : Ngt G 2 = 0) :
    ∀ i, G.degree i ≤ 4 := by
  intro i
  let C := G.connectedComponentMk i
  let j : C.supp := ⟨i, rfl⟩
  have hC : (G.induce C.supp).Connected := C.connected_toSimpleGraph
  let : Nonempty C.supp := hC.nonempty
  have hmon := induced_Ngt_le G (G.induce C.supp) Subtype.val
    Subtype.val_injective (by intro a b; rfl) 2
  have hz : Ngt (G.induce C.supp) 2 = 0 := by omega
  obtain ⟨r, hr, x, hx, _hnorm, he, hr0, _hsimple, _hupper, _hdom⟩ :=
    Paper7Admissible.connected_perron (G.induce C.supp) hC
  have hr2 := Ngt_zero_spectrum_le (G.induce C.supp) 2 hz r hr
  have hd := positive_eigenvector_degree_le_square (G.induce C.supp) r x hx he j
  rw [component_degree_eq G C j] at hd
  have hd4 : (G.degree i : ℝ) ≤ 4 := by nlinarith
  exact_mod_cast hd4
#print axioms Paper7IntroHighBranch.Ngt_two_zero_degree_le_four

theorem Ngt_two_positive_of_degree_ge_five
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) (hi : 5 ≤ G.degree i) :
    0 < Ngt G 2 := by
  by_contra hn
  have hz : Ngt G 2 = 0 := by omega
  have hd := Ngt_two_zero_degree_le_four G hz i
  omega
#print axioms Paper7IntroHighBranch.Ngt_two_positive_of_degree_ge_five

theorem Ngt_two_zero_continuation_degree_le_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hzero : Ngt G 2 = 0)
    (i j k : V) (hij : G.Adj i j) (hjk : G.Adj j k) (hki : k ≠ i) :
    G.degree i ≤ 3 := by
  let C := G.connectedComponentMk i
  let a : C.supp := ⟨i, rfl⟩
  have hj : j ∈ C.supp := C.mem_supp_of_adj_mem_supp a.property hij
  have hk : k ∈ C.supp := C.mem_supp_of_adj_mem_supp hj hjk
  have hC : (G.induce C.supp).Connected := C.connected_toSimpleGraph
  let : Nonempty C.supp := hC.nonempty
  have hmon := induced_Ngt_le G (G.induce C.supp) Subtype.val
    Subtype.val_injective (by intro u v; rfl) 2
  have hz : Ngt (G.induce C.supp) 2 = 0 := by omega
  obtain ⟨r, hr, x, hx, _hnorm, he, hr0, _hsimple, _hupper, _hdom⟩ :=
    Paper7Admissible.connected_perron (G.induce C.supp) hC
  have hr2 := Ngt_zero_spectrum_le (G.induce C.supp) 2 hz r hr
  have hd := Paper7C61Higher.degree_lt_eigenvalue_sq (G.induce C.supp) r x hx he
    a ⟨j, hj⟩ ⟨k, hk⟩ hij hjk (by intro h; exact hki (congrArg Subtype.val h))
  rw [component_degree_eq G C a] at hd
  have hd4 : (G.degree i : ℝ) < 4 := by nlinarith
  have hd4' : G.degree i < 4 := by exact_mod_cast hd4
  omega
#print axioms Paper7IntroHighBranch.Ngt_two_zero_continuation_degree_le_three

end Paper7IntroHighBranch
