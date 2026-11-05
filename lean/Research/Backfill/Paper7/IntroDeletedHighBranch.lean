import Research.Backfill.Paper7.IntroTwoRegularBoundary
import Research.Backfill.Paper7.IntroComponentThresholdPartition
import Research.Backfill.Paper7.IntroSeparatedPartitionSpectrum
import Research.Backfill.Paper7.IntroDeletedVertexGap
import Research.Backfill.Paper7.IntroEvenRadiusFourExclusion

/-! Actual large branching components cannot coexist after a single deletion. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroHighBranch
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7IntroCutGap Paper7OddIntegral

theorem integral_connected_Ngt_two_le_one
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hI : IsIntegralGraph G) (hbound : ∀ x ∈ spec G, x ≤ 3) : Ngt G 2 ≤ 1 := by
  have hfilter : (spec G).filter (fun x : ℝ => 2 < x) =
      (spec G).filter (fun x : ℝ => x = 3) := by
    apply Multiset.filter_congr
    intro x hx
    constructor
    · intro hx2
      have hx3 := hbound x hx
      rw [← integerSpectrum_cast G hI] at hx
      obtain ⟨z, _hz, rfl⟩ := Multiset.mem_map.mp hx
      have hz2 : (2 : ℤ) < z := by exact_mod_cast hx2
      have hz3 : z ≤ (3 : ℤ) := by exact_mod_cast hx3
      have hz : z = 3 := by omega
      exact_mod_cast hz
    · intro hx3
      rw [hx3]
      norm_num
  have hcount : Ngt G 2 = mult G 3 := by
    change ((spec G).filter (fun x : ℝ => 2 < x)).card = (spec G).count 3
    rw [hfilter, Multiset.filter_eq', Multiset.card_replicate]
  rw [hcount]
  by_cases hthree : (3 : ℝ) ∈ spec G
  · let : Nonempty V := hG.nonempty
    obtain ⟨r, hr, _x, _hx, _hnorm, _he, _hr0, hsimple, _hupper, hdom⟩ :=
      Paper7Admissible.connected_perron G hG
    have hr3 := hbound r hr
    have h3r := hdom 3 hthree
    norm_num at h3r
    have hr : r = 3 := by linarith
    rw [hr] at hsimple
    exact hsimple.le
  · have hz : (spec G).count (3 : ℝ) = 0 := Multiset.count_eq_zero.mpr hthree
    change (spec G).count (3 : ℝ) ≤ 1
    omega
#print axioms Paper7IntroHighBranch.integral_connected_Ngt_two_le_one

theorem intro21_even_Ngt_two_le_one
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b) : Ngt G 2 ≤ 1 := by
  apply integral_connected_Ngt_two_le_one G hG.1 hI
  intro x hx
  exact (le_abs_self x).trans
    (Paper7IntroFour.intro21_even_spectrum_abs_le_three G b hG hI hn hb x hx)
#print axioms Paper7IntroHighBranch.intro21_even_Ngt_two_le_one

theorem separated_partition_Ngt
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ¬G.Adj i j) (t : ℝ) :
    Ngt G t = Ngt (G.induce S) t + Ngt (G.induce (Sᶜ)) t := by
  unfold Ngt
  rw [separated_partition_spec G S hsep, Multiset.filter_add, Multiset.card_add]
#print axioms Paper7IntroHighBranch.separated_partition_Ngt

theorem deleted_component_threshold_budget
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent) (t : ℝ) :
    Ngt ((vertexDeletedGraph G v).induce C.supp) t +
      Ngt ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})) t ≤ Ngt G t := by
  exact induced_component_threshold_budget G (vertexDeletedGraph G v)
    (fun x : {w : V // w ≠ v} => x.val) Subtype.val_injective
    (by intro i j; rfl) C t
#print axioms Paper7IntroHighBranch.deleted_component_threshold_budget

theorem intro21_even_high_component_complement_degree_le_four
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (i : C.supp) (hi : 5 ≤ ((vertexDeletedGraph G v).induce C.supp).degree i) :
    ∀ j, ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).degree j ≤ 4 := by
  have hp := Ngt_two_positive_of_degree_ge_five
    ((vertexDeletedGraph G v).induce C.supp) i hi
  have hbudget := deleted_component_threshold_budget G v C 2
  have htotal := intro21_even_Ngt_two_le_one G b hG hI hn hb
  have hz : Ngt ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})) 2 = 0 := by omega
  exact Ngt_two_zero_degree_le_four _ hz
#print axioms Paper7IntroHighBranch.intro21_even_high_component_complement_degree_le_four

theorem intro21_even_high_component_complement_continuation_degree_le_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (i : C.supp) (hi : 5 ≤ ((vertexDeletedGraph G v).induce C.supp).degree i)
    (j k l : {u : {w : V // w ≠ v} // u ∉ C.supp})
    (hjk : ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).Adj j k)
    (hkl : ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).Adj k l) (hlj : l ≠ j) :
    ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).degree j ≤ 3 := by
  have hp := Ngt_two_positive_of_degree_ge_five
    ((vertexDeletedGraph G v).induce C.supp) i hi
  have hbudget := deleted_component_threshold_budget G v C 2
  have htotal := intro21_even_Ngt_two_le_one G b hG hI hn hb
  have hz : Ngt ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})) 2 = 0 := by omega
  exact Ngt_two_zero_continuation_degree_le_three _ hz j k l hjk hkl hlj
#print axioms Paper7IntroHighBranch.intro21_even_high_component_complement_continuation_degree_le_three

theorem intro21_even_decorated_core_branch_Ngt_two_zero
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (S : Set {u : {w : V // w ≠ v} // u ∉ C.supp})
    (hd : ∀ i, (((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).induce S).degree i = 2)
    (z : {u : {w : V // w ≠ v} // u ∉ C.supp}) (hz : z ∉ S) (w : S)
    (hzw : ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).Adj z w.val) :
    Ngt ((vertexDeletedGraph G v).induce C.supp) 2 = 0 := by
  have hp : 0 < Ngt ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})) 2 := by
    by_contra hnp
    have hz0 : Ngt ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})) 2 = 0 := by omega
    apply Ngt_two_zero_two_regular_no_boundary
      ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})) hz0
      (((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).induce S) Subtype.val
      Subtype.val_injective (by intro a b; rfl) hd z
      (fun j h => hz (h.symm ▸ j.property)) w
    exact hzw
  have hbudget := deleted_component_threshold_budget G v C 2
  have htotal := intro21_even_Ngt_two_le_one G b hG hI hn hb
  omega
#print axioms Paper7IntroHighBranch.intro21_even_decorated_core_branch_Ngt_two_zero

theorem intro21_even_decorated_core_branch_degree_bounds
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent)
    (S : Set {u : {w : V // w ≠ v} // u ∉ C.supp})
    (hd : ∀ i, (((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).induce S).degree i = 2)
    (z : {u : {w : V // w ≠ v} // u ∉ C.supp}) (hz : z ∉ S) (w : S)
    (hzw : ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).Adj z w.val) :
    (∀ i, ((vertexDeletedGraph G v).induce C.supp).degree i ≤ 4) ∧
    (∀ i j k : C.supp,
      ((vertexDeletedGraph G v).induce C.supp).Adj i j →
      ((vertexDeletedGraph G v).induce C.supp).Adj j k → k ≠ i →
      ((vertexDeletedGraph G v).induce C.supp).degree i ≤ 3) := by
  have hzero := intro21_even_decorated_core_branch_Ngt_two_zero
    G b hG hI hn hb v C S hd z hz w hzw
  exact ⟨Ngt_two_zero_degree_le_four _ hzero,
    fun i j k hij hjk hki =>
      Ngt_two_zero_continuation_degree_le_three _ hzero i j k hij hjk hki⟩
#print axioms Paper7IntroHighBranch.intro21_even_decorated_core_branch_degree_bounds

end Paper7IntroHighBranch
