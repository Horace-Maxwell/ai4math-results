import Research.Backfill.Paper7.IntroUnicyclicContinuation
import Research.Backfill.Paper7.IntroBranchSquareBounds
import Research.Backfill.Paper7.IntroEvenDegreeMoments

/-! Exact leaf/excess conservation and uniform branching-square bounds. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroFour
open SimpleGraph BackfillPaper7.Challenge Paper7Unicyclic Paper7IntroEven

def leafVerts {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 1)
#print axioms Paper7IntroFour.leafVerts

def nonleafVerts {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => 2 ≤ G.degree v)
#print axioms Paper7IntroFour.nonleafVerts

theorem unicyclic_leaf_partition
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) :
    Disjoint (leafVerts G) (nonleafVerts G) ∧
      leafVerts G ∪ nonleafVerts G = Finset.univ ∧
      (leafVerts G).card + (nonleafVerts G).card = Fintype.card V := by
  have hd : Disjoint (leafVerts G) (nonleafVerts G) := by
    apply Finset.disjoint_left.mpr
    intro v hl hn
    have hl' : G.degree v = 1 := (Finset.mem_filter.mp hl).2
    have hn' : 2 ≤ G.degree v := (Finset.mem_filter.mp hn).2
    omega
  have hu : leafVerts G ∪ nonleafVerts G = Finset.univ := by
    ext v
    have hpos := unicyclic_positive_degree G b hG v
    simp only [Finset.mem_union, leafVerts, nonleafVerts, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    omega
  have hc := Finset.card_union_of_disjoint hd
  rw [hu, Finset.card_univ] at hc
  exact ⟨hd, hu, hc.symm⟩
#print axioms Paper7IntroFour.unicyclic_leaf_partition

theorem unicyclic_leaf_card_add_cycle_le
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) : (leafVerts G).card + b ≤ Fintype.card V := by
  obtain ⟨s, ⟨r, w, hw, hlen, _hs⟩, _hu⟩ := hG.2
  have hd : Disjoint (leafVerts G) w.support.toFinset := by
    apply Finset.disjoint_left.mpr
    intro v hl hv
    have hleaf : G.degree v = 1 := (Finset.mem_filter.mp hl).2
    have hcycle := cycle_vertex_degree_ge_two G w hw v (List.mem_toFinset.mp hv)
    omega
  have hc : (leafVerts G).card + w.support.toFinset.card ≤ Fintype.card V := by
    calc
      _ = (leafVerts G ∪ w.support.toFinset).card := (Finset.card_union_of_disjoint hd).symm
      _ ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.subset_univ _)
      _ = _ := Finset.card_univ
  rwa [Paper7Cycles.cycle_support_card w hw, hlen] at hc
#print axioms Paper7IntroFour.unicyclic_leaf_card_add_cycle_le

theorem unicyclic_leaf_excess_identities
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) :
    (∑ v ∈ nonleafVerts G, ((G.degree v : ℤ) - 2)) = ((leafVerts G).card : ℤ) ∧
      degreeDeviation G = ((leafVerts G).card : ℤ) +
        ∑ v ∈ nonleafVerts G, ((G.degree v : ℤ) - 2) ^ 2 := by
  obtain ⟨hdisj, hunion, hcard⟩ := unicyclic_leaf_partition G b hG
  have hcardZ : ((leafVerts G).card : ℤ) + ((nonleafVerts G).card : ℤ) =
      (Fintype.card V : ℤ) := by exact_mod_cast hcard
  have hdegree : (∑ v : V, (G.degree v : ℤ)) = 2 * (Fintype.card V : ℤ) := by
    have h := G.sum_degrees_eq_twice_card_edges
    rw [unicyclic_card_edges G hG] at h
    exact_mod_cast h
  have hsum : (∑ v ∈ leafVerts G, (G.degree v : ℤ)) +
      (∑ v ∈ nonleafVerts G, (G.degree v : ℤ)) = ∑ v : V, (G.degree v : ℤ) := by
    rw [← Finset.sum_union hdisj, hunion]
  have hleaf : (∑ v ∈ leafVerts G, (G.degree v : ℤ)) = ((leafVerts G).card : ℤ) := by
    calc
      _ = ∑ _v ∈ leafVerts G, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro v hv
        have hd : G.degree v = 1 := (Finset.mem_filter.mp hv).2
        simp only [hd, Nat.cast_one]
      _ = _ := by simp
  have hexcess : (∑ v ∈ nonleafVerts G, ((G.degree v : ℤ) - 2)) =
      (∑ v ∈ nonleafVerts G, (G.degree v : ℤ)) - ((nonleafVerts G).card : ℤ) * 2 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  constructor
  · linarith
  · have hsumSq : (∑ v ∈ leafVerts G, ((G.degree v : ℤ) - 2) ^ 2) +
        (∑ v ∈ nonleafVerts G, ((G.degree v : ℤ) - 2) ^ 2) = degreeDeviation G := by
      rw [← Finset.sum_union hdisj, hunion]
      rfl
    have hleafSq : (∑ v ∈ leafVerts G, ((G.degree v : ℤ) - 2) ^ 2) =
        ((leafVerts G).card : ℤ) := by
      calc
        _ = ∑ _v ∈ leafVerts G, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro v hv
          have hd : G.degree v = 1 := (Finset.mem_filter.mp hv).2
          norm_num [hd]
        _ = _ := by simp
    rw [hleafSq] at hsumSq
    exact hsumSq.symm
#print axioms Paper7IntroFour.unicyclic_leaf_excess_identities

theorem intro21_branch_mass_le_188_of_leaves_le_fifteen
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hL : (leafVerts G).card ≤ 15) : degreeDeviation G ≤ 188 := by
  obtain ⟨hsum, hD⟩ := unicyclic_leaf_excess_identities G b hG
  have hs := sum_sq_cap_thirteen_budget_fifteen (nonleafVerts G)
    (fun v => (G.degree v : ℤ) - 2) (by
      intro v hv
      have hd : 2 ≤ G.degree v := (Finset.mem_filter.mp hv).2
      omega) (by
      intro v _hv
      have hd := intro21_degree_le_fifteen G b hG hI hn v
      omega) (by rw [hsum]; exact_mod_cast hL)
  have hLZ : ((leafVerts G).card : ℤ) ≤ 15 := by exact_mod_cast hL
  linarith
#print axioms Paper7IntroFour.intro21_branch_mass_le_188_of_leaves_le_fifteen

theorem intro21_branch_mass_le_202_of_leaves_le_seventeen
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hL : (leafVerts G).card ≤ 17) : degreeDeviation G ≤ 202 := by
  obtain ⟨hsum, hD⟩ := unicyclic_leaf_excess_identities G b hG
  have hs := sum_sq_cap_thirteen_budget_seventeen (nonleafVerts G)
    (fun v => (G.degree v : ℤ) - 2) (by
      intro v hv
      have hd : 2 ≤ G.degree v := (Finset.mem_filter.mp hv).2
      omega) (by
      intro v _hv
      have hd := intro21_degree_le_fifteen G b hG hI hn v
      omega) (by rw [hsum]; exact_mod_cast hL)
  have hLZ : ((leafVerts G).card : ℤ) ≤ 17 := by exact_mod_cast hL
  linarith
#print axioms Paper7IntroFour.intro21_branch_mass_le_202_of_leaves_le_seventeen

end Paper7IntroFour
