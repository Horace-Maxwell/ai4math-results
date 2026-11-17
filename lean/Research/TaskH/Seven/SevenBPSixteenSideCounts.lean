import Research.TaskH.Seven.SevenBPSixteenSideStructure
import Research.TaskH.Seven.SevenBPAttachmentArithmetic

/-! Exact actual C16 attachment statistics and the disjoint high-neighborhood
budget. The graph supplies every weight, neighbor relation and side set. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem bounded_four_hook_identity (S : Finset V) (w : V→ℕ)
    (hw : ∀z∈S,w z≤4) :
    (∑z∈S,w z)+(S.filter (fun z=>w z=1)).card+2*(S.filter (fun z=>w z=0)).card=
      2*S.card+(S.filter (fun z=>w z=3)).card+2*(S.filter (fun z=>w z=4)).card := by
  have hpoint : ∀z∈S,w z+(if w z=1 then 1 else 0)+2*(if w z=0 then 1 else 0)=
      2+(if w z=3 then 1 else 0)+2*(if w z=4 then 1 else 0) := by
    intro z hz
    have hn := hw z hz
    have tab : ∀n : ℕ,n≤4 → n+(if n=1 then 1 else 0)+2*(if n=0 then 1 else 0)=
        2+(if n=3 then 1 else 0)+2*(if n=4 then 1 else 0) := by
      intro n hn
      interval_cases n <;> norm_num
    exact tab (w z) hn
  simp only [Finset.card_filter]
  have hh := Finset.sum_congr rfl hpoint
  simpa only [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_const,Nat.nsmul_eq_mul,
    Nat.mul_comm] using hh

theorem bounded_four_hook_partition (S : Finset V) (w : V→ℕ)
    (hw : ∀z∈S,w z≤4) :
    (S.filter (fun z=>w z=0)).card+(S.filter (fun z=>w z=1)).card+
      (S.filter (fun z=>w z=2)).card+(S.filter (fun z=>w z=3)).card+
      (S.filter (fun z=>w z=4)).card=S.card := by
  simp only [Finset.card_filter]
  have hpoint : ∀z∈S,(if w z=0 then 1 else 0)+(if w z=1 then 1 else 0)+
      (if w z=2 then 1 else 0)+(if w z=3 then 1 else 0)+(if w z=4 then 1 else 0)=1 := by
    intro z hz
    have hn := hw z hz
    have tab : ∀n : ℕ,n≤4 → (if n=0 then 1 else 0)+(if n=1 then 1 else 0)+
        (if n=2 then 1 else 0)+(if n=3 then 1 else 0)+(if n=4 then 1 else 0)=1 := by
      intro n hn
      interval_cases n <;> norm_num
    exact tab (w z) hn
  have hh := Finset.sum_congr rfl hpoint
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_one] using hh

theorem low_hook_filter_card (S : Finset V) (w : V→ℕ) :
    (S.filter (fun z=>w z≤1)).card=
      (S.filter (fun z=>w z=0)).card+(S.filter (fun z=>w z=1)).card := by
  simp only [Finset.card_filter]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs <;> omega

theorem bounded_four_high_sum (S : Finset V) (w : V→ℕ)
    (hw : ∀z∈S,w z≤4) :
    (∑z∈S.filter (fun z=>3≤w z),(7-w z))=
      4*(S.filter (fun z=>w z=3)).card+3*(S.filter (fun z=>w z=4)).card := by
  simp only [Finset.sum_filter,Finset.card_filter,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  have hn := hw z hz
  have tab : ∀n : ℕ,n≤4 → (if 3≤n then 7-n else 0)=
      4*(if n=3 then 1 else 0)+3*(if n=4 then 1 else 0) := by
    intro n hn
    interval_cases n <;> norm_num
  exact tab (w z) hn

noncomputable def sixteenSideHookSum [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (q : Fin 2) : ℕ :=
  ∑z∈sixteenAttachmentOutsideSide c u q,(outsideHookFinset G u z).card

theorem sixteen_side_attachment_identity [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (c : G.Coloring Bool) (q : Fin 2) :
    sixteenSideHookSum c u q+(sixteenSideWeight c u q 1).card+2*(sixteenSideWeight c u q 0).card=
      2*(sixteenAttachmentOutsideSide c u q).card+(sixteenSideWeight c u q 3).card+
        2*(sixteenSideWeight c u q 4).card :=
  bounded_four_hook_identity _ _ (sixteen_side_weight_bound hb u hu h14 c q)

theorem sixteen_side_weight_partition [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (c : G.Coloring Bool) (q : Fin 2) :
    (sixteenSideWeight c u q 0).card+(sixteenSideWeight c u q 1).card+
      (sixteenSideWeight c u q 2).card+(sixteenSideWeight c u q 3).card+
      (sixteenSideWeight c u q 4).card=(sixteenAttachmentOutsideSide c u q).card :=
  bounded_four_hook_partition _ _ (sixteen_side_weight_bound hb u hu h14 c q)

theorem sixteen_side_low_card [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (q : Fin 2) :
    (sixteenSideLow c u q).card=(sixteenSideWeight c u q 0).card+(sixteenSideWeight c u q 1).card :=
  low_hook_filter_card _ _

theorem sixteen_side_high_budget [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (hd : ∀z : V,7≤G.degree z) (c : G.Coloring Bool) (q : Fin 2) :
    4*(sixteenSideWeight c u q 3).card+3*(sixteenSideWeight c u q 4).card≤
      (sixteenAttachmentOutsideSide c u (q+1)).card := by
  let A := sixteenSideHigh c u q
  let B := sixteenAttachmentOutsideSide c u (q+1)
  have hrow (z : V) (hz : z∈A) : 7-(outsideHookFinset G u z).card≤(B.filter (G.Adj z)).card := by
    have hzs := (Finset.mem_filter.mp hz).1
    rw [sixteen_side_neighbors_exact c u hu q z hzs]
    have hp := outside_degree_partition (G := G) u hu.1 z
    change (outsideHookFinset G u z).card+(actualOutsideNeighbors G u z).card=G.degree z at hp
    have hh := hd z
    omega
  have hcol (w : V) (hw : w∈B) : (A.filter (fun z=>G.Adj z w)).card≤1 := by
    have hs : A.filter (fun z=>G.Adj z w)⊆
        (actualOutsideNeighbors G u w).filter (fun z=>3≤(outsideHookFinset G u z).card) := by
      intro z hz
      obtain ⟨hzA,hzw⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzs,hz3⟩ := Finset.mem_filter.mp hzA
      refine Finset.mem_filter.mpr ⟨?_,hz3⟩
      exact (mem_actualOutsideNeighbors u w z).mpr
        ⟨hzw.symm,sixteen_side_not_range c u q z hzs⟩
    have hh := outside_neighbors_high_count_le_one hb u hu h14 w
      (sixteen_side_not_range c u (q+1) w hw)
    exact le_trans (Finset.card_le_card hs) hh
  calc
    _ = ∑z∈A,(7-(outsideHookFinset G u z).card) :=
      (bounded_four_high_sum _ _ (sixteen_side_weight_bound hb u hu h14 c q)).symm
    _ ≤ ∑z∈A,(B.filter (G.Adj z)).card := Finset.sum_le_sum hrow
    _ = ∑w∈B,(A.filter (fun z=>G.Adj z w)).card := FiniteBudget.relation_double_count A B G.Adj
    _ ≤ ∑_w∈B,(1 : ℕ) := Finset.sum_le_sum hcol
    _ = B.card := by simp

theorem sixteen_side_high_count_forces_low [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (h14 : NoFourteenCycle G)
    (hd : ∀z : V,7≤G.degree z) (c : G.Coloring Bool) (q : Fin 2)
    (hh : 0<(sixteenSideWeight c u q 3).card) :
    4≤(sixteenSideWeight c u q 1).card+2*(sixteenSideWeight c u q 0).card := by
  obtain ⟨z,hz⟩ := Finset.card_pos.mp hh
  have hzH : z∈sixteenSideHigh c u q := by
    obtain ⟨hzs,hz3⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hzs,by omega⟩
  have hl := sixteen_high_forces_four_low_on_side hb u hu h14 hd c q z hzH
  have hc := sixteen_side_low_card c u q
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.bounded_four_hook_identity
#print axioms TaskH.Seven.BP.bounded_four_hook_partition
#print axioms TaskH.Seven.BP.low_hook_filter_card
#print axioms TaskH.Seven.BP.bounded_four_high_sum
#print axioms TaskH.Seven.BP.sixteenSideHookSum
#print axioms TaskH.Seven.BP.sixteen_side_attachment_identity
#print axioms TaskH.Seven.BP.sixteen_side_weight_partition
#print axioms TaskH.Seven.BP.sixteen_side_low_card
#print axioms TaskH.Seven.BP.sixteen_side_high_budget
#print axioms TaskH.Seven.BP.sixteen_side_high_count_forces_low
