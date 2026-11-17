import Research.TaskH.Seven.SevenBPEighteenSideStructure

/-! Actual outside attachment statistics force both sides to have15 or16
vertices; each15-point side has exactly four low vertices and at most one
zero-or-two attachment vertex. The final covering contradiction is separate. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem bounded_hook_deficit_identity (S : Finset V) (w : V→ℕ)
    (hw : ∀ z∈S,w z≤3) :
    (∑z∈S,w z)+2*(S.filter (fun z=>w z≤1)).card+
      (S.filter (fun z=>w z=0)).card+(S.filter (fun z=>w z=2)).card=3*S.card := by
  have hpoint : ∀ z∈S,w z+2*(if w z≤1 then 1 else 0)+
      (if w z=0 then 1 else 0)+(if w z=2 then 1 else 0)=3 := by
    intro z hz
    have hn := hw z hz
    have tab : ∀ n : ℕ,n≤3 → n+2*(if n≤1 then 1 else 0)+
        (if n=0 then 1 else 0)+(if n=2 then 1 else 0)=3 := by
      intro n hn
      interval_cases n <;> norm_num
    exact tab (w z) hn
  simp only [Finset.card_filter]
  calc
    _ = ∑z∈S,(w z+2*(if w z≤1 then 1 else 0)+
        (if w z=0 then 1 else 0)+(if w z=2 then 1 else 0)) := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum]
    _ = ∑_z∈S,(3 : ℕ) := Finset.sum_congr rfl hpoint
    _ = 3*S.card := by simp [Nat.mul_comm]

theorem bounded_hook_no_three_budget (S : Finset V) (w : V→ℕ)
    (hw : ∀ z∈S,w z≤2) :
    (∑z∈S,w z)+(S.filter (fun z=>w z≤1)).card≤2*S.card := by
  have hpoint : ∀ z∈S,w z+(if w z≤1 then 1 else 0)≤2 := by
    intro z hz
    have hn := hw z hz
    split_ifs <;> omega
  simp only [Finset.card_filter]
  calc
    _ = ∑z∈S,(w z+(if w z≤1 then 1 else 0)) := by rw [Finset.sum_add_distrib]
    _ ≤ ∑_z∈S,(2 : ℕ) := Finset.sum_le_sum hpoint
    _ = 2*S.card := by simp [Nat.mul_comm]

noncomputable def eighteenSideZero [Fintype V] (c : G.Coloring Bool) (u : Fin 18 → V) (q : Fin 2) : Finset V :=
  (eighteenOutsideSide c u q).filter (fun z=>(eighteenOutsideHooks G u z).card=0)
noncomputable def eighteenSideTwo [Fintype V] (c : G.Coloring Bool) (u : Fin 18 → V) (q : Fin 2) : Finset V :=
  (eighteenOutsideSide c u q).filter (fun z=>(eighteenOutsideHooks G u z).card=2)

theorem eighteen_side_hook_bound [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G) (u : Fin 18 → V)
    (hu : IsCycleEighteen G u) (c : G.Coloring Bool) (q : Fin 2) :
    ∀z∈eighteenOutsideSide c u q,(eighteenOutsideHooks G u z).card≤3 := by
  intro z hz
  exact eighteen_outside_hook_card_le_three hb h14 h16 u hu z (eighteen_side_not_range c u q z hz)

theorem eighteen_side_deficit_identity [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G) (u : Fin 18 → V)
    (hu : IsCycleEighteen G u) (c : G.Coloring Bool) (q : Fin 2) :
    (∑z∈eighteenOutsideSide c u q,(eighteenOutsideHooks G u z).card)+
      2*(eighteenSideLow c u q).card+(eighteenSideZero c u q).card+
      (eighteenSideTwo c u q).card=3*(eighteenOutsideSide c u q).card :=
  bounded_hook_deficit_identity _ _ (eighteen_side_hook_bound hb h14 h16 u hu c q)

theorem eighteen_side_no_triple_budget [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G) (u : Fin 18 → V)
    (hu : IsCycleEighteen G u) (c : G.Coloring Bool) (q : Fin 2)
    (he : eighteenSideTriple c u q=∅) :
    (∑z∈eighteenOutsideSide c u q,(eighteenOutsideHooks G u z).card)+
      (eighteenSideLow c u q).card≤2*(eighteenOutsideSide c u q).card := by
  apply bounded_hook_no_three_budget
  intro z hz
  have h3 := eighteen_side_hook_bound hb h14 h16 u hu c q z hz
  have hn3 : (eighteenOutsideHooks G u z).card≠3 := by
    intro h
    have hm : z∈eighteenSideTriple c u q := Finset.mem_filter.mpr ⟨hz,h⟩
    rw [he] at hm
    exact Finset.notMem_empty z hm
  omega

theorem eighteen_both_sides_have_triple [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G) (u : Fin 18 → V)
    (hu : IsCycleEighteen G u) (hn : Fintype.card V≤49) (hd : ∀x : V,7≤G.degree x)
    (c : G.Coloring Bool) (q : Fin 2) : (eighteenSideTriple c u q).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hnone
  have hsize : (eighteenOutsideSide c u q).card+(eighteenOutsideSide c u (q+1)).card≤31 := by
    have hh := eighteen_outside_sides_card_le_thirty_one c u hu hn
    have hcases : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide +kernel
    rcases hcases q with hq | hq
    · subst q
      simpa only [show (0 : Fin 2)+1=1 by decide] using hh
    · subst q
      simpa only [show (1 : Fin 2)+1=0 by decide,Nat.add_comm] using hh
  have hEa := eighteen_each_side_attachments_ge_thirty_six hb h14 h16 u hu hd c q
  have hEb := eighteen_each_side_attachments_ge_thirty_six hb h14 h16 u hu hd c (q+1)
  have haBudget := eighteen_side_no_triple_budget hb h14 h16 u hu c q hnone
  have hbUpper : (∑z∈eighteenOutsideSide c u (q+1),(eighteenOutsideHooks G u z).card)≤
      3*(eighteenOutsideSide c u (q+1)).card := by
    have hh := eighteen_side_deficit_identity hb h14 h16 u hu c (q+1)
    omega
  have hnb : (eighteenSideTriple c u (q+1)).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hbBudget := eighteen_side_no_triple_budget hb h14 h16 u hu c (q+1) he
    omega
  obtain ⟨b,hbq⟩ := hnb
  have hlow := eighteen_triple_forces_four_opposite_low hb h14 h16 u hu hd c (q+1) b hbq
  have hqq : (q+1)+1=q := by
    have tab : ∀ q : Fin 2,(q+1)+1=q := by decide +kernel
    exact tab q
  rw [hqq] at hlow
  omega

theorem eighteen_each_side_four_low [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G) (u : Fin 18 → V)
    (hu : IsCycleEighteen G u) (hn : Fintype.card V≤49) (hd : ∀x : V,7≤G.degree x)
    (c : G.Coloring Bool) (q : Fin 2) : 4≤(eighteenSideLow c u q).card := by
  obtain ⟨b,hbq⟩ := eighteen_both_sides_have_triple hb h14 h16 u hu hn hd c (q+1)
  have hh := eighteen_triple_forces_four_opposite_low hb h14 h16 u hu hd c (q+1) b hbq
  have hqq : (q+1)+1=q := by
    have tab : ∀ q : Fin 2,(q+1)+1=q := by decide +kernel
    exact tab q
  simpa only [hqq] using hh

theorem eighteen_each_side_at_least_fifteen [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G) (u : Fin 18 → V)
    (hu : IsCycleEighteen G u) (hn : Fintype.card V≤49) (hd : ∀x : V,7≤G.degree x)
    (c : G.Coloring Bool) (q : Fin 2) : 15≤(eighteenOutsideSide c u q).card := by
  have hE := eighteen_each_side_attachments_ge_thirty_six hb h14 h16 u hu hd c q
  have hL := eighteen_each_side_four_low hb h14 h16 u hu hn hd c q
  have hD := eighteen_side_deficit_identity hb h14 h16 u hu c q
  omega

theorem eighteen_fifteen_side_counts [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G) (u : Fin 18 → V)
    (hu : IsCycleEighteen G u) (hn : Fintype.card V≤49) (hd : ∀x : V,7≤G.degree x)
    (c : G.Coloring Bool) (q : Fin 2) (h15 : (eighteenOutsideSide c u q).card=15) :
    (eighteenSideLow c u q).card=4 ∧ (eighteenSideZero c u q).card+(eighteenSideTwo c u q).card≤1 := by
  have hE := eighteen_each_side_attachments_ge_thirty_six hb h14 h16 u hu hd c q
  have hL := eighteen_each_side_four_low hb h14 h16 u hu hn hd c q
  have hD := eighteen_side_deficit_identity hb h14 h16 u hu c q
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.bounded_hook_deficit_identity
#print axioms TaskH.Seven.BP.bounded_hook_no_three_budget
#print axioms TaskH.Seven.BP.eighteenSideZero
#print axioms TaskH.Seven.BP.eighteenSideTwo
#print axioms TaskH.Seven.BP.eighteen_side_hook_bound
#print axioms TaskH.Seven.BP.eighteen_side_deficit_identity
#print axioms TaskH.Seven.BP.eighteen_side_no_triple_budget
#print axioms TaskH.Seven.BP.eighteen_both_sides_have_triple
#print axioms TaskH.Seven.BP.eighteen_each_side_four_low
#print axioms TaskH.Seven.BP.eighteen_each_side_at_least_fifteen
#print axioms TaskH.Seven.BP.eighteen_fifteen_side_counts
