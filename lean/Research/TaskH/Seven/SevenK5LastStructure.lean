import Research.TaskH.Seven.SevenK5LastFinite

/-! The selected thirty actual vertices form a cross-label star forest.
The generic finite count is applied to its actual edges, never postulated. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

noncomputable def fiveGroupCrossGraph {V : Type u} (G : SimpleGraph V)
    (r : Fin 5 × Fin 6 → V) : SimpleGraph (Fin 5 × Fin 6) where
  Adj a b := G.Adj (r a) (r b) ∧ a.1 ≠ b.1
  symm := ⟨by intro a b h; exact ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨by intro a h; exact h.2 rfl⟩

theorem no_four_path_edge_has_leaf {A : Type u} [Fintype A]
    (F : SimpleGraph A) [DecidableRel F.Adj] (label : A → Fin 5)
    (hedge : ∀ a b, F.Adj a b → label a ≠ label b)
    (hneighbors : ∀ a b c, F.Adj a b → F.Adj a c → label b = label c)
    (hnopath : ∀ t : Fin 4 → A, Function.Injective t →
      F.Adj (t 0) (t 1) → F.Adj (t 1) (t 2) → F.Adj (t 2) (t 3) → False) :
    ∀ a b, F.Adj a b → F.degree a ≤ 1 ∨ F.degree b ≤ 1 := by
  classical
  intro a b hab
  by_contra hno
  have ha : 1 < (F.neighborFinset a).card := by
    rw [F.card_neighborFinset_eq_degree]
    omega
  have hb : 1 < (F.neighborFinset b).card := by
    rw [F.card_neighborFinset_eq_degree]
    omega
  obtain ⟨x, hx, hxb⟩ := Finset.exists_mem_ne ha b
  obtain ⟨y, hy, hya⟩ := Finset.exists_mem_ne hb a
  have hax := (F.mem_neighborFinset a x).mp hx
  have hby := (F.mem_neighborFinset b y).mp hy
  have hxy : x ≠ y := by
    intro he
    have hl := hneighbors a x b hax hab
    exact (hedge b y hby) (hl.symm.trans (congrArg label he))
  let t : Fin 4 → A := ![x, a, b, y]
  have hxa : x ≠ a := hax.ne.symm
  have hyb : y ≠ b := hby.ne.symm
  have hba : b ≠ a := hab.ne.symm
  have hay : a ≠ y := Ne.symm hya
  have hbx : b ≠ x := Ne.symm hxb
  have hti : Function.Injective t := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [t]
  exact hnopath t hti hax.symm hab hby

theorem actual_five_group_independent_transversal
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn9 : 9 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (r : Fin 5 × Fin 6 → V) (hrinj : Function.Injective r)
    (hrmem : ∀ a, r a ∈ fiveCliqueSingleGroup G q a.1) :
    ∃ f : Fin 5 → Fin 6, ∀ i j : Fin 5, i ≠ j →
      ¬ G.Adj (r (i, f i)) (r (j, f j)) := by
  classical
  let F := fiveGroupCrossGraph G r
  have hlabel : ∀ a, fiveCliqueLabels G q (r a) = {a.1} :=
    fun a => (Finset.mem_filter.mp (hrmem a)).2
  have hout : ∀ a i, q i ≠ r a := by
    intro a i he
    have hh := Finset.mem_compl.mp (Finset.mem_filter.mp (hrmem a)).1
    apply hh
    rw [← he]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hroot : ∀ a, G.Adj (q a.1) (r a) := by
    intro a
    have hm : a.1 ∈ fiveCliqueLabels G q (r a) := by rw [hlabel]; simp
    exact (Finset.mem_filter.mp hm).2.symm
  have hneighbors : ∀ a b c, F.Adj a b → F.Adj a c → b.1 = c.1 := by
    intro a b c hab hac
    by_contra hbc
    have he := five_clique_distinct_roots_common_neighbor_unique hcrit hr hn9 q hq hclique
      (r b) (r c) (r a) (hout b) (hout c) (hout a) b.1 c.1 hbc
      (hroot b) (hroot c) hab.1.symm hac.1.symm
    exact hbc (congrArg Prod.fst (hrinj he))
  have hnopath : ∀ t : Fin 4 → (Fin 5 × Fin 6), Function.Injective t →
      F.Adj (t 0) (t 1) → F.Adj (t 1) (t 2) → F.Adj (t 2) (t 3) → False := by
    intro t ht h01 h12 h23
    have h02 := hneighbors (t 1) (t 0) (t 2) h01.symm h12
    have h13 := hneighbors (t 2) (t 1) (t 3) h12.symm h23
    have h03 : (t 0).1 ≠ (t 3).1 := by
      intro he
      exact h01.2 (he.trans h13.symm)
    exact critical_no_five_clique_external_four_path_at hcrit hr hn9 q (r ∘ t)
      hq (hrinj.comp ht) (fun i j => hout (t j) i) hclique
      (t 0).1 (t 3).1 h03 (hroot (t 0)) h01.1 h12.1 h23.1 (hroot (t 3)).symm
  have hleaf := no_four_path_edge_has_leaf F Prod.fst
    (fun a b h => h.2) hneighbors hnopath
  let E := orderedStarEdges F (fun a => a.1.val)
  have hE : E.card ≤ 30 := by
    have hh := ordered_star_edges_card_le F (fun a => a.1.val) hleaf
    simpa only [Fintype.card_prod, Fintype.card_fin] using hh
  have hsep : ∀ e ∈ E, e.1.1 ≠ e.2.1 := by
    intro e he
    exact (Finset.mem_filter.mp he).2.1.2
  obtain ⟨f, hf⟩ := thirty_point_independent_transversal E hE hsep
  refine ⟨f, ?_⟩
  intro i j hij hadj
  by_cases hlt : i.val < j.val
  · have he : ((i, f i), (j, f j)) ∈ E :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hadj, hij⟩, hlt⟩
    exact hf _ he ⟨rfl, rfl⟩
  · have hgt : j.val < i.val := by
      have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
      omega
    have he : ((j, f j), (i, f i)) ∈ E :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hadj.symm, Ne.symm hij⟩, hgt⟩
    exact hf _ he ⟨rfl, rfl⟩

end TaskH.Seven
#print axioms TaskH.Seven.fiveGroupCrossGraph
#print axioms TaskH.Seven.no_four_path_edge_has_leaf
#print axioms TaskH.Seven.actual_five_group_independent_transversal
