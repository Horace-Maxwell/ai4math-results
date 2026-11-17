import Research.TaskH.Seven.SevenK5LastStructure

/-! Six actual vertices per singleton group and five actual disjoint closed
outside neighborhoods. The groups are derived from degree ten and r=0. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem five_single_group_card_ge_six
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hdegree : ∀ x : V, 10 ≤ G.degree x)
    (hM : (fiveCliqueMulti G q).card = 0) (i : Fin 5) :
    6 ≤ (fiveCliqueSingleGroup G q i).card := by
  classical
  have hsub : packingNeighborsIn G (fiveCliqueSet q)ᶜ (q i) ⊆
      fiveCliqueSingleGroup G q i := by
    intro x hx
    have hh := Finset.mem_filter.mp hx
    have hiL : i ∈ fiveCliqueLabels G q x := by
      simpa only [fiveCliqueLabels, Finset.mem_filter, Finset.mem_univ, true_and]
        using hh.2.symm
    have hle : (fiveCliqueLabels G q x).card ≤ 1 := by
      by_contra hlarge
      have hxM : x ∈ fiveCliqueMulti G q :=
        Finset.mem_filter.mpr ⟨hh.1, by omega⟩
      have hpos := Finset.card_pos.mpr ⟨x, hxM⟩
      omega
    have he : fiveCliqueLabels G q x = {i} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hiL, fun j hj => Finset.card_le_one.mp hle j hj i hiL⟩
    exact Finset.mem_filter.mpr ⟨hh.1, he⟩
  have hout := packingNeighborsIn_compl_lower (fiveCliqueSet q) (q i) 10 4
    (hdegree _) (fiveClique_root_internal_neighbors_card q hq hclique i).le
  have hout' : 6 ≤ (packingNeighborsIn G (fiveCliqueSet q)ᶜ (q i)).card := by
    simpa using hout
  exact hout'.trans (Finset.card_le_card hsub)

omit [DecidableRel G.Adj] in
noncomputable def fiveSixGroupEmbedding (q : Fin 5 → V)
    (hgroup : ∀ i, 6 ≤ (fiveCliqueSingleGroup G q i).card) (i : Fin 5) :
    Fin 6 ↪ ↥(fiveCliqueSingleGroup G q i) := by
  have hc : Fintype.card (Fin 6) ≤ Fintype.card ↥(fiveCliqueSingleGroup G q i) := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hgroup i
  exact Classical.choice (Function.Embedding.nonempty_of_card_le hc)

omit [DecidableRel G.Adj] in
noncomputable def fiveSixGroupVertices (q : Fin 5 → V)
    (hgroup : ∀ i, 6 ≤ (fiveCliqueSingleGroup G q i).card) (a : Fin 5 × Fin 6) : V :=
  (fiveSixGroupEmbedding q hgroup a.1 a.2).val

omit [DecidableRel G.Adj] in
theorem fiveSixGroupVertices_mem (q : Fin 5 → V)
    (hgroup : ∀ i, 6 ≤ (fiveCliqueSingleGroup G q i).card) (a : Fin 5 × Fin 6) :
    fiveSixGroupVertices q hgroup a ∈ fiveCliqueSingleGroup G q a.1 :=
  (fiveSixGroupEmbedding q hgroup a.1 a.2).property

omit [DecidableRel G.Adj] in
theorem fiveSixGroupVertices_injective (q : Fin 5 → V)
    (hgroup : ∀ i, 6 ≤ (fiveCliqueSingleGroup G q i).card) :
    Function.Injective (fiveSixGroupVertices (G := G) q hgroup) := by
  intro a b he
  have ha := (Finset.mem_filter.mp (fiveSixGroupVertices_mem q hgroup a)).2
  have hb := (Finset.mem_filter.mp (fiveSixGroupVertices_mem q hgroup b)).2
  have hab : a.1 = b.1 := by
    rw [he, hb] at ha
    exact Finset.singleton_inj.mp ha.symm
  rcases a with ⟨i, s⟩
  rcases b with ⟨j, t⟩
  change i = j at hab
  subst j
  have hsub : fiveSixGroupEmbedding q hgroup i s = fiveSixGroupEmbedding q hgroup i t :=
    Subtype.ext he
  exact Prod.ext rfl ((fiveSixGroupEmbedding q hgroup i).injective hsub)

theorem five_independent_groups_closed_packing
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn9 : 9 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hdegree : ∀ x : V, 10 ≤ G.degree x)
    (y : Fin 5 → V) (hyinj : Function.Injective y)
    (hymem : ∀ i, y i ∈ fiveCliqueSingleGroup G q i)
    (hyind : ∀ i j, i ≠ j → ¬ G.Adj (y i) (y j)) :
    55 ≤ Fintype.card V := by
  classical
  let H := (fiveCliqueSet q)ᶜ
  let N : Fin 5 → Finset V := fun i => insert (y i) (packingNeighborsIn G H (y i))
  have hyout : ∀ i, y i ∉ fiveCliqueSet q := fun i =>
    Finset.mem_compl.mp (Finset.mem_filter.mp (hymem i)).1
  have hyq : ∀ i j, q j ≠ y i := by
    intro i j he
    apply hyout i
    rw [← he]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hylabel : ∀ i, fiveCliqueLabels G q (y i) = {i} := fun i =>
    (Finset.mem_filter.mp (hymem i)).2
  have hyroot : ∀ i, G.Adj (q i) (y i) := by
    intro i
    have hm : i ∈ fiveCliqueLabels G q (y i) := by rw [hylabel]; simp
    have hlabels : fiveCliqueLabels G q (y i) =
        (Finset.univ : Finset (Fin 5)).filter (fun a => G.Adj (y i) (q a)) :=
      Finset.filter_congr_decidable _ _ _
    rw [hlabels] at hm
    exact (Finset.mem_filter.mp hm).2.symm
  have hsub : ∀ i, N i ⊆ H := by
    intro i z hz
    rcases Finset.mem_insert.mp hz with hzy | hz
    · rw [hzy]
      exact Finset.mem_compl.mpr (hyout i)
    · exact (Finset.mem_filter.mp hz).1
  have hN : ∀ i, 10 ≤ (N i).card := by
    intro i
    have hin : (packingNeighborsIn G (fiveCliqueSet q) (y i)).card ≤ 1 := by
      rw [fiveClique_internal_neighbors_card q hq, hylabel]
      exact (Finset.card_singleton i).le
    have hout : 9 ≤ (packingNeighborsIn G H (y i)).card :=
      packingNeighborsIn_compl_lower (G := G) (fiveCliqueSet q) (y i) 10 1 (hdegree _) hin
    have hself : y i ∉ packingNeighborsIn G H (y i) := by
      intro hm
      exact (Finset.mem_filter.mp hm).2.ne rfl
    change 10 ≤ (insert (y i) (packingNeighborsIn G H (y i))).card
    rw [Finset.card_insert_of_notMem hself]
    omega
  have hdis : ∀ i j, i ≠ j → Disjoint (N i) (N j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    rcases Finset.mem_insert.mp hzi with hzi | hzi
    · rcases Finset.mem_insert.mp hzj with hzj | hzj
      · exact (hyinj.ne hij) (hzi.symm.trans hzj)
      · have hadj := (Finset.mem_filter.mp hzj).2
        rw [hzi] at hadj
        exact hyind i j hij hadj.symm
    · rcases Finset.mem_insert.mp hzj with hzj | hzj
      · have hadj := (Finset.mem_filter.mp hzi).2
        rw [hzj] at hadj
        exact hyind i j hij hadj
      · have hzout : z ∉ fiveCliqueSet q :=
          Finset.mem_compl.mp (Finset.mem_filter.mp hzi).1
        have hzq : ∀ a, q a ≠ z := by
          intro a he
          apply hzout
          rw [← he]
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
        have he := five_clique_distinct_roots_common_neighbor_unique hcrit hr hn9 q hq hclique
          (y i) (y j) z (hyq i) (hyq j) hzq i j hij (hyroot i) (hyroot j)
          (Finset.mem_filter.mp hzi).2 (Finset.mem_filter.mp hzj).2
        exact (hyinj.ne hij) he
  have hrow : ∀ i ∈ (Finset.univ : Finset (Fin 5)), 10 ≤
      (H.filter (fun z => z ∈ N i)).card := by
    intro i _hi
    have he : H.filter (fun z => z ∈ N i) = N i := by
      ext z
      simp only [Finset.mem_filter]
      exact ⟨fun hz => hz.2, fun hz => ⟨hsub i hz, hz⟩⟩
    rw [he]
    exact hN i
  have hcol : ∀ z ∈ H,
      ((Finset.univ : Finset (Fin 5)).filter (fun i => z ∈ N i)).card ≤ 1 := by
    intro z _hz
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact Finset.disjoint_left.mp (hdis i j hij)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hd : (∑ i : Fin 5, (H.filter (fun z => z ∈ N i)).card) =
      ∑ z ∈ H, ((Finset.univ : Finset (Fin 5)).filter (fun i => z ∈ N i)).card := by
    convert FiniteBudget.relation_double_count (Finset.univ : Finset (Fin 5)) H
      (fun i z => z ∈ N i) using 1 <;> apply Finset.sum_congr rfl
    all_goals
      intro x _
      apply congrArg Finset.card
      ext z
      simp only [Finset.mem_filter]
  have hlo : 50 ≤ ∑ i : Fin 5, (H.filter (fun z => z ∈ N i)).card := by
    calc
      50 = ∑ _i : Fin 5, 10 := by norm_num
      _ ≤ _ := Finset.sum_le_sum hrow
  have hhi : (∑ z ∈ H, ((Finset.univ : Finset (Fin 5)).filter
      (fun i => z ∈ N i)).card) ≤ H.card := by
    calc
      _ ≤ ∑ _z ∈ H, 1 := Finset.sum_le_sum hcol
      _ = H.card := by simp
  have hcard := Finset.card_add_card_compl (fiveCliqueSet q)
  rw [fiveCliqueSet_card q hq] at hcard
  change 5 + H.card = Fintype.card V at hcard
  have hpack := hlo.trans (hd.le.trans hhi)
  omega

theorem critical_five_clique_no_multi_packing
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn9 : 9 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hdegree : ∀ x : V, 10 ≤ G.degree x)
    (hM : (fiveCliqueMulti G q).card = 0) : 55 ≤ Fintype.card V := by
  classical
  have hgroup := five_single_group_card_ge_six q hq hclique hdegree hM
  let r := fiveSixGroupVertices (G := G) q hgroup
  have hrinj : Function.Injective r := fiveSixGroupVertices_injective q hgroup
  obtain ⟨f, hf⟩ := actual_five_group_independent_transversal hcrit hr hn9 q hq hclique r
    hrinj (fiveSixGroupVertices_mem q hgroup)
  let y : Fin 5 → V := fun i => r (i, f i)
  have hy : Function.Injective y := by
    intro i j he
    exact congrArg Prod.fst (hrinj he)
  exact five_independent_groups_closed_packing hcrit hr hn9 q hq hclique hdegree y hy
    (fun i => fiveSixGroupVertices_mem q hgroup (i, f i)) hf

end TaskH.Seven
#print axioms TaskH.Seven.five_single_group_card_ge_six
#print axioms TaskH.Seven.fiveSixGroupEmbedding
#print axioms TaskH.Seven.fiveSixGroupVertices
#print axioms TaskH.Seven.fiveSixGroupVertices_mem
#print axioms TaskH.Seven.fiveSixGroupVertices_injective
#print axioms TaskH.Seven.five_independent_groups_closed_packing
#print axioms TaskH.Seven.critical_five_clique_no_multi_packing
