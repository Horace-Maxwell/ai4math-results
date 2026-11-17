import Research.TaskH.Seven.SevenK6CliqueData

/-!
Transport the fixed two-hook path certificates to actual graph vertices.
In any deleted-vertex coloring, an outside point with two neighbors in the
seven-point configuration is forced to have the added point's color and can
meet only the two hook vertices.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

theorem six_clique_rainbow_forbids_five_path
    (hr : RainbowSevenCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 7))
    (t : Fin 6 → V) (ht : Function.Injective t)
    (h01 : G.Adj (t 0) (t 1)) (h12 : G.Adj (t 1) (t 2))
    (h23 : G.Adj (t 2) (t 3)) (h34 : G.Adj (t 3) (t 4))
    (h45 : G.Adj (t 4) (t 5))
    (y : V) (hy : y ≠ w) (hwt : ∀ i, t i ≠ w)
    (hyout : ∀ i, y ≠ t i) (j : Fin 6)
    (hcolor : c ⟨y, hy⟩ = c ⟨t j, hwt j⟩) :
    ¬ (G.Adj y (t 0) ∧ G.Adj y (t 5)) := by
  classical
  rintro ⟨hy0, hy5⟩
  let f : Fin 7 → V := ![y, t 0, t 1, t 2, t 3, t 4, t 5]
  have hty : ∀ i, t i ≠ y := fun i he => hyout i he.symm
  have hf : IsHeptagon G f := by
    refine ⟨?_, hy0, h01, h12, h23, h34, h45, hy5.symm⟩
    intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all [f, ht.eq_iff]
  have hfw : ∀ i, f i ≠ w := by
    intro i
    fin_cases i <;> simp [f, hy, hwt]
  have hci := rainbow_heptagon_colors_injective hr w c f hf hfw
  let idx : Fin 6 → Fin 7 := ![1, 2, 3, 4, 5, 6]
  have hidx : ∀ i, f (idx i) = t i := by intro i; fin_cases i <;> rfl
  have he : (⟨f (idx j), hfw (idx j)⟩ : {x : V // x ≠ w}) = ⟨t j, hwt j⟩ :=
    Subtype.ext (hidx j)
  have hc' : c ⟨f 0, hfw 0⟩ = c ⟨f (idx j), hfw (idx j)⟩ := by
    rw [he]
    exact hcolor
  have hzero := hci hc'
  fin_cases j <;> norm_num [idx] at hzero

noncomputable def sixCliqueWithPoint (q : Fin 6 → V) (y : V) : Fin 7 → V :=
  ![q 0, q 1, q 2, q 3, q 4, q 5, y]

theorem sixCliqueWithPoint_castSucc (q : Fin 6 → V) (y : V) (i : Fin 6) :
    sixCliqueWithPoint q y i.castSucc = q i := by
  fin_cases i <;> rfl

theorem sixCliqueWithPoint_of_lt (q : Fin 6 → V) (y : V)
    (i : Fin 7) (hi : i.val < 6) :
    sixCliqueWithPoint q y i = q ⟨i.val, hi⟩ := by
  have he : (⟨i.val, hi⟩ : Fin 6).castSucc = i := Fin.ext rfl
  exact (congrArg (sixCliqueWithPoint q y) he).symm.trans
    (sixCliqueWithPoint_castSucc q y ⟨i.val, hi⟩)

theorem sixCliqueWithPoint_injective (q : Fin 6 → V) (y : V)
    (hq : Function.Injective q) (hy : ∀ i, y ≠ q i) :
    Function.Injective (sixCliqueWithPoint q y) := by
  have hy' : ∀ i, q i ≠ y := fun i hi => hy i hi.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [sixCliqueWithPoint, hq.eq_iff]

theorem sixCliqueWithPoint_adj (q : Fin 6 → V) (y : V)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (i j : Fin 7) (h : SixCliqueTwoAdj i j) :
    G.Adj (sixCliqueWithPoint q y i) (sixCliqueWithPoint q y j) := by
  rcases h with ⟨hne, hinside | hleft | hright⟩
  · rcases hinside with ⟨hi, hj⟩
    rw [sixCliqueWithPoint_of_lt q y i hi, sixCliqueWithPoint_of_lt q y j hj]
    apply hclique
    intro he
    exact hne (Fin.ext (congrArg (fun a : Fin 6 => a.val) he))
  · rcases hleft with ⟨rfl, hj | hj⟩
    · subst j
      exact hy0
    · subst j
      exact hy1
  · rcases hright with ⟨rfl, hi | hi⟩
    · subst i
      exact hy0.symm
    · subst i
      exact hy1.symm

theorem six_clique_two_colors_injective (hr : RainbowSevenCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 7))
    (e : Fin 7 → V) (he : Function.Injective e)
    (hadj : ∀ i j, SixCliqueTwoAdj i j → G.Adj (e i) (e j))
    (hew : ∀ i, e i ≠ w) : Function.Injective (fun i => c ⟨e i, hew i⟩) := by
  let k : Fin 7 → Fin 7 := ![6, 0, 2, 3, 4, 5, 1]
  have hk : Function.Injective k := by decide +kernel
  have hka : ∀ i : Fin 7, SixCliqueTwoAdj (k i) (k (i + 1)) := by decide +kernel
  let f := e ∘ k
  have hf : IsHeptagon G f := ⟨he.comp hk,
    hadj _ _ (hka 0), hadj _ _ (hka 1), hadj _ _ (hka 2),
    hadj _ _ (hka 3), hadj _ _ (hka 4), hadj _ _ (hka 5), hadj _ _ (hka 6)⟩
  have hfw : ∀ i, f i ≠ w := fun i => hew (k i)
  have hci := rainbow_heptagon_colors_injective hr w c f hf hfw
  intro i j hij
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective hk i
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective hk j
  have hab : a = b := by
    apply hci
    simpa only [f, Function.comp_apply, ha, hb] using hij
  exact ha.symm.trans ((congrArg k hab).trans hb)

theorem six_clique_two_attachment_pair (hr : RainbowSevenCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 7))
    (e : Fin 7 → V) (he : Function.Injective e)
    (hadj : ∀ i j, SixCliqueTwoAdj i j → G.Adj (e i) (e j))
    (hew : ∀ i, e i ≠ w)
    (z : V) (hzw : z ≠ w) (hzout : ∀ i, z ≠ e i)
    (r : Fin 7) (hcolor : c ⟨z, hzw⟩ = c ⟨e r, hew r⟩)
    (a b : Fin 7) (hab : a ≠ b) (hza : G.Adj z (e a)) (hzb : G.Adj z (e b)) :
    r = 6 ∧ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) := by
  classical
  have hra : r ≠ a := by
    intro hr
    have ha' : (G.induce {x | x ≠ w}).Adj ⟨z, hzw⟩ ⟨e a, hew a⟩ := hza
    exact (c.valid ha') (by simpa only [hr] using hcolor)
  have hrb : r ≠ b := by
    intro hr
    have hb' : (G.induce {x | x ≠ w}).Adj ⟨z, hzw⟩ ⟨e b, hew b⟩ := hzb
    exact (c.valid hb') (by simpa only [hr] using hcolor)
  by_contra hbad
  have hbad' : r ≠ 6 ∨ ¬ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) := by tauto
  obtain ⟨ht0, ht5, ht, ⟨j, hj⟩, htadj⟩ := sixCliqueTwoPath_spec r a b hab hra hrb hbad'
  let t := sixCliqueTwoPath r a b
  let f := e ∘ t
  have hfi : Function.Injective f := he.comp ht
  have hfw : ∀ i, f i ≠ w := fun i => hew (t i)
  have hzf : ∀ i, z ≠ f i := fun i => hzout (t i)
  have hcf : c ⟨z, hzw⟩ = c ⟨f j, hfw j⟩ := by
    have hsub : (⟨f j, hfw j⟩ : {x : V // x ≠ w}) = ⟨e r, hew r⟩ :=
      Subtype.ext (congrArg e hj)
    rw [hsub]
    exact hcolor
  have hno := six_clique_rainbow_forbids_five_path hr w c f hfi
    (hadj _ _ (htadj 0)) (hadj _ _ (htadj 1))
    (hadj _ _ (htadj 2)) (hadj _ _ (htadj 3)) (hadj _ _ (htadj 4)) z hzw hfw hzf j hcf
  apply hno
  constructor
  · simpa only [f, t, Function.comp_apply, ht0] using hza
  · simpa only [f, t, Function.comp_apply, ht5] using hzb

theorem six_two_neighbor_indices_small_or_pair (A : Finset (Fin 7)) (r : Fin 7)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      r = 6 ∧ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0))) :
    A.card ≤ 1 ∨ r = 6 ∧ A ⊆ {0, 1} := by
  classical
  by_cases hsmall : A.card ≤ 1
  · exact Or.inl hsmall
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have hp := hpair a ha b hb hab
    refine Or.inr ⟨hp.1, ?_⟩
    intro z hz
    by_cases hza : z = a
    · rw [hza]
      rcases hp.2 with ⟨h0, _h1⟩ | ⟨h1, _h0⟩
      · exact Finset.mem_insert.mpr (Or.inl h0)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h1))
    · have hzpair := hpair z hz a ha hza
      rcases hzpair.2 with ⟨h0, _h1⟩ | ⟨h1, _h0⟩
      · exact Finset.mem_insert.mpr (Or.inl h0)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h1))

noncomputable def sixCliqueTwoNeighborIndices (G : SimpleGraph V)
    (e : Fin 7 → V) (z : V) : Finset (Fin 7) := by
  classical
  exact Finset.univ.filter (fun i => G.Adj z (e i))

/-- This holds in every actual deleted-point coloring avoiding the eight
specified vertices, not just a separately chosen coloring. -/
theorem six_clique_two_attachment_coloring_constraints
    (hr : RainbowSevenCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 7))
    (e : Fin 7 → V) (he : Function.Injective e)
    (hadj : ∀ i j, SixCliqueTwoAdj i j → G.Adj (e i) (e j))
    (hew : ∀ i, e i ≠ w) (z : V) (hzw : z ≠ w) (hzout : ∀ i, z ≠ e i) :
    (sixCliqueTwoNeighborIndices G e z).card ≤ 1 ∨
      c ⟨z, hzw⟩ = c ⟨e 6, hew 6⟩ ∧ sixCliqueTwoNeighborIndices G e z ⊆ {0, 1} := by
  classical
  have hci := six_clique_two_colors_injective hr w c e he hadj hew
  obtain ⟨r, hrcolor⟩ := Finite.surjective_of_injective hci (c ⟨z, hzw⟩)
  have hcolor : c ⟨z, hzw⟩ = c ⟨e r, hew r⟩ := hrcolor.symm
  have hpair : ∀ a ∈ sixCliqueTwoNeighborIndices G e z,
      ∀ b ∈ sixCliqueTwoNeighborIndices G e z, a ≠ b →
        r = 6 ∧ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) := by
    intro a ha b hb hab
    exact six_clique_two_attachment_pair hr w c e he hadj hew z hzw hzout r hcolor
      a b hab (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  rcases six_two_neighbor_indices_small_or_pair (sixCliqueTwoNeighborIndices G e z) r hpair
      with hsmall | ⟨hr, hsub⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨by simpa only [hr] using hcolor, hsub⟩

theorem actual_six_clique_two_attachment_coloring_constraints
    (hr : RainbowSevenCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 7))
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i) (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (hqw : ∀ i, q i ≠ w) (hyw : y ≠ w)
    (z : V) (hzw : z ≠ w) (hzout : z ≠ y ∧ ∀ i, z ≠ q i) :
    (sixCliqueTwoNeighborIndices G (sixCliqueWithPoint q y) z).card ≤ 1 ∨
      c ⟨z, hzw⟩ = c ⟨y, hyw⟩ ∧
        sixCliqueTwoNeighborIndices G (sixCliqueWithPoint q y) z ⊆ {0, 1} := by
  have hew : ∀ i, sixCliqueWithPoint q y i ≠ w := by
    intro i
    fin_cases i <;> simp [sixCliqueWithPoint, hqw, hyw]
  have hzout' : ∀ i, z ≠ sixCliqueWithPoint q y i := by
    intro i
    fin_cases i <;> simp [sixCliqueWithPoint, hzout.1, hzout.2]
  exact six_clique_two_attachment_coloring_constraints hr w c _
    (sixCliqueWithPoint_injective q y hq hy) (sixCliqueWithPoint_adj q y hclique hy0 hy1)
    hew z hzw hzout'

end TaskH.Seven

#print axioms TaskH.Seven.six_clique_rainbow_forbids_five_path
#print axioms TaskH.Seven.sixCliqueWithPoint
#print axioms TaskH.Seven.sixCliqueWithPoint_castSucc
#print axioms TaskH.Seven.sixCliqueWithPoint_of_lt
#print axioms TaskH.Seven.sixCliqueWithPoint_injective
#print axioms TaskH.Seven.sixCliqueWithPoint_adj
#print axioms TaskH.Seven.six_clique_two_colors_injective
#print axioms TaskH.Seven.six_clique_two_attachment_pair
#print axioms TaskH.Seven.six_two_neighbor_indices_small_or_pair
#print axioms TaskH.Seven.sixCliqueTwoNeighborIndices
#print axioms TaskH.Seven.six_clique_two_attachment_coloring_constraints
#print axioms TaskH.Seven.actual_six_clique_two_attachment_coloring_constraints
