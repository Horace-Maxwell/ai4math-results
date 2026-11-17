import Research.TaskH.Six.SixFiveCliqueData
import Research.TaskH.Six.SixCliquePathPacking

/-!
Transport the fixed two-hook path certificates to actual graph vertices.
In any deleted-vertex coloring, an outside point with two neighbors in the
six-point configuration is forced to have the added point's color and can
meet only the two hook vertices.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

noncomputable def fiveCliqueWithPoint (q : Fin 5 → V) (y : V) : Fin 6 → V :=
  ![q 0, q 1, q 2, q 3, q 4, y]

theorem fiveCliqueWithPoint_castSucc (q : Fin 5 → V) (y : V) (i : Fin 5) :
    fiveCliqueWithPoint q y i.castSucc = q i := by
  fin_cases i <;> rfl

theorem fiveCliqueWithPoint_of_lt (q : Fin 5 → V) (y : V)
    (i : Fin 6) (hi : i.val < 5) :
    fiveCliqueWithPoint q y i = q ⟨i.val, hi⟩ := by
  have he : (⟨i.val, hi⟩ : Fin 5).castSucc = i := Fin.ext rfl
  exact (congrArg (fiveCliqueWithPoint q y) he).symm.trans
    (fiveCliqueWithPoint_castSucc q y ⟨i.val, hi⟩)

theorem fiveCliqueWithPoint_injective (q : Fin 5 → V) (y : V)
    (hq : Function.Injective q) (hy : ∀ i, y ≠ q i) :
    Function.Injective (fiveCliqueWithPoint q y) := by
  have hy' : ∀ i, q i ≠ y := fun i hi => hy i hi.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [fiveCliqueWithPoint, hq.eq_iff]

theorem fiveCliqueWithPoint_adj (q : Fin 5 → V) (y : V)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (i j : Fin 6) (h : FiveCliqueTwoAdj i j) :
    G.Adj (fiveCliqueWithPoint q y i) (fiveCliqueWithPoint q y j) := by
  rcases h with ⟨hne, hinside | hleft | hright⟩
  · rcases hinside with ⟨hi, hj⟩
    rw [fiveCliqueWithPoint_of_lt q y i hi, fiveCliqueWithPoint_of_lt q y j hj]
    apply hclique
    intro he
    exact hne (Fin.ext (congrArg (fun a : Fin 5 => a.val) he))
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

theorem five_clique_two_colors_injective (hr : RainbowSixCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 6))
    (e : Fin 6 → V) (he : Function.Injective e)
    (hadj : ∀ i j, FiveCliqueTwoAdj i j → G.Adj (e i) (e j))
    (hew : ∀ i, e i ≠ w) : Function.Injective (fun i => c ⟨e i, hew i⟩) := by
  let k : Fin 6 → Fin 6 := ![5, 0, 2, 3, 4, 1]
  have hk : Function.Injective k := by decide +kernel
  have hka : ∀ i : Fin 6, FiveCliqueTwoAdj (k i) (k (i + 1)) := by decide +kernel
  let f := e ∘ k
  have hf : IsHexagon G f := ⟨he.comp hk,
    hadj _ _ (hka 0), hadj _ _ (hka 1), hadj _ _ (hka 2),
    hadj _ _ (hka 3), hadj _ _ (hka 4), hadj _ _ (hka 5)⟩
  have hfw : ∀ i, f i ≠ w := fun i => hew (k i)
  have hci := rainbow_hexagon_colors_injective hr w c f hf hfw
  intro i j hij
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective hk i
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective hk j
  have hab : a = b := by
    apply hci
    simpa only [f, Function.comp_apply, ha, hb] using hij
  exact ha.symm.trans ((congrArg k hab).trans hb)

theorem five_clique_two_attachment_pair (hr : RainbowSixCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 6))
    (e : Fin 6 → V) (he : Function.Injective e)
    (hadj : ∀ i j, FiveCliqueTwoAdj i j → G.Adj (e i) (e j))
    (hew : ∀ i, e i ≠ w)
    (z : V) (hzw : z ≠ w) (hzout : ∀ i, z ≠ e i)
    (r : Fin 6) (hcolor : c ⟨z, hzw⟩ = c ⟨e r, hew r⟩)
    (a b : Fin 6) (hab : a ≠ b) (hza : G.Adj z (e a)) (hzb : G.Adj z (e b)) :
    r = 5 ∧ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) := by
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
  have hbad' : r ≠ 5 ∨ ¬ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) := by tauto
  obtain ⟨ht0, ht4, ht, ⟨j, hj⟩, htadj⟩ := fiveCliqueTwoPath_spec r a b hab hra hrb hbad'
  let t := fiveCliqueTwoPath r a b
  let f := e ∘ t
  have hfi : Function.Injective f := he.comp ht
  have hfw : ∀ i, f i ≠ w := fun i => hew (t i)
  have hzf : ∀ i, z ≠ f i := fun i => hzout (t i)
  have hcf : c ⟨z, hzw⟩ = c ⟨f j, hfw j⟩ := by
    have hsub : (⟨f j, hfw j⟩ : {x : V // x ≠ w}) = ⟨e r, hew r⟩ :=
      Subtype.ext (congrArg e hj)
    rw [hsub]
    exact hcolor
  have hno := rainbow_forbids_four_path hr w c f hfi
    (hadj _ _ (htadj 0)) (hadj _ _ (htadj 1))
    (hadj _ _ (htadj 2)) (hadj _ _ (htadj 3)) z hzw hfw hzf j hcf
  apply hno
  constructor
  · simpa only [f, t, Function.comp_apply, ht0] using hza
  · simpa only [f, t, Function.comp_apply, ht4] using hzb

theorem five_two_neighbor_indices_small_or_pair (A : Finset (Fin 6)) (r : Fin 6)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      r = 5 ∧ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0))) :
    A.card ≤ 1 ∨ r = 5 ∧ A ⊆ {0, 1} := by
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

noncomputable def fiveCliqueTwoNeighborIndices (G : SimpleGraph V)
    (e : Fin 6 → V) (z : V) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter (fun i => G.Adj z (e i))

/-- This holds in every actual deleted-point coloring avoiding the seven
specified vertices, not just a separately chosen coloring. -/
theorem five_clique_two_attachment_coloring_constraints
    (hr : RainbowSixCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 6))
    (e : Fin 6 → V) (he : Function.Injective e)
    (hadj : ∀ i j, FiveCliqueTwoAdj i j → G.Adj (e i) (e j))
    (hew : ∀ i, e i ≠ w) (z : V) (hzw : z ≠ w) (hzout : ∀ i, z ≠ e i) :
    (fiveCliqueTwoNeighborIndices G e z).card ≤ 1 ∨
      c ⟨z, hzw⟩ = c ⟨e 5, hew 5⟩ ∧ fiveCliqueTwoNeighborIndices G e z ⊆ {0, 1} := by
  classical
  have hci := five_clique_two_colors_injective hr w c e he hadj hew
  obtain ⟨r, hrcolor⟩ := Finite.surjective_of_injective hci (c ⟨z, hzw⟩)
  have hcolor : c ⟨z, hzw⟩ = c ⟨e r, hew r⟩ := hrcolor.symm
  have hpair : ∀ a ∈ fiveCliqueTwoNeighborIndices G e z,
      ∀ b ∈ fiveCliqueTwoNeighborIndices G e z, a ≠ b →
        r = 5 ∧ ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) := by
    intro a ha b hb hab
    exact five_clique_two_attachment_pair hr w c e he hadj hew z hzw hzout r hcolor
      a b hab (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  rcases five_two_neighbor_indices_small_or_pair (fiveCliqueTwoNeighborIndices G e z) r hpair
      with hsmall | ⟨hr, hsub⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨by simpa only [hr] using hcolor, hsub⟩

theorem actual_five_clique_two_attachment_coloring_constraints
    (hr : RainbowSixCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 6))
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i) (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (hqw : ∀ i, q i ≠ w) (hyw : y ≠ w)
    (z : V) (hzw : z ≠ w) (hzout : z ≠ y ∧ ∀ i, z ≠ q i) :
    (fiveCliqueTwoNeighborIndices G (fiveCliqueWithPoint q y) z).card ≤ 1 ∨
      c ⟨z, hzw⟩ = c ⟨y, hyw⟩ ∧
        fiveCliqueTwoNeighborIndices G (fiveCliqueWithPoint q y) z ⊆ {0, 1} := by
  have hew : ∀ i, fiveCliqueWithPoint q y i ≠ w := by
    intro i
    fin_cases i <;> simp [fiveCliqueWithPoint, hqw, hyw]
  have hzout' : ∀ i, z ≠ fiveCliqueWithPoint q y i := by
    intro i
    fin_cases i <;> simp [fiveCliqueWithPoint, hzout.1, hzout.2]
  exact five_clique_two_attachment_coloring_constraints hr w c _
    (fiveCliqueWithPoint_injective q y hq hy) (fiveCliqueWithPoint_adj q y hclique hy0 hy1)
    hew z hzw hzout'

end TaskH.Six

#print axioms TaskH.Six.fiveCliqueWithPoint
#print axioms TaskH.Six.fiveCliqueWithPoint_castSucc
#print axioms TaskH.Six.fiveCliqueWithPoint_of_lt
#print axioms TaskH.Six.fiveCliqueWithPoint_injective
#print axioms TaskH.Six.fiveCliqueWithPoint_adj
#print axioms TaskH.Six.five_clique_two_colors_injective
#print axioms TaskH.Six.five_clique_two_attachment_pair
#print axioms TaskH.Six.five_two_neighbor_indices_small_or_pair
#print axioms TaskH.Six.fiveCliqueTwoNeighborIndices
#print axioms TaskH.Six.five_clique_two_attachment_coloring_constraints
#print axioms TaskH.Six.actual_five_clique_two_attachment_coloring_constraints
