import Research.TaskH.FourCountData

/-!
The high-minimum-degree branch of Task H at k=4.

This argument counts actual ordered quadruples with four distinct vertices,
then maps them into the frozen set of cycle edge sets. Its hypotheses concern
the actual graph's degrees and vertex cardinality, not an assumed common-
neighbour counting formula or an abstract cycle budget.
-/

universe u

namespace TaskH.FourCount

open SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

def orderedPairs : Finset (V × V) := (Finset.univ : Finset V).offDiag

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def commonFinset (a c : V) : Finset V := G.neighborFinset a ∩ G.neighborFinset c

@[simp] theorem mem_commonFinset (a c x : V) :
    x ∈ commonFinset G a c ↔ G.Adj a x ∧ G.Adj c x := by
  simp [commonFinset, G.mem_neighborFinset]

def oppositeQuads : Finset (Σ _ac : V × V, V × V) :=
  orderedPairs.sigma fun ac => (commonFinset G ac.1 ac.2).offDiag

def endWedges : Finset (Σ _ac : V × V, V) :=
  orderedPairs.sigma fun ac => commonFinset G ac.1 ac.2

def centerWedges : Finset (Σ _x : V, V × V) :=
  (Finset.univ : Finset V).sigma fun x => (G.neighborFinset x).offDiag

def encodeQuad (w : Σ _ac : V × V, V × V) : Fin 4 → V :=
  ![w.1.1, w.2.1, w.1.2, w.2.2]

omit [Fintype V] [DecidableEq V] in
theorem encodeQuad_injective : Function.Injective (encodeQuad (V := V)) := by
  rintro ⟨⟨a, c⟩, ⟨x, y⟩⟩ ⟨⟨b, d⟩, ⟨z, t⟩⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  change a = b at h0
  change x = z at h1
  change c = d at h2
  change y = t at h3
  subst b; subst z; subst d; subst t
  rfl

theorem encodeQuad_isQuad {w : Σ _ac : V × V, V × V}
    (hw : w ∈ oppositeQuads G) : IsQuad G (encodeQuad w) := by
  rcases w with ⟨⟨a, c⟩, ⟨x, y⟩⟩
  have h := Finset.mem_sigma.mp hw
  have hac : a ≠ c := (Finset.mem_offDiag.mp h.1).2.2
  have hxy := Finset.mem_offDiag.mp h.2
  have hax := (mem_commonFinset G a c x).mp hxy.1
  have hay := (mem_commonFinset G a c y).mp hxy.2.1
  have hny : x ≠ y := hxy.2.2
  have hxa : x ≠ a := hax.1.ne.symm
  have hxc : x ≠ c := hax.2.ne.symm
  have hya : y ≠ a := hay.1.ne.symm
  have hyc : y ≠ c := hay.2.ne.symm
  refine ⟨?_, hax.1, hax.2.symm, hay.2, hay.1.symm⟩
  intro i j he
  fin_cases i <;> fin_cases j <;>
    simp_all [encodeQuad, ne_comm]

theorem oppositeQuads_card_le_quadWords :
    (oppositeQuads G).card ≤ (quadWords G).card := by
  classical
  apply Finset.card_le_card_of_injOn encodeQuad
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, encodeQuad_isQuad G hw⟩
  · exact fun _ _ _ _ h => encodeQuad_injective h

def transposeWedge (w : Σ _ac : V × V, V) : Σ _x : V, V × V := ⟨w.2, w.1⟩

omit [Fintype V] [DecidableEq V] in
theorem transposeWedge_injective : Function.Injective (transposeWedge (V := V)) := by
  rintro ⟨⟨a, c⟩, x⟩ ⟨⟨b, d⟩, y⟩ h
  cases h
  rfl

/-- Count length-two paths by their middle vertex or by their ordered endpoints. -/
theorem endWedges_card_eq_centerWedges : (endWedges G).card = (centerWedges G).card := by
  apply Finset.card_bij (fun w _ => transposeWedge w)
  · rintro ⟨⟨a, c⟩, x⟩ hw
    have h := Finset.mem_sigma.mp hw
    have hn : a ≠ c := (Finset.mem_offDiag.mp h.1).2.2
    have hx := (mem_commonFinset G a c x).mp h.2
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_offDiag.mpr ⟨?_, ?_, hn⟩⟩
    · exact (G.mem_neighborFinset x a).mpr hx.1.symm
    · exact (G.mem_neighborFinset x c).mpr hx.2.symm
  · exact fun _ _ _ _ h => transposeWedge_injective h
  · rintro ⟨x, ⟨a, c⟩⟩ hw
    have h := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hw).2
    refine ⟨⟨(a, c), x⟩, ?_, rfl⟩
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, h.2.2⟩, ?_⟩
    exact (mem_commonFinset G a c x).mpr
      ⟨((G.mem_neighborFinset x a).mp h.1).symm,
        ((G.mem_neighborFinset x c).mp h.2.1).symm⟩

private theorem two_mul_le_square_sub_add_two (t : ℕ) :
    2 * t ≤ t * t - t + 2 := by
  rcases t with _ | t
  · decide
  rcases t with _ | t
  · decide
  have hle : t + 2 ≤ (t + 2) * (t + 2) := by nlinarith
  have hsub := Nat.sub_add_cancel hle
  nlinarith [Nat.zero_le (t * t)]

/-- Every endpoint pair with t common neighbours gives t(t-1) ordered squares. -/
theorem twice_endWedges_le_oppositeQuads_add_pairs :
    2 * (endWedges G).card ≤ (oppositeQuads G).card + 2 * (orderedPairs (V := V)).card := by
  rw [endWedges, oppositeQuads, Finset.card_sigma, Finset.card_sigma]
  calc
    2 * (∑ ac ∈ orderedPairs, (commonFinset G ac.1 ac.2).card) =
        ∑ ac ∈ orderedPairs, 2 * (commonFinset G ac.1 ac.2).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ ac ∈ orderedPairs, ((commonFinset G ac.1 ac.2).offDiag.card + 2) := by
      apply Finset.sum_le_sum
      intro ac _
      rw [Finset.offDiag_card]
      exact two_mul_le_square_sub_add_two _
    _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]

omit [DecidableEq V] in
theorem twenty_mul_card_le_centerWedges
    (hdeg : ∀ v : V, 5 ≤ G.degree v) :
    20 * Fintype.card V ≤ (centerWedges G).card := by
  rw [centerWedges, Finset.card_sigma]
  calc
    20 * Fintype.card V = ∑ _v : V, 20 := by simp [Nat.mul_comm]
    _ ≤ ∑ v : V, (G.neighborFinset v).offDiag.card := by
      apply Finset.sum_le_sum
      intro v _
      rw [Finset.offDiag_card, G.card_neighborFinset_eq_degree]
      have hd := hdeg v
      have hpred : 4 ≤ G.degree v - 1 := by omega
      have hmul : 5 * 4 ≤ G.degree v * (G.degree v - 1) :=
        Nat.mul_le_mul hd hpred
      simpa only [Nat.mul_sub_one] using hmul

/-- A completely graph-level lower bound, already using the frozen count. -/
theorem forty_mul_card_le_eight_cycles_add_orderedPairs
    (hdeg : ∀ v : V, 5 ≤ G.degree v) :
    40 * Fintype.card V ≤
      8 * Challenge.modCycleCount 4 G + 2 * (orderedPairs (V := V)).card := by
  have h1 := twenty_mul_card_le_centerWedges G hdeg
  have h2 := twice_endWedges_le_oppositeQuads_add_pairs G
  have h3 := oppositeQuads_card_le_quadWords G
  have h4 := quadWords_card_le_eight_mul_modCycleCount G
  rw [endWedges_card_eq_centerWedges G] at h2
  omega

omit [DecidableEq V] in
theorem orderedPairs_card_add_card :
    (orderedPairs (V := V)).card + Fintype.card V = Fintype.card V * Fintype.card V := by
  rw [orderedPairs, Finset.offDiag_card, Finset.card_univ]
  exact Nat.sub_add_cancel (Nat.le_mul_self _)

/-- The real graph must contain at least 23 modulo-four cycles on 6--15 vertices. -/
theorem twenty_three_le_modCycleCount_of_minDegree_five
    (hdeg : ∀ v : V, 5 ≤ G.degree v)
    (hn6 : 6 ≤ Fintype.card V) (hn15 : Fintype.card V ≤ 15) :
    23 ≤ Challenge.modCycleCount 4 G := by
  have h := forty_mul_card_le_eight_cycles_add_orderedPairs G hdeg
  have hp := orderedPairs_card_add_card (V := V)
  have hr : (90 : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≤
      21 * (Fintype.card V : ℤ) := by
    have h6 : (6 : ℤ) ≤ Fintype.card V := by exact_mod_cast hn6
    have h15 : (Fintype.card V : ℤ) ≤ 15 := by exact_mod_cast hn15
    nlinarith [mul_nonneg (sub_nonneg.mpr h6) (sub_nonneg.mpr h15)]
  have hrn : 90 + Fintype.card V * Fintype.card V ≤ 21 * Fintype.card V := by
    exact_mod_cast hr
  have hc : 90 ≤ 4 * Challenge.modCycleCount 4 G := by omega
  omega

theorem not_fifteen_cycles_of_minDegree_five
    (hdeg : ∀ v : V, 5 ≤ G.degree v)
    (hn6 : 6 ≤ Fintype.card V) (hn15 : Fintype.card V ≤ 15) :
    Challenge.modCycleCount 4 G ≠ 15 := by
  have h := twenty_three_le_modCycleCount_of_minDegree_five G hdeg hn6 hn15
  omega

end TaskH.FourCount

#print axioms TaskH.FourCount.endWedges_card_eq_centerWedges
#print axioms TaskH.FourCount.twice_endWedges_le_oppositeQuads_add_pairs
#print axioms TaskH.FourCount.forty_mul_card_le_eight_cycles_add_orderedPairs
#print axioms TaskH.FourCount.twenty_three_le_modCycleCount_of_minDegree_five
#print axioms TaskH.FourCount.not_fifteen_cycles_of_minDegree_five
