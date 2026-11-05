import Research.Backfill.Paper7.SetupCardinality

set_option autoImplicit false

noncomputable section

namespace Paper7Setup

open SimpleGraph BackfillPaper7.Challenge
open scoped Classical

theorem pq_length (b : ℕ) (p q : Fin b → ℕ) (k : Fin b) :
    (pq b p q k).length = p k + q k := by
  simp [pq]

#print axioms Paper7Setup.pq_length

theorem pq_get_one_or_two (b : ℕ) (p q : Fin b → ℕ) (k : Fin b)
    (j : Fin (pq b p q k).length) :
    (pq b p q k).get j = 1 ∨ (pq b p q k).get j = 2 := by
  have hm := List.get_mem (pq b p q k) j
  change (pq b p q k).get j ∈ List.replicate (p k) 1 ++ List.replicate (q k) 2 at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact Or.inl (List.mem_replicate.mp hm).2
  · exact Or.inr (List.mem_replicate.mp hm).2

#print axioms Paper7Setup.pq_get_one_or_two

/-- Root neighbors consist of the two circle neighbors and one initial
vertex for each positive arm at the root. -/
theorem sun_root_degree (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) (k : Fin b)
    (hpos : ∀ j : Fin (L k).length, 0 < (L k).get j) :
    (sunGraph b L).degree (Sum.inl k) = 2 + (L k).length := by
  let f : Fin (L k).length → SunV b L :=
    fun j => Sum.inr ⟨k, j, ⟨0, hpos j⟩⟩
  let R : Finset (SunV b L) :=
    ((cycleGraph b).neighborFinset k).image Sum.inl
  let A : Finset (SunV b L) := Finset.univ.image f
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : SunV b L => match x with
      | Sum.inl _ => 0
      | Sum.inr z => z.2.1.val) hij
  have hdis : Disjoint R A := by
    apply Finset.disjoint_left.mpr
    intro x hx hxa
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _hj, heq⟩ := Finset.mem_image.mp hxa
    change (Sum.inr ⟨k, j, ⟨0, hpos j⟩⟩ : SunV b L) = Sum.inl i at heq
    cases heq
  have hset : (sunGraph b L).neighborFinset (Sum.inl k) = R ∪ A := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    constructor
    · intro hx
      cases x with
      | inl i =>
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨i, (SimpleGraph.mem_neighborFinset (cycleGraph b) k i).mpr
          ((Paper7Cleared.sun_cycle_adj_iff b L hb k i).mp hx), rfl⟩
      | inr z =>
        rcases z with ⟨k', j, a⟩
        obtain ⟨hk, ha⟩ := (Paper7Cleared.sun_root_arm_adj_iff b L k k' j a).mp hx
        subst k'
        have haz : a = ⟨0, hpos j⟩ := Fin.ext ha
        subst a
        exact Finset.mem_union_right R (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact (Paper7Cleared.sun_cycle_adj_iff b L hb k i).mpr
          ((SimpleGraph.mem_neighborFinset (cycleGraph b) k i).mp hi)
      · obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
        exact (Paper7Cleared.sun_root_arm_adj_iff b L k k j ⟨0, hpos j⟩).mpr ⟨rfl, rfl⟩
  have hR : R.card = 2 := by
    change (((cycleGraph b).neighborFinset k).image
      (Sum.inl : Fin b → SunV b L)).card = 2
    rw [Finset.card_image_of_injective _ Sum.inl_injective,
      SimpleGraph.card_neighborFinset_eq_degree]
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
    exact SimpleGraph.cycleGraph_degree_three_le
  have hA : A.card = (L k).length := by
    change (Finset.univ.image f).card = (L k).length
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  change ((sunGraph b L).neighborFinset (Sum.inl k)).card = _
  rw [hset, Finset.card_union_of_disjoint hdis, hR, hA]

#print axioms Paper7Setup.sun_root_degree

theorem sun_arm_degree_one {b : ℕ} {L : Fin b → List ℕ} (k : Fin b)
    (j : Fin (L k).length) (hL : (L k).get j = 1) (a : Fin ((L k).get j)) :
    (sunGraph b L).degree (Sum.inr ⟨k, j, a⟩) = 1 := by
  have ha : a.val = 0 := by have := a.isLt; omega
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨Sum.inl k,
    (Paper7Cleared.sun_arm_root_adj_iff b L k k j a).mpr ⟨rfl, ha⟩, ?_⟩
  intro y hy
  cases y with
  | inl i =>
    exact congrArg Sum.inl
      ((Paper7Cleared.sun_arm_root_adj_iff b L i k j a).mp hy).1.symm
  | inr y =>
    rcases y with ⟨k', j', a'⟩
    obtain ⟨hk, hj, hs⟩ := (Paper7Cleared.sun_arm_adj_iff b L k k' j j' a a').mp hy
    subst k'
    have hje : j = j' := Fin.ext hj
    subst j'
    have := a'.isLt
    rcases hs with hs | hs <;> omega

#print axioms Paper7Setup.sun_arm_degree_one

theorem sun_arm_degree_two_first {b : ℕ} {L : Fin b → List ℕ} (k : Fin b)
    (j : Fin (L k).length) (hL : (L k).get j = 2) :
    (sunGraph b L).degree (Sum.inr ⟨k, j, ⟨0, by omega⟩⟩) = 2 := by
  let a0 : Fin ((L k).get j) := ⟨0, by omega⟩
  let a1 : Fin ((L k).get j) := ⟨1, by omega⟩
  have hset : (sunGraph b L).neighborFinset (Sum.inr ⟨k, j, a0⟩) =
      {Sum.inl k, Sum.inr ⟨k, j, a1⟩} := by
    ext y
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hy
      cases y with
      | inl i =>
        exact Or.inl (congrArg Sum.inl
          ((Paper7Cleared.sun_arm_root_adj_iff b L i k j a0).mp hy).1.symm)
      | inr y =>
        rcases y with ⟨k', j', a'⟩
        obtain ⟨hk, hj, hs⟩ := (Paper7Cleared.sun_arm_adj_iff b L k k' j j' a0 a').mp hy
        apply Or.inr
        apply Paper7SunMoments.sun_arm_vertex_eq_of_coords hk.symm hj.symm
        change a'.val = 1
        change 0 + 1 = a'.val ∨ a'.val + 1 = 0 at hs
        omega
    · rintro (rfl | rfl)
      · exact (Paper7Cleared.sun_arm_root_adj_iff b L k k j a0).mpr ⟨rfl, rfl⟩
      · exact (Paper7Cleared.sun_arm_adj_iff b L k k j j a0 a1).mpr
          ⟨rfl, rfl, Or.inl rfl⟩
  change ((sunGraph b L).neighborFinset (Sum.inr ⟨k, j, a0⟩)).card = 2
  rw [hset]
  simp

#print axioms Paper7Setup.sun_arm_degree_two_first

theorem sun_arm_degree_two_last {b : ℕ} {L : Fin b → List ℕ} (k : Fin b)
    (j : Fin (L k).length) (hL : (L k).get j = 2) :
    (sunGraph b L).degree (Sum.inr ⟨k, j, ⟨1, by omega⟩⟩) = 1 := by
  let a0 : Fin ((L k).get j) := ⟨0, by omega⟩
  let a1 : Fin ((L k).get j) := ⟨1, by omega⟩
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨Sum.inr ⟨k, j, a0⟩,
    (Paper7Cleared.sun_arm_adj_iff b L k k j j a1 a0).mpr
      ⟨rfl, rfl, Or.inr rfl⟩, ?_⟩
  intro y hy
  cases y with
  | inl i =>
    have ha := ((Paper7Cleared.sun_arm_root_adj_iff b L i k j a1).mp hy).2
    change 1 = 0 at ha
    omega
  | inr y =>
    rcases y with ⟨k', j', a'⟩
    obtain ⟨hk, hj, hs⟩ := (Paper7Cleared.sun_arm_adj_iff b L k k' j j' a1 a').mp hy
    apply Paper7SunMoments.sun_arm_vertex_eq_of_coords hk.symm hj.symm
    change a'.val = 0
    have ha' : a'.val < 2 := by
      subst k'
      have hje : j = j' := Fin.ext hj
      subst j'
      simpa only [hL] using a'.isLt
    change 1 + 1 = a'.val ∨ a'.val + 1 = 1 at hs
    omega

#print axioms Paper7Setup.sun_arm_degree_two_last

theorem sg_root_degree (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) (k : Fin b) :
    (SG b p q).degree (Sum.inl k) = 2 + p k + q k := by
  rw [sun_root_degree b (pq b p q) hb k]
  · rw [pq_length]
    omega
  · intro j
    rcases pq_get_one_or_two b p q k j with h | h <;> omega

#print axioms Paper7Setup.sg_root_degree

end Paper7Setup
