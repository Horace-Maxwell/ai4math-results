import Research.TaskH.FiniteBudget

/-!
Packing bounds for actual graph neighbor sets. These conditional finite-set
helpers do not assert the disjointness needed by an original graph branch;
that disjointness must be proved using its actual rainbow-cycle transport.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def packingNeighborsIn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (x : V) : Finset V := S.filter (fun y => G.Adj x y)

omit [Fintype V] in
theorem packingNeighborsIn_subset (S : Finset V) (x : V) :
    packingNeighborsIn G S x ⊆ S := Finset.filter_subset _ _

theorem packingNeighborsIn_partition (S : Finset V) (x : V) :
    (packingNeighborsIn G S x).card + (packingNeighborsIn G Sᶜ x).card = G.degree x := by
  classical
  have he : packingNeighborsIn G S x ∪ packingNeighborsIn G Sᶜ x =
      G.neighborFinset x := by
    ext y
    simp only [packingNeighborsIn, Finset.mem_union, Finset.mem_filter,
      Finset.mem_compl, G.mem_neighborFinset]
    tauto
  have hd : Disjoint (packingNeighborsIn G S x) (packingNeighborsIn G Sᶜ x) := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    exact (Finset.mem_compl.mp (Finset.mem_filter.mp hz).1)
      (Finset.mem_filter.mp hy).1
  rw [← Finset.card_union_of_disjoint hd, he, G.card_neighborFinset_eq_degree]

theorem packingNeighborsIn_compl_lower (S : Finset V) (x : V) (δ b : ℕ)
    (hdegree : δ ≤ G.degree x) (hinside : (packingNeighborsIn G S x).card ≤ b) :
    δ - b ≤ (packingNeighborsIn G Sᶜ x).card := by
  have hh := packingNeighborsIn_partition (G := G) S x
  omega

omit [Fintype V] in
theorem actual_open_neighborhood_weighted_packing
    (T H : Finset V) (B : V → ℕ)
    (hrow : ∀ x ∈ T, B x ≤ (packingNeighborsIn G H x).card)
    (hcommon : ∀ z ∈ H, ∀ x ∈ T, ∀ y ∈ T,
      G.Adj x z → G.Adj y z → x = y) :
    (∑ x ∈ T, B x) ≤ H.card := by
  classical
  have hcol : ∀ z ∈ H, (T.filter (fun x => G.Adj x z)).card ≤ 1 := by
    intro z hz
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact hcommon z hz x (Finset.mem_filter.mp hx).1 y
      (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2
  calc
    (∑ x ∈ T, B x) ≤ ∑ x ∈ T, (packingNeighborsIn G H x).card :=
      Finset.sum_le_sum hrow
    _ = ∑ z ∈ H, (T.filter (fun x => G.Adj x z)).card := by
      convert FiniteBudget.relation_double_count T H G.Adj using 1 <;>
        apply Finset.sum_congr rfl
      all_goals
        intro x _
        congr 1
        ext z
        simp only [packingNeighborsIn, Finset.mem_filter]
    _ ≤ ∑ _z ∈ H, 1 := Finset.sum_le_sum hcol
    _ = H.card := by simp

omit [Fintype V] in
theorem actual_open_neighborhood_uniform_packing
    (T H : Finset V) (b : ℕ)
    (hrow : ∀ x ∈ T, b ≤ (packingNeighborsIn G H x).card)
    (hcommon : ∀ z ∈ H, ∀ x ∈ T, ∀ y ∈ T,
      G.Adj x z → G.Adj y z → x = y) : b * T.card ≤ H.card := by
  have hh := actual_open_neighborhood_weighted_packing T H (fun _ => b) hrow hcommon
  simpa [Nat.mul_comm] using hh

omit [Fintype V] in
theorem actual_open_neighborhood_two_class_packing
    (M P H : Finset V) (a b : ℕ) (hdisjoint : Disjoint M P)
    (hM : ∀ x ∈ M, a ≤ (packingNeighborsIn G H x).card)
    (hP : ∀ x ∈ P, b ≤ (packingNeighborsIn G H x).card)
    (hcommon : ∀ z ∈ H, ∀ x ∈ M ∪ P, ∀ y ∈ M ∪ P,
      G.Adj x z → G.Adj y z → x = y) :
    a * M.card + b * P.card ≤ H.card := by
  classical
  let B : V → ℕ := fun x => if x ∈ M then a else b
  have hrow : ∀ x ∈ M ∪ P, B x ≤ (packingNeighborsIn G H x).card := by
    intro x hx
    by_cases hxM : x ∈ M
    · simpa [B, hxM] using hM x hxM
    · have hxP := (Finset.mem_union.mp hx).resolve_left hxM
      simpa [B, hxM] using hP x hxP
  have hh := actual_open_neighborhood_weighted_packing (M ∪ P) H B hrow hcommon
  rw [Finset.sum_union hdisjoint] at hh
  have hsM : (∑ x ∈ M, B x) = a * M.card := by
    calc
      (∑ x ∈ M, B x) = ∑ _x ∈ M, a := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [B, hx]
      _ = a * M.card := by simp [Nat.mul_comm]
  have hsP : (∑ x ∈ P, B x) = b * P.card := by
    have hnot : ∀ x ∈ P, x ∉ M := by
      intro x hxP hxM
      exact Finset.disjoint_left.mp hdisjoint hxM hxP
    calc
      (∑ x ∈ P, B x) = ∑ _x ∈ P, b := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [B, hnot x hx]
      _ = b * P.card := by simp [Nat.mul_comm]
  rw [hsM, hsP] at hh
  exact hh

end TaskH.Six

#print axioms TaskH.Six.packingNeighborsIn
#print axioms TaskH.Six.packingNeighborsIn_subset
#print axioms TaskH.Six.packingNeighborsIn_partition
#print axioms TaskH.Six.packingNeighborsIn_compl_lower
#print axioms TaskH.Six.actual_open_neighborhood_weighted_packing
#print axioms TaskH.Six.actual_open_neighborhood_uniform_packing
#print axioms TaskH.Six.actual_open_neighborhood_two_class_packing
