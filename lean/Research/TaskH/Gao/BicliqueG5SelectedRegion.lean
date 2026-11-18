import Research.TaskH.Gao.G6ActualComponents
import Research.TaskH.Gao.CliqueCoreDegree

/-! The actual selected region contains at least two actual neighbors of w.
This is derived from the original degree; H is never supplied as nonempty. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem g5_selected_two_neighbors [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y w : V) (s k : ℕ)
    (hAB : Disjoint A B) (hy : y ∉ A ∪ B) (hw : w ∈ B \ {x})
    (hindB : ∀ a ∈ B, ∀ b ∈ B, ¬G.Adj a b)
    (hNy : G.neighborSet y = A) (hA : A.ncard = s + 1)
    (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    2 ≤ (G.neighborSet w ∩ g6SelectedRegion G A B y w).ncard := by
  let H := g6SelectedRegion G A B y w
  have hwy : w ≠ y := fun he => hy (Or.inr (he ▸ hw.1))
  have hdegree := hd w hw.2 hwy
  have hcover := g6_w_neighbor_cover G A B y w hw.1 hindB hNy hAB
  have hdis : Disjoint H A := by
    apply Set.disjoint_left.mpr
    intro z hzH hzA
    exact Set.disjoint_left.mp (g6Selected_disjoint_core G A B y w) hzH (Or.inl hzA)
  have hpart := disjoint_region_neighbor_partition G H A hdis w (fun z ez => hcover ez)
  have hcap := Set.ncard_le_ncard (Set.inter_subset_right : G.neighborSet w ∩ A ⊆ A)
  change 2 ≤ (G.neighborSet w ∩ H).ncard
  omega

theorem g5_selected_region_nonempty [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y w : V) (s k : ℕ)
    (hAB : Disjoint A B) (hy : y ∉ A ∪ B) (hw : w ∈ B \ {x})
    (hindB : ∀ a ∈ B, ∀ b ∈ B, ¬G.Adj a b)
    (hNy : G.neighborSet y = A) (hA : A.ncard = s + 1)
    (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    (g6SelectedRegion G A B y w).Nonempty := by
  have htwo := g5_selected_two_neighbors G A B x y w s k hAB hy hw hindB hNy hA hs hsk hd
  obtain ⟨z, hz⟩ := (Set.ncard_pos (Set.toFinite (G.neighborSet w ∩ g6SelectedRegion G A B y w))).mp
    (by omega : 0 < (G.neighborSet w ∩ g6SelectedRegion G A B y w).ncard)
  exact ⟨z, hz.2⟩

theorem g5_nonroot_B_exists [Fintype V] (B : Set V) (x : V) (s : ℕ)
    (hx : x ∈ B) (hs : 1 ≤ s) (hB : B.ncard = s + 1) :
    (B \ ({x} : Set V)).Nonempty := by
  have hc : (B \ ({x} : Set V)).ncard = s := by
    rw [Set.ncard_sdiff_singleton_of_mem hx, hB]
    omega
  exact (Set.ncard_pos (Set.toFinite _)).mp (by omega)

#print axioms g5_selected_two_neighbors
#print axioms g5_selected_region_nonempty
#print axioms g5_nonroot_B_exists
end TaskH.Gao
