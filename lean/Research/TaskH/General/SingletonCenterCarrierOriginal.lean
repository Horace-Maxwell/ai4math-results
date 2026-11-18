import Research.TaskH.General.ThreeSingletonCliqueOriginal

/-! The singleton-center carrier is defined from the actual root-neighbor
fibers, rather than from a supplied clique or a whole-color-class oracle. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

def OriginalSingletonCenter {v : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) (a : V) : Prop :=
  ∃ hva : G.Adj v a, ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
    c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a

noncomputable def originalSingletonCenters {v : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) : Finset V := by
  classical
  exact Finset.univ.filter (OriginalSingletonCenter c)

theorem mem_originalSingletonCenters {v a : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) :
    a ∈ originalSingletonCenters c ↔ OriginalSingletonCenter c a := by
  classical
  simp only [originalSingletonCenters, Finset.mem_filter, Finset.mem_univ, true_and]

theorem original_singleton_center_ne_root {v a : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (ha : a ∈ originalSingletonCenters c) : a ≠ v := by
  obtain ⟨hva, _⟩ := (mem_originalSingletonCenters c).mp ha
  exact hva.ne.symm

theorem original_singleton_centers_color_ne {v a b : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (ha : a ∈ originalSingletonCenters c) (hb : b ∈ originalSingletonCenters c)
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) :
    c ⟨a, hav⟩ ≠ c ⟨b, hbv⟩ := by
  obtain ⟨_, haunique⟩ := (mem_originalSingletonCenters c).mp ha
  obtain ⟨hvb, _⟩ := (mem_originalSingletonCenters c).mp hb
  intro hc
  exact hab (haunique b hbv hvb hc.symm).symm

theorem original_singleton_third_exists {v a b : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcard : 3 ≤ (originalSingletonCenters c).card) :
    ∃ h ∈ originalSingletonCenters c, h ≠ a ∧ h ≠ b := by
  classical
  by_contra! hh
  have hsub : originalSingletonCenters c ⊆ ({a, b} : Finset V) := by
    intro z hz
    by_cases hza : z = a
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl hza
    · have hzb : z = b := hh z hz hza
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr hzb
  have hle := Finset.card_le_card hsub
  have htwo : ({a, b} : Finset V).card ≤ 2 := Finset.card_le_two
  omega

theorem equality_original_singleton_centers_clique (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcard : 3 ≤ (originalSingletonCenters c).card) :
    G.IsClique (originalSingletonCenters c : Set V) := by
  intro a ha b hb hab
  obtain ⟨h, hh, hha, hhb⟩ := original_singleton_third_exists c hcard (a := a) (b := b)
  obtain ⟨hva, haunique⟩ := (mem_originalSingletonCenters c).mp ha
  obtain ⟨hvb, hbunique⟩ := (mem_originalSingletonCenters c).mp hb
  obtain ⟨hvh, hhunique⟩ := (mem_originalSingletonCenters c).mp hh
  exact equality_original_three_singleton_centers_adjacent hk hcrit hcount
    hvh hva hvb c hhunique haunique hbunique
    (original_singleton_centers_color_ne c hh ha hha _ _)
    (original_singleton_centers_color_ne c hh hb hhb _ _)
    (original_singleton_centers_color_ne c ha hb hab _ _)

end TaskH.General

#print axioms TaskH.General.OriginalSingletonCenter
#print axioms TaskH.General.originalSingletonCenters
#print axioms TaskH.General.mem_originalSingletonCenters
#print axioms TaskH.General.original_singleton_center_ne_root
#print axioms TaskH.General.original_singleton_centers_color_ne
#print axioms TaskH.General.original_singleton_third_exists
#print axioms TaskH.General.equality_original_singleton_centers_clique
