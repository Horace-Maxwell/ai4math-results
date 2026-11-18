import Research.TaskH.General.SingletonSpineOriginal
import Research.TaskH.General.FiniteColorAvoidance

/-! The finite choices needed for the k-3-vertex spine are made internally.
The palette is the image of actual singleton centers, not a whole-class size. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
theorem finset_subset_card_with_two {J : Finset V} {a b : V} {n : ℕ}
    (ha : a ∈ J) (hb : b ∈ J) (hab : a ≠ b) (hn : 2 ≤ n) (hnJ : n ≤ J.card) :
    ∃ K ⊆ J, a ∈ K ∧ b ∈ K ∧ K.card = n := by
  classical
  have hba : b ∈ J.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hsize : (J.erase a |>.erase b).card = J.card - 2 := by
    rw [Finset.card_erase_of_mem hba, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq
    (show n - 2 ≤ (J.erase a |>.erase b).card by omega)
  have haT : a ∉ T := by
    intro hh
    exact Finset.notMem_erase a J (Finset.mem_of_mem_erase (hT hh))
  have hbT : b ∉ T := by
    intro hh
    exact Finset.notMem_erase b (J.erase a) (hT hh)
  refine ⟨insert a (insert b T), ?_, by simp, by simp, ?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ha
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hb
    · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hT hz))
  · rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_insert] using
      (show ¬(a = b ∨ a ∈ T) from fun hh => hh.elim hab haT)),
      Finset.card_insert_of_notMem hbT, hTcard]
    omega

noncomputable def originalSingletonPalette {v : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) : Finset (Fin k) := by
  classical
  exact (originalSingletonCenters c).attach.image
    (fun z => c ⟨z.val, original_singleton_center_ne_root c z.property⟩)

theorem original_singleton_palette_card_le {v : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) :
    (originalSingletonPalette c).card ≤ (originalSingletonCenters c).card := by
  classical
  unfold originalSingletonPalette
  exact (Finset.card_image_le).trans (le_of_eq Finset.card_attach)

theorem original_singleton_color_mem_palette {v z : V}
    (c : (G.induce {w | w ≠ v}).Coloring (Fin k))
    (hzJ : z ∈ originalSingletonCenters c) (hzv : z ≠ v) :
    c ⟨z, hzv⟩ ∈ originalSingletonPalette c := by
  classical
  exact Finset.mem_image.mpr ⟨⟨z, hzJ⟩, Finset.mem_attach _ _, rfl⟩

theorem equality_original_singleton_spine_root_color_avoidance (hk : 5 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcard : 3 ≤ (originalSingletonCenters c).card)
    (ha : a ∈ originalSingletonCenters c) (hb : b ∈ originalSingletonCenters c)
    (hab : a ≠ b) (γ : Fin k) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.length = k - 4 ∧ v ∉ p.support ∧
      ∀ (z : V) (hzv : z ≠ v), c ⟨z, hzv⟩ = γ →
        z ∉ originalSingletonCenters c → z ∉ p.support := by
  classical
  let J := originalSingletonCenters c
  by_cases hlarge : k - 3 ≤ J.card
  · obtain ⟨K, hK, haK, hbK, hKcard⟩ :=
      finset_subset_card_with_two ha hb hab (by omega : 2 ≤ k - 3) hlarge
    let D : Fin 0 → Fin k := Fin.elim0
    obtain ⟨p, hp, hlen, hv, hsupp⟩ := equality_original_singleton_spine
      (by omega) hcrit hcount c hcard K hK (by omega) haK hbK hab
      (s := 0) (by omega) D (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i)
    refine ⟨p, hp, by omega, hv, ?_⟩
    intro z hzv _ hzJ hzp
    rcases hsupp z hzp with hzK | ⟨_, i, _⟩
    · exact hzJ (hK hzK)
    · exact Fin.elim0 i
  · let s := k - 3 - J.card
    let S := insert γ (originalSingletonPalette c)
    have hS : S.card ≤ J.card + 1 := by
      exact (Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right (original_singleton_palette_card_le c) 1)
    have hcap : s + S.card ≤ k := by dsimp [s]; omega
    obtain ⟨D, hD, hDS⟩ := exists_color_list_avoiding_palette S hcap
    have hDJ : ∀ i (z : V) (_hzJ : z ∈ originalSingletonCenters c) (hzv : z ≠ v),
        D i ≠ c ⟨z, hzv⟩ := by
      intro i z hzJ hzv hc
      exact hDS i (Finset.mem_insert_of_mem (by
        rw [hc]
        exact original_singleton_color_mem_palette c hzJ hzv))
    obtain ⟨p, hp, hlen, hv, hsupp⟩ := equality_original_singleton_spine
      (by omega) hcrit hcount c hcard J (fun _ hz => hz) (by dsimp [J]; omega)
      ha hb hab (by dsimp [s]; omega) D hD hDJ
    refine ⟨p, hp, by dsimp [s] at hlen; omega, hv, ?_⟩
    intro z hzv hc hzJ hzp
    rcases hsupp z hzp with hz | ⟨hzv', i, hi⟩
    · exact hzJ hz
    · have he : D i = γ := hi.symm.trans hc
      exact hDS i (Finset.mem_insert.mpr (Or.inl he))

end TaskH.General

#print axioms TaskH.General.finset_subset_card_with_two
#print axioms TaskH.General.originalSingletonPalette
#print axioms TaskH.General.original_singleton_palette_card_le
#print axioms TaskH.General.original_singleton_color_mem_palette
#print axioms TaskH.General.equality_original_singleton_spine_root_color_avoidance
