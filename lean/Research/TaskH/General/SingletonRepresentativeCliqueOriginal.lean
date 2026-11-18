import Research.TaskH.General.SingletonFullCliqueOriginal
import Research.TaskH.General.CliqueExteriorHookOriginal

/-! All k representatives below are selected from the actual original
root fibers. Their old colors prove injectivity; FULL is derived internally. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem original_singleton_palette_card {v : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) :
    (originalSingletonPalette c).card = (originalSingletonCenters c).card := by
  classical
  have hf : Function.Injective (fun z : originalSingletonCenters c =>
      c ⟨z.val, original_singleton_center_ne_root c z.property⟩) := by
    intro a b hc
    apply Subtype.ext
    by_contra hab
    exact original_singleton_centers_color_ne c a.property b.property hab _ _ hc
  unfold originalSingletonPalette
  rw [Finset.card_image_of_injective _ hf, Finset.card_attach]

theorem equality_original_singleton_or_full_representative (hk : 5 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcard : 3 ≤ (originalSingletonCenters c).card) (γ : Fin k) :
    ∃ (p : V) (hvp : G.Adj v p), c ⟨p, hvp.ne.symm⟩ = γ ∧
      (p ∈ originalSingletonCenters c ∨
        (γ ∉ originalSingletonPalette c ∧ ∀ a ∈ originalSingletonCenters c, G.Adj p a)) := by
  classical
  by_cases hγ : γ ∈ originalSingletonPalette c
  · obtain ⟨z, _, hzγ⟩ := Finset.mem_image.mp hγ
    obtain ⟨hvz, _⟩ := (mem_originalSingletonCenters c).mp z.property
    exact ⟨z.val, hvz, hzγ, Or.inl z.property⟩
  · obtain ⟨p, _, hvp, _, hpγ, _, _, hpfull, _⟩ :=
      equality_original_nonsingleton_full_empty hk hcrit hcount c hcard γ hγ
    exact ⟨p, hvp, hpγ, Or.inr ⟨hγ, hpfull⟩⟩

theorem equality_original_root_color_representatives (hk : 5 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcard : 3 ≤ (originalSingletonCenters c).card) :
    ∃ (f : Fin k → V) (hf : ∀ i, G.Adj v (f i)),
      (∀ i, c ⟨f i, (hf i).ne.symm⟩ = i) ∧ Function.Injective f ∧
      ∀ i, f i ∈ originalSingletonCenters c ∨
        (i ∉ originalSingletonPalette c ∧ ∀ a ∈ originalSingletonCenters c, G.Adj (f i) a) := by
  classical
  choose f hf hc hs using
    (fun i => equality_original_singleton_or_full_representative hk hcrit hcount c hcard i)
  refine ⟨f, hf, hc, ?_, hs⟩
  intro i j he
  exact (hc i).symm.trans ((congrArg c (Subtype.ext he)).trans (hc j))

theorem equality_original_representative_clique_complete
    (hcrit : IsCriticalPlus k G) {v : V}
    (f : Fin k → V) (hf : Function.Injective f)
    (hroot : ∀ i, G.Adj v (f i))
    (hedges : ∀ i j, i ≠ j → G.Adj (f i) (f j)) :
    IsCompleteOfOrder G (k + 1) := by
  classical
  let T := Finset.univ.image f
  have hvT : v ∉ T := by
    rintro hh
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hh
    exact (hroot i).ne hi.symm
  have hTcard : T.card = k := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  let S := insert v T
  have hS : G.IsClique (S : Set V) := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · exact False.elim (hab rfl)
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
        exact hroot j
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact (hroot i).symm
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
        exact hedges i j (fun he => hab (congrArg f he))
  have hScard : S.card = k + 1 := by
    rw [Finset.card_insert_of_notMem hvT, hTcard]
  exact critical_clique_succ_complete_original hcrit S hS hScard

theorem equality_original_three_singleton_complete_six (hk : 6 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcard : 3 ≤ (originalSingletonCenters c).card) :
    IsCompleteOfOrder G (k + 1) := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (originalSingletonCenters c).card)
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < (originalSingletonCenters c).card) a
  obtain ⟨f, hroot, hcolor, hf, hs⟩ :=
    equality_original_root_color_representatives (by omega) hcrit hcount c hcard
  apply equality_original_representative_clique_complete hcrit f hf hroot
  intro i j hij
  rcases hs i with hiJ | ⟨hi, hiFull⟩
  · rcases hs j with hjJ | ⟨_, hjFull⟩
    · exact equality_original_singleton_centers_clique (by omega) hcrit hcount c hcard
        hiJ hjJ (fun he => hij (hf he))
    · exact (hjFull (f i) hiJ).symm
  · rcases hs j with hjJ | ⟨hj, hjFull⟩
    · exact hiFull (f j) hjJ
    · exact equality_original_full_points_adjacent_aux hk hcrit hcount c ha hb hba.symm
        i j hij hi hj (hroot i) (hroot j) (hcolor i) (hcolor j)
        (hiFull a ha) (hiFull b hb) (hjFull a ha)

end TaskH.General

#print axioms TaskH.General.original_singleton_palette_card
#print axioms TaskH.General.equality_original_singleton_or_full_representative
#print axioms TaskH.General.equality_original_root_color_representatives
#print axioms TaskH.General.equality_original_representative_clique_complete
#print axioms TaskH.General.equality_original_three_singleton_complete_six
