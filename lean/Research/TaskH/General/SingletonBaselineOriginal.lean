import Research.TaskH.General.SingletonRepresentativeCliqueOriginal

/-! The k=5 boundary is handled explicitly by the actual K5 double-exterior
hook theorem. It is not obtained by asserting that a six-cycle has length 5. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_three_singleton_complete_five
    (hcrit : IsCriticalPlus 5 G) (hcount : modCycleCount 5 G = bound 5)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin 5))
    (hcard : 3 ≤ (originalSingletonCenters c).card) : IsCompleteOfOrder G 6 := by
  classical
  by_cases hex : ∃ γ δ : Fin 5, γ ≠ δ ∧ γ ∉ originalSingletonPalette c ∧
      δ ∉ originalSingletonPalette c
  · obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := hex
    let A := Finset.univ \ originalSingletonPalette c
    have hγA : γ ∈ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hγ⟩
    have hδA : δ ∈ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hδ⟩
    have htwo : 2 ≤ A.card := by
      have hs : ({γ, δ} : Finset (Fin 5)) ⊆ A := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hγA
        · exact (Finset.mem_singleton.mp hi).symm ▸ hδA
      have he : ({γ, δ} : Finset (Fin 5)).card = 2 := by simp [hγδ]
      exact he ▸ Finset.card_le_card hs
    have hAsize : A.card + (originalSingletonPalette c).card = 5 := by
      exact (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)).trans
        (by simp only [Finset.card_univ, Fintype.card_fin])
    have hJsize : (originalSingletonCenters c).card = 3 := by
      have he := original_singleton_palette_card c
      omega
    obtain ⟨P, E, hvP, hvE, hPγ, hEγ, hEP, hPfull, _⟩ :=
      equality_original_nonsingleton_full_empty (by omega) hcrit hcount c hcard γ hγ
    obtain ⟨T, _, hvT, _, hTδ, _, _, hTfull, _⟩ :=
      equality_original_nonsingleton_full_empty (by omega) hcrit hcount c hcard δ hδ
    have hPJ : P ∉ originalSingletonCenters c := by
      intro hh; apply hγ; rw [← hPγ]
      exact original_singleton_color_mem_palette c hh hvP.ne.symm
    have hEJ : E ∉ originalSingletonCenters c := by
      intro hh; apply hγ; rw [← hEγ]
      exact original_singleton_color_mem_palette c hh hvE.ne.symm
    have hTJ : T ∉ originalSingletonCenters c := by
      intro hh; apply hδ; rw [← hTδ]
      exact original_singleton_color_mem_palette c hh hvT.ne.symm
    have hTP : T ≠ P := by
      intro he
      apply hγδ
      exact hPγ.symm.trans ((congrArg c (Subtype.ext he)).symm.trans hTδ)
    have hTE : T ≠ E := by
      intro he
      apply hγδ
      exact hEγ.symm.trans ((congrArg c (Subtype.ext he)).symm.trans hTδ)
    let Q := insert v (insert P (originalSingletonCenters c))
    have hvJ : v ∉ originalSingletonCenters c := by
      intro hh
      exact original_singleton_center_ne_root c hh rfl
    have hQcard : Q.card = 5 := by
      change (insert v (insert P (originalSingletonCenters c))).card = 5
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert]
        exact fun hh => hh.elim hvP.ne hvJ),
        Finset.card_insert_of_notMem hPJ, hJsize]
    have hQ : G.IsClique (Q : Set V) := by
      intro a ha b hb hab
      have haQ : a = v ∨ a = P ∨ a ∈ originalSingletonCenters c := by
        rcases Finset.mem_insert.mp ha with hav | haRest
        · exact Or.inl hav
        · exact Or.inr (Finset.mem_insert.mp haRest)
      have hbQ : b = v ∨ b = P ∨ b ∈ originalSingletonCenters c := by
        rcases Finset.mem_insert.mp hb with hbv | hbRest
        · exact Or.inl hbv
        · exact Or.inr (Finset.mem_insert.mp hbRest)
      rcases haQ with hav | haP | haJ
      · subst a
        rcases hbQ with hbv | hbP | hbJ
        · subst b
          exact False.elim (hab rfl)
        · subst b
          exact hvP
        · exact ((mem_originalSingletonCenters c).mp hbJ).choose
      · subst a
        rcases hbQ with hbv | hbP | hbJ
        · subst b
          exact hvP.symm
        · subst b
          exact False.elim (hab rfl)
        · exact hPfull b hbJ
      · rcases hbQ with hbv | hbP | hbJ
        · subst b
          exact (((mem_originalSingletonCenters c).mp haJ).choose).symm
        · subst b
          exact (hPfull a haJ).symm
        · exact equality_original_singleton_centers_clique (by omega) hcrit hcount c hcard haJ hbJ hab
    have hTQ : T ∉ Q := by
      simp only [Q, Finset.mem_insert, not_or]
      exact ⟨hvT.ne.symm, hTP, hTJ⟩
    have hEQ : E ∉ Q := by
      simp only [Q, Finset.mem_insert, not_or]
      exact ⟨hvE.ne.symm, hEP, hEJ⟩
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (originalSingletonCenters c).card)
    obtain ⟨hva, _⟩ := (mem_originalSingletonCenters c).mp ha
    exact False.elim (equality_original_k_clique_two_exterior_hooks (by omega) hcrit hcount
      Q hQ hQcard hTQ hEQ hTE (by simp [Q]) (by simp [Q, ha]) hva.ne
      hvT.symm (hTfull a ha))
  · obtain ⟨f, hroot, _, hf, hs⟩ :=
      equality_original_root_color_representatives (by omega) hcrit hcount c hcard
    apply equality_original_representative_clique_complete hcrit f hf hroot
    intro i j hij
    rcases hs i with hiJ | ⟨hi, hiFull⟩
    · rcases hs j with hjJ | ⟨_, hjFull⟩
      · exact equality_original_singleton_centers_clique (by omega) hcrit hcount c hcard
          hiJ hjJ (fun he => hij (hf he))
      · exact (hjFull (f i) hiJ).symm
    · rcases hs j with hjJ | ⟨hj, _⟩
      · exact hiFull (f j) hjJ
      · exact False.elim (hex ⟨i, j, hij, hi, hj⟩)

theorem equality_original_three_singleton_complete {k : ℕ} (hk : 5 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcard : 3 ≤ (originalSingletonCenters c).card) :
    IsCompleteOfOrder G (k + 1) := by
  by_cases hk6 : 6 ≤ k
  · exact equality_original_three_singleton_complete_six hk6 hcrit hcount c hcard
  · have he : k = 5 := by omega
    subst k
    exact equality_original_three_singleton_complete_five hcrit hcount c hcard

theorem equality_original_singleton_centers_le_two {k : ℕ} (hk : 5 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1))
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) :
    (originalSingletonCenters c).card ≤ 2 := by
  by_contra hh
  exact hnot (equality_original_three_singleton_complete hk hcrit hcount c (by omega))

end TaskH.General

#print axioms TaskH.General.equality_original_three_singleton_complete_five
#print axioms TaskH.General.equality_original_three_singleton_complete
#print axioms TaskH.General.equality_original_singleton_centers_le_two
