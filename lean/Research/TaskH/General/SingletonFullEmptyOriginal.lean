import Research.TaskH.General.SingletonFiberHookUniquenessOriginal

/-! FULL/EMPTY is derived for each actual nonsingleton root color.
The second EMPTY point comes from failure of singleton-fiber uniqueness,
not from an assumption about the size of the whole deleted color class. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_nonsingleton_color_touches_each_center (hk : 5 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcard : 3 ≤ (originalSingletonCenters c).card)
    (γ : Fin k) (hγ : γ ∉ originalSingletonPalette c)
    {b : V} (hb : b ∈ originalSingletonCenters c) :
    ∃ (p : V) (hvp : G.Adj v p), c ⟨p, hvp.ne.symm⟩ = γ ∧ G.Adj p b := by
  classical
  obtain ⟨a, ha, hab⟩ := Finset.exists_mem_ne (by omega : 1 < (originalSingletonCenters c).card) b
  obtain ⟨hva, hau⟩ := (mem_originalSingletonCenters c).mp ha
  obtain ⟨hvb, hbu⟩ := (mem_originalSingletonCenters c).mp hb
  have hγa : γ ≠ c ⟨a, hva.ne.symm⟩ := by
    intro he
    apply hγ
    rw [he]
    exact original_singleton_color_mem_palette c ha hva.ne.symm
  have hγb : γ ≠ c ⟨b, hvb.ne.symm⟩ := by
    intro he
    apply hγ
    rw [he]
    exact original_singleton_color_mem_palette c hb hvb.ne.symm
  obtain ⟨p, hpv, hvp, hpγ, hpb⟩ := equality_original_singleton_color_fiber_touches
    (by omega) hcrit hcount hva hvb c hau hbu
    (original_singleton_centers_color_ne c ha hb hab _ _) γ hγa hγb
  exact ⟨p, hvp, hpγ, hpb⟩

theorem equality_original_nonsingleton_full_empty (hk : 5 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcard : 3 ≤ (originalSingletonCenters c).card)
    (γ : Fin k) (hγ : γ ∉ originalSingletonPalette c) :
    ∃ (P E : V) (hvP : G.Adj v P) (hvE : G.Adj v E),
      c ⟨P, hvP.ne.symm⟩ = γ ∧ c ⟨E, hvE.ne.symm⟩ = γ ∧ E ≠ P ∧
      (∀ a ∈ originalSingletonCenters c, G.Adj P a) ∧
      (∀ (p : V) (hvp : G.Adj v p), c ⟨p, hvp.ne.symm⟩ = γ → p ≠ P →
        ∀ a ∈ originalSingletonCenters c, ¬G.Adj p a) := by
  classical
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (originalSingletonCenters c).card)
  obtain ⟨P, hvP, hPγ, hPb⟩ :=
    equality_original_nonsingleton_color_touches_each_center hk hcrit hcount c hcard γ hγ hb
  have hPfull : ∀ a ∈ originalSingletonCenters c, G.Adj P a := by
    intro a ha
    by_cases hab : a = b
    · simpa only [hab] using hPb
    obtain ⟨p, hvp, hpγ, hpa⟩ :=
      equality_original_nonsingleton_color_touches_each_center hk hcrit hcount c hcard γ hγ ha
    by_cases hpP : p = P
    · simpa only [hpP] using hpa
    have hba := equality_original_duplicate_fiber_hooks_agree hk hcrit hcount hvP hvp
      (fun he => hpP he.symm) c (hPγ.trans hpγ.symm) hcard hb ha hPb hpa
    exact False.elim (hab hba.symm)
  have hother : ∀ (p : V) (hvp : G.Adj v p), c ⟨p, hvp.ne.symm⟩ = γ → p ≠ P →
      ∀ a ∈ originalSingletonCenters c, ¬G.Adj p a := by
    intro p hvp hpγ hpP a ha hpa
    obtain ⟨b', hb', hba⟩ :=
      Finset.exists_mem_ne (by omega : 1 < (originalSingletonCenters c).card) a
    have he := equality_original_duplicate_fiber_hooks_agree hk hcrit hcount hvP hvp
      (fun he => hpP he.symm) c (hPγ.trans hpγ.symm) hcard hb' ha (hPfull b' hb') hpa
    exact hba he
  have hE : ∃ (E : V) (hvE : G.Adj v E), c ⟨E, hvE.ne.symm⟩ = γ ∧ E ≠ P := by
    by_contra hn
    have huniq : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
        c ⟨z, hzv⟩ = c ⟨P, hvP.ne.symm⟩ → z = P := by
      intro z hzv hvz hc
      by_contra hzP
      exact hn ⟨z, hvz, hc.trans hPγ, hzP⟩
    have hPJ : P ∈ originalSingletonCenters c :=
      (mem_originalSingletonCenters c).mpr ⟨hvP, huniq⟩
    apply hγ
    rw [← hPγ]
    exact original_singleton_color_mem_palette c hPJ hvP.ne.symm
  obtain ⟨E, hvE, hEγ, hEP⟩ := hE
  exact ⟨P, E, hvP, hvE, hPγ, hEγ, hEP, hPfull, hother⟩

end TaskH.General

#print axioms TaskH.General.equality_original_nonsingleton_color_touches_each_center
#print axioms TaskH.General.equality_original_nonsingleton_full_empty
