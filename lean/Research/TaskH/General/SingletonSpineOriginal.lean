import Research.TaskH.General.ThreeSingletonTailOriginal
import Research.TaskH.General.SingletonCenterCarrierOriginal
import Research.TaskH.Gao.CliquePaths

/-! A genuine singleton spine uses exactly one ordered donor. Its tail is
spliced into the first edge of a real finite-clique path, so no simultaneous
donor-disjointness assumption or path-existence oracle is introduced. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k s : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_singleton_spine (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcard : 3 ≤ (originalSingletonCenters c).card)
    (K : Finset V) (hK : K ⊆ originalSingletonCenters c)
    (hKtwo : 2 ≤ K.card) (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (hsk : s + 3 ≤ k) (D : Fin s → Fin k) (hD : Function.Injective D)
    (hDJ : ∀ i (z : V) (_hzJ : z ∈ originalSingletonCenters c) (hzv : z ≠ v),
      D i ≠ c ⟨z, hzv⟩) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.length = K.card + s - 1 ∧ v ∉ p.support ∧
      (∀ z ∈ p.support, z ∈ K ∨
        ∃ (hzv : z ≠ v) (i : Fin s), c ⟨z, hzv⟩ = D i) := by
  classical
  have hclique : G.IsClique (K : Set V) := by
    intro z hz w hw hzw
    exact equality_original_singleton_centers_clique hk hcrit hcount c hcard
      (hK hz) (hK hw) hzw
  obtain ⟨p₀, hp₀, hlen₀, hsupp₀⟩ :=
    _root_.TaskH.Gao.finset_clique_path_exact (K.card - 1) K a b hclique
      ha hb hab (by omega) (by omega)
  obtain ⟨w, e, r, rfl⟩ := Walk.exists_eq_cons_of_ne hab p₀
  have hr : r.IsPath := hp₀.of_cons
  have har : a ∉ r.support := (Walk.cons_isPath_iff e r).mp hp₀ |>.2
  have hwK : w ∈ K := hsupp₀ w (List.mem_cons_of_mem _ r.start_mem_support)
  have hsuppR : ∀ z ∈ r.support, z ∈ K := by
    intro z hz
    exact hsupp₀ z (List.mem_cons_of_mem _ hz)
  obtain ⟨h, hhJ, hha, hhw⟩ := original_singleton_third_exists c hcard (a := a) (b := w)
  obtain ⟨hva, hau⟩ := (mem_originalSingletonCenters c).mp (hK ha)
  obtain ⟨hvw, hwu⟩ := (mem_originalSingletonCenters c).mp (hK hwK)
  obtain ⟨hvh, hhu⟩ := (mem_originalSingletonCenters c).mp hhJ
  obtain ⟨q, hq, hqlen, hvq, _, _, hqcolors⟩ :=
    equality_original_three_singleton_tail hk hcrit hcount hva hvw hvh c hau hwu hhu
      (original_singleton_centers_color_ne c (hK ha) (hK hwK) e.ne _ _)
      (original_singleton_centers_color_ne c (hK ha) hhJ hha.symm _ _)
      (original_singleton_centers_color_ne c (hK hwK) hhJ hhw.symm _ _)
      hsk D hD
      (fun i => hDJ i a (hK ha) hva.ne.symm)
      (fun i => hDJ i w (hK hwK) hvw.ne.symm)
      (fun i => hDJ i h hhJ hvh.ne.symm)
  have hint : ∀ z : V, z ∈ q.support → z ∈ r.support → z = w := by
    intro z hzq hzr
    by_contra hzw
    have hza : z ≠ a := by intro he; subst z; exact har hzr
    have hzv : z ≠ v := by intro he; subst z; exact hvq hzq
    obtain ⟨i, hc⟩ := hqcolors z hzv hzq hza hzw
    exact hDJ i z (hK (hsuppR z hzr)) hzv hc.symm
  have hp : (q.append r).IsPath :=
    _root_.TaskH.Fan.isPath_append_of_support_intersection q r hq hr hint
  refine ⟨q.append r, hp, ?_, ?_, ?_⟩
  · simp only [Walk.length_cons] at hlen₀
    rw [Walk.length_append, hqlen]
    omega
  · intro hv
    rcases (Walk.mem_support_append_iff q r).mp hv with hv | hv
    · exact hvq hv
    · exact original_singleton_center_ne_root c (hK (hsuppR v hv)) rfl
  · intro z hz
    rcases (Walk.mem_support_append_iff q r).mp hz with hzq | hzr
    · by_cases hza : z = a
      · exact Or.inl (by simpa only [hza] using ha)
      by_cases hzw : z = w
      · exact Or.inl (by simpa only [hzw] using hwK)
      have hzv : z ≠ v := by intro he; subst z; exact hvq hzq
      obtain ⟨i, hc⟩ := hqcolors z hzv hzq hza hzw
      exact Or.inr ⟨hzv, i, hc⟩
    · exact Or.inl (hsuppR z hzr)

end TaskH.General

#print axioms TaskH.General.equality_original_singleton_spine
