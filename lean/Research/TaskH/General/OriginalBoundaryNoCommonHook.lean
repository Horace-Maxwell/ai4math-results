import Research.TaskH.General.OriginalBoundaryCliqueExclusion
import Research.TaskH.General.OriginalCommonHookPropagation
import Research.TaskH.General.SingletonFullCliqueOriginal

/-! A common hook forces an actual k-clique, contradicted by the internally
derived boundary order budget. All color representatives are actual root
neighbors selected from original donor coverage, with no FULL oracle. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open scoped Classical
open SimpleGraph _root_.TaskH.Challenge
variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem original_two_center_palette {v a b : V}
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hcenters : originalSingletonCenters c = {a, b}) (hav : a ≠ v) (hbv : b ≠ v)
    (γ : Fin k) : γ ∈ originalSingletonPalette c ↔ γ = c ⟨a, hav⟩ ∨ γ = c ⟨b, hbv⟩ := by
  classical
  constructor
  · intro hγ
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hγ
    have hm : (z : V) ∈ ({a, b} : Finset V) :=
      Eq.mp (congrArg (fun J : Finset V => (z : V) ∈ J) hcenters) z.property
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he
    · exact Or.inl (hz.symm.trans (congrArg c (Subtype.ext he)))
    · exact Or.inr (hz.symm.trans (congrArg c (Subtype.ext he)))
  · rintro (rfl | rfl)
    · apply original_singleton_color_mem_palette c _ hav
      rw [hcenters]
      exact Finset.mem_insert_self _ _
    · apply original_singleton_color_mem_palette c _ hbv
      rw [hcenters]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem equality_original_boundary_no_common_hook [DecidableRel G.Adj]
    (hk : 6 ≤ k) (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1)) (v : V) (hv : G.degree v = 2 * k - 2)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) {a b P : V}
    (hab : a ≠ b) (hcenters : originalSingletonCenters c = {a, b})
    (hvP : G.Adj v P) (hPa : G.Adj P a) (hPb : G.Adj P b) : False := by
  classical
  have ha : a ∈ originalSingletonCenters c := by rw [hcenters]; exact Finset.mem_insert_self _ _
  have hb : b ∈ originalSingletonCenters c := by
    rw [hcenters]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨hva, hau⟩ := (mem_originalSingletonCenters c).mp ha
  obtain ⟨hvb, hbu⟩ := (mem_originalSingletonCenters c).mp hb
  let α := c ⟨a, hva.ne.symm⟩
  let β := c ⟨b, hvb.ne.symm⟩
  let γ₀ := c ⟨P, hvP.ne.symm⟩
  have hαβ : α ≠ β := original_singleton_centers_color_ne c ha hb hab _ _
  have hγa : γ₀ ≠ α := c.valid hPa
  have hγb : γ₀ ≠ β := c.valid hPb
  have hγ₀ : γ₀ ∉ originalSingletonPalette c := by
    rw [original_two_center_palette c hcenters hva.ne.symm hvb.ne.symm]
    exact fun hh => hh.elim hγa hγb
  have hrepresentative : ∀ γ : Fin k, γ ≠ α → γ ≠ β →
      ∃ (z : V) (hvz : G.Adj v z), c ⟨z, hvz.ne.symm⟩ = γ ∧ G.Adj z a ∧ G.Adj z b := by
    intro γ hγα hγβ
    by_cases he : γ = γ₀
    · exact ⟨P, hvP, he.symm, hPa, hPb⟩
    have hγ : γ ∉ originalSingletonPalette c := by
      rw [original_two_center_palette c hcenters hva.ne.symm hvb.ne.symm]
      exact fun hh => hh.elim hγα hγβ
    obtain ⟨T, hTv, hvT, hTγ, hTa⟩ := equality_original_singleton_color_fiber_touches
      (by omega) hcrit hcount hvb hva c hbu hau hαβ.symm γ hγβ hγα
    have hmore := equality_original_common_hook_propagation hk hcrit hcount c ha hb hab
      γ₀ γ (fun h => he h.symm) hγ₀ hγ hvP hvT rfl hTγ hPa hPb hTa
    exact ⟨T, hvT, hTγ, hTa, hmore.2⟩
  let I := (Finset.univ : Finset (Fin k)).erase β
  have hchoose : ∀ i : I, ∃ (z : V) (hvz : G.Adj v z),
      c ⟨z, hvz.ne.symm⟩ = i.val ∧ (i.val = α ∨ (G.Adj z a ∧ G.Adj z b)) := by
    intro i
    have hiβ := (Finset.mem_erase.mp i.property).1
    by_cases hiα : i.val = α
    · exact ⟨a, hva, hiα.symm, Or.inl hiα⟩
    obtain ⟨z, hvz, hzc, hza, hzb⟩ := hrepresentative i.val hiα hiβ
    exact ⟨z, hvz, hzc, Or.inr ⟨hza, hzb⟩⟩
  choose f hf hc hshape using hchoose
  have hinj : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    exact (hc i).symm.trans ((congrArg c (Subtype.ext he)).trans (hc j))
  have hcenter : ∀ i : I, i.val = α → f i = a := by
    intro i hi
    exact hau (f i) (hf i).ne.symm (hf i) ((hc i).trans hi)
  have hadj : ∀ i j : I, i ≠ j → G.Adj (f i) (f j) := by
    intro i j hij
    have hijc : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    rcases hshape i with hiα | ⟨hia, hib⟩
    · have hfi := hcenter i hiα
      rcases hshape j with hjα | ⟨hja, _⟩
      · exact False.elim (hijc (hiα.trans hjα.symm))
      · simpa only [hfi] using hja.symm
    · rcases hshape j with hjα | ⟨hja, _⟩
      · have hfj := hcenter j hjα
        simpa only [hfj] using hia
      · have hiJ : i.val ∉ originalSingletonPalette c := by
          rw [original_two_center_palette c hcenters hva.ne.symm hvb.ne.symm]
          intro hh
          rcases hh with he | he
          · exact (c.valid (show (G.induce {z | z ≠ v}).Adj
              ⟨f i, (hf i).ne.symm⟩ ⟨a, hva.ne.symm⟩ from hia)) ((hc i).trans he)
          · exact (Finset.mem_erase.mp i.property).1 he
        have hjJ : j.val ∉ originalSingletonPalette c := by
          rw [original_two_center_palette c hcenters hva.ne.symm hvb.ne.symm]
          intro hh
          rcases hh with he | he
          · exact (c.valid (show (G.induce {z | z ≠ v}).Adj
              ⟨f j, (hf j).ne.symm⟩ ⟨a, hva.ne.symm⟩ from hja)) ((hc j).trans he)
          · exact (Finset.mem_erase.mp j.property).1 he
        exact equality_original_full_points_adjacent_aux hk hcrit hcount c ha hb hab
          i.val j.val hijc hiJ hjJ (hf i) (hf j) (hc i) (hc j) hia hib hja
  let T := Finset.univ.image f
  have hvT : v ∉ T := by
    rintro hh
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hh
    exact (hf i).ne hi.symm
  have hTcard : T.card + 1 = k := by
    change (Finset.univ.image f).card + 1 = k
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
    simpa only [I, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_erase_add_one (Finset.mem_univ β))
  let Q := insert v T
  have hQ : G.IsClique (Q : Set V) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact False.elim (hxy rfl)
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
        exact hf j
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hf i).symm
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
        exact hadj i j (fun he => hxy (congrArg f he))
  have hQcard : Q.card = k := by
    change (insert v T).card = k
    rw [Finset.card_insert_of_notMem hvT]
    exact hTcard
  exact equality_original_boundary_no_k_clique hk hcrit hcount hnot v hv Q hQ hQcard

end TaskH.General
#print axioms TaskH.General.original_two_center_palette
#print axioms TaskH.General.equality_original_boundary_no_common_hook
