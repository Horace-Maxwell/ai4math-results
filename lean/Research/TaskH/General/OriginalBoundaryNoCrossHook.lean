import Research.TaskH.General.OriginalBoundaryNoCommonHook

/-! No cross-hook edge, for ANY two actual non-singleton root fibers.
The real six-edge spoke is constructed in G, not postulated. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open scoped Classical
open SimpleGraph _root_.TaskH.Challenge
variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_boundary_no_cross_hook [DecidableRel G.Adj]
    (hk : 6 ≤ k) (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1)) (v : V) (hv : G.degree v = 2 * k - 2)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) {a b x y : V}
    (hab : a ≠ b) (hcenters : originalSingletonCenters c = {a, b})
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hxa : G.Adj x a) (hyb : G.Adj y b)
    (hxJ : c ⟨x, hvx.ne.symm⟩ ∉ originalSingletonPalette c)
    (hyJ : c ⟨y, hvy.ne.symm⟩ ∉ originalSingletonPalette c) : ¬G.Adj x y := by
  classical
  intro hxy
  have ha : a ∈ originalSingletonCenters c := by rw [hcenters]; exact Finset.mem_insert_self _ _
  have hb : b ∈ originalSingletonCenters c := by
    rw [hcenters]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨hva, hau⟩ := (mem_originalSingletonCenters c).mp ha
  obtain ⟨hvb, hbu⟩ := (mem_originalSingletonCenters c).mp hb
  have hcolab := original_singleton_centers_color_ne c ha hb hab hva.ne.symm hvb.ne.symm
  have hya : c ⟨y, hvy.ne.symm⟩ ≠ c ⟨a, hva.ne.symm⟩ := by
    intro he
    apply hyJ
    rw [he]
    exact original_singleton_color_mem_palette c ha hva.ne.symm
  have hybc : c ⟨y, hvy.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩ := by
    intro he
    apply hyJ
    rw [he]
    exact original_singleton_color_mem_palette c hb hvb.ne.symm
  obtain ⟨T, hTv, hvT, hTy, hTa⟩ := equality_original_singleton_color_fiber_touches
    (by omega) hcrit hcount hvb hva c hbu hau hcolab.symm
    (c ⟨y, hvy.ne.symm⟩) hybc hya
  have hTyne : T ≠ y := by
    intro he
    exact equality_original_boundary_no_common_hook hk hcrit hcount hnot v hv c hab hcenters
      hvy (by simpa only [he] using hTa) hyb
  have hxc : c ⟨x, hvx.ne.symm⟩ ≠ c ⟨y, hvy.ne.symm⟩ := c.valid hxy
  have color_ne : ∀ {p q : V} (hp : p ≠ v) (hq : q ≠ v),
      c ⟨p, hp⟩ ≠ c ⟨q, hq⟩ → p ≠ q := by
    intro p q hp hq hpc he
    exact hpc (congrArg c (Subtype.ext he))
  have hxb : c ⟨x, hvx.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩ := by
    intro he
    apply hxJ
    rw [he]
    exact original_singleton_color_mem_palette c hb hvb.ne.symm
  have hbY : b ≠ y := color_ne hvb.ne.symm hvy.ne.symm hybc.symm
  have hbX : b ≠ x := color_ne hvb.ne.symm hvx.ne.symm hxb.symm
  have hbT : b ≠ T := color_ne hvb.ne.symm hvT.ne.symm (by rw [hTy]; exact hybc.symm)
  have hyX : y ≠ x := hxy.ne.symm
  have hyA : y ≠ a := color_ne hvy.ne.symm hva.ne.symm hya
  have hxT : x ≠ T := color_ne hvx.ne.symm hvT.ne.symm (by rw [hTy]; exact hxc)
  let Q : G.Walk b v := Walk.cons hyb.symm
    (Walk.cons hxy.symm (Walk.cons hxa (Walk.cons hTa.symm hvT.symm.toWalk)))
  have hQ : Q.IsPath := by
    apply Walk.IsPath.mk'
    change [b, y, x, a, T, v].Nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, or_false, and_true]
    exact ⟨⟨hbY, hbX, hab.symm, hbT, hvb.ne.symm⟩,
      ⟨⟨hyX, hyA, hTyne.symm, hvy.ne.symm⟩,
        ⟨⟨hxa.ne, hxT, hvx.ne.symm⟩, ⟨⟨hTa.ne.symm, hva.ne.symm⟩, ⟨hvT.ne.symm, fun hfalse => hfalse⟩⟩⟩⟩⟩
  have hlen : Q.length = 5 := by simp [Q]
  have hyQ : y ∈ Q.support := by simp [Q, Walk.support_cons]
  have hTQ : T ∈ Q.support := by simp [Q, Walk.support_cons]
  have he := equality_original_short_spoke_support_rainbow (by omega) hcrit hcount
    hva hvb c hau hbu hcolab Q hQ (by omega) (by omega)
    hyQ hTQ hvy.ne.symm hvT.ne.symm hTy.symm
  exact hTyne he.symm

end TaskH.General
#print axioms TaskH.General.equality_original_boundary_no_cross_hook
