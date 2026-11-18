import Research.TaskH.General.SingletonFullEmptyOriginal
import Research.TaskH.General.ShortSpokeSupportOriginal

/-! Two real six-cycles with actual singleton spokes force the two internal
points of the length-three donor to be the already derived FULL points.
This auxiliary step uses k>=6; it does not silently extend to k=5. -/

set_option autoImplicit false

universe u

namespace TaskH.General
open scoped Classical

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_common_hook_propagation (hk : 6 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b P T : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (ha : a ∈ originalSingletonCenters c) (hb : b ∈ originalSingletonCenters c)
    (hab : a ≠ b) (γ δ : Fin k) (hγδ : γ ≠ δ)
    (hγ : γ ∉ originalSingletonPalette c) (hδ : δ ∉ originalSingletonPalette c)
    (hvP : G.Adj v P) (hvT : G.Adj v T)
    (hPγ : c ⟨P, hvP.ne.symm⟩ = γ) (hTδ : c ⟨T, hvT.ne.symm⟩ = δ)
    (hPa : G.Adj P a) (hPb : G.Adj P b)
    (hTa : G.Adj T a) : G.Adj P T ∧ G.Adj T b := by
  classical
  obtain ⟨hva, hau⟩ := (mem_originalSingletonCenters c).mp ha
  obtain ⟨hvb, hbu⟩ := (mem_originalSingletonCenters c).mp hb
  have hcolab := original_singleton_centers_color_ne c ha hb hab hva.ne.symm hvb.ne.symm
  have hγa : γ ≠ c ⟨a, hva.ne.symm⟩ := by
    intro he; apply hγ; rw [he]
    exact original_singleton_color_mem_palette c ha hva.ne.symm
  have hγb : γ ≠ c ⟨b, hvb.ne.symm⟩ := by
    intro he; apply hγ; rw [he]
    exact original_singleton_color_mem_palette c hb hvb.ne.symm
  have hδa : δ ≠ c ⟨a, hva.ne.symm⟩ := by
    intro he; apply hδ; rw [he]
    exact original_singleton_color_mem_palette c ha hva.ne.symm
  have hδb : δ ≠ c ⟨b, hvb.ne.symm⟩ := by
    intro he; apply hδ; rw [he]
    exact original_singleton_color_mem_palette c hb hvb.ne.symm
  let D : Fin 2 → Fin k := Fin.cons γ (fun _ : Fin 1 => δ)
  have hD : Function.Injective D := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [D]
  have hDa : ∀ i, D i ≠ c ⟨a, hva.ne.symm⟩ := by
    intro i; fin_cases i
    · simpa [D] using hγa
    · simpa [D] using hδa
  have hDb : ∀ i, D i ≠ c ⟨b, hvb.ne.symm⟩ := by
    intro i; fin_cases i
    · simpa [D] using hγb
    · simpa [D] using hδb
  obtain ⟨d, hd, hdlen, _, hword, _⟩ := equality_original_ordered_singleton_donor
    (by omega) hcrit hcount hva hvb c hau hbu hcolab (by omega) D hD hDa hDb
  obtain ⟨p, evp, q, rfl⟩ := Walk.exists_eq_cons_of_ne hvb.ne d
  obtain ⟨_, hc0⟩ := hword 0
  have hpγ : c ⟨p, evp.ne.symm⟩ = γ := by simpa [D] using hc0
  have hpb : p ≠ b := by
    intro he
    apply hγb
    exact hpγ.symm.trans (congrArg c (Subtype.ext he))
  obtain ⟨z, epz, r, rfl⟩ := Walk.exists_eq_cons_of_ne hpb q
  obtain ⟨hzv0, hc1⟩ := hword 1
  have hzv : z ≠ v := by simpa using hzv0
  have hzδ : c ⟨z, hzv⟩ = δ := by simpa [D] using hc1
  have hrl : r.length = 1 := by
    simp only [Walk.length_cons] at hdlen
    omega
  have ezb : G.Adj z b := Walk.adj_of_length_eq_one hrl
  have color_ne : ∀ {x y : V} (hx : x ≠ v) (hy : y ≠ v),
      c ⟨x, hx⟩ ≠ c ⟨y, hy⟩ → x ≠ y := by
    intro x y hx hy hxy he
    exact hxy (congrArg c (Subtype.ext he))
  have haP : a ≠ P := color_ne hva.ne.symm hvP.ne.symm (by rw [hPγ]; exact hγa.symm)
  have haz : a ≠ z := color_ne hva.ne.symm hzv (by rw [hzδ]; exact hδa.symm)
  have hap : a ≠ p := color_ne hva.ne.symm evp.ne.symm (by rw [hpγ]; exact hγa.symm)
  have hPb_ne : P ≠ b := color_ne hvP.ne.symm hvb.ne.symm (by rw [hPγ]; exact hγb)
  have hPz : P ≠ z := color_ne hvP.ne.symm hzv (by rw [hPγ, hzδ]; exact hγδ)
  have hbz : b ≠ z := color_ne hvb.ne.symm hzv (by rw [hzδ]; exact hδb.symm)
  have hbp : b ≠ p := color_ne hvb.ne.symm evp.ne.symm (by rw [hpγ]; exact hγb.symm)
  have hzp : z ≠ p := color_ne hzv evp.ne.symm (by rw [hzδ, hpγ]; exact hγδ.symm)
  have hpP : p = P := by
    by_contra hne
    let Q : G.Walk a v := Walk.cons hPa.symm
      (Walk.cons hPb (Walk.cons ezb.symm (Walk.cons epz.symm evp.symm.toWalk)))
    have hQ : Q.IsPath := by
      apply Walk.IsPath.mk'
      change [a, P, b, z, p, v].Nodup
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        List.nodup_nil, not_or, or_false, and_true]
      exact ⟨⟨haP, hab, haz, hap, hva.ne.symm⟩,
        ⟨⟨hPb_ne, hPz, fun he => hne he.symm, hvP.ne.symm⟩,
          ⟨⟨hbz, hbp, hvb.ne.symm⟩, ⟨⟨hzp, hzv⟩, ⟨evp.ne.symm, fun hfalse => hfalse⟩⟩⟩⟩⟩
    have hQlen : Q.length = 5 := by simp [Q]
    have hPP : P ∈ Q.support := by simp [Q, Walk.support_cons]
    have hpQ : p ∈ Q.support := by simp [Q, Walk.support_cons]
    have he := equality_original_short_spoke_support_rainbow (by omega) hcrit hcount
      hvb hva c hbu hau hcolab.symm Q hQ (by omega) (by omega)
      hPP hpQ hvP.ne.symm evp.ne.symm (hPγ.trans hpγ.symm)
    exact hne he.symm
  subst p
  have hbT : b ≠ T := color_ne hvb.ne.symm hvT.ne.symm (by rw [hTδ]; exact hδb.symm)
  have haT : a ≠ T := color_ne hva.ne.symm hvT.ne.symm (by rw [hTδ]; exact hδa.symm)
  have hPT : P ≠ T := color_ne hvP.ne.symm hvT.ne.symm (by rw [hPγ, hTδ]; exact hγδ)
  have hzT : z = T := by
    by_contra hne
    let Q : G.Walk b v := Walk.cons ezb.symm
      (Walk.cons epz.symm (Walk.cons hPa (Walk.cons hTa.symm hvT.symm.toWalk)))
    have hQ : Q.IsPath := by
      apply Walk.IsPath.mk'
      change [b, z, P, a, T, v].Nodup
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        List.nodup_nil, not_or, or_false, and_true]
      exact ⟨⟨hbz, hPb_ne.symm, hab.symm, hbT, hvb.ne.symm⟩,
        ⟨⟨hPz.symm, haz.symm, hne, hzv⟩,
          ⟨⟨haP.symm, hPT, hvP.ne.symm⟩, ⟨⟨haT, hva.ne.symm⟩, ⟨hvT.ne.symm, fun hfalse => hfalse⟩⟩⟩⟩⟩
    have hQlen : Q.length = 5 := by simp [Q]
    have hzQ : z ∈ Q.support := by simp [Q, Walk.support_cons]
    have hTQ : T ∈ Q.support := by simp [Q, Walk.support_cons]
    have he := equality_original_short_spoke_support_rainbow (by omega) hcrit hcount
      hva hvb c hau hbu hcolab Q hQ (by omega) (by omega)
      hzQ hTQ hzv hvT.ne.symm (hzδ.trans hTδ.symm)
    exact hne he
  exact ⟨by simpa only [hzT] using epz, by simpa only [hzT] using ezb⟩


end TaskH.General
#print axioms TaskH.General.equality_original_common_hook_propagation
