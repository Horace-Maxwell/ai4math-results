import Research.TaskV.Stanley.StarCore
import Research.TaskV.Stanley.StarProfiles
import Research.TaskV.Stanley.AnchorCuts
import Research.TaskV.Stanley.AnchorSides

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

variable {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}

@[simp] theorem expandedCoreSet_compl (hG : G.Connected) (hc : (core G).Nonempty)
    (s : Finset ↥(core G)) : expandedCoreSet hG hc sᶜ = (expandedCoreSet hG hc s)ᶜ := by
  classical ext x; simp

theorem expanded_cut (hG : G.Connected) (hc : (core G).Nonempty)
    (s : Finset ↥(core G)) :
    connectedCut G (expandedCoreSet hG hc s) ↔ connectedCut (coreGraph G) s := by
  classical
  unfold connectedCut
  rw [connected_of_centers,← coe_compl,← expandedCoreSet_compl,connected_of_centers,coe_compl]
  exact Iff.rfl

theorem component_weight_lower (h : ∀ c ∈ core G, 2 ≤ coreWeight G c)
    {s : Finset ↥(core G)} (hsc : ((coreGraph G).induce (s : Set ↥(core G))).Connected) :
    2 ≤ ∑ c ∈ s, coreWeight G c := by
  classical
  obtain ⟨a⟩ := hsc.nonempty
  exact (h _ a.val.property).trans (single_le_sum (fun (b : ↥(core G)) _ => Nat.zero_le (coreWeight G b)) a.property)

theorem cut_is_expanded (hG : G.Connected) (hc : (core G).Nonempty)
    (s : Finset (Fin n)) (hs : connectedCut G s) (sa : 2 ≤ s.card) (so : 2 ≤ n-s.card) :
    ∃ t : Finset ↥(core G), expandedCoreSet hG hc t = s := by
  classical
  let f := cutCode s
  have z : {x : Fin n | f x = 0} = (s : Set (Fin n)) := by ext; simp [f]
  have o : {x : Fin n | f x = 1} = (s : Set (Fin n))ᶜ := by ext; simp [f]
  have fz : fiberSet f 0 = s := by ext; simp [f]
  have fo : fiberSet f 1 = sᶜ := by ext; simp [f]
  have sz (c : Fin 2) : 2 ≤ Nat.card {i : Fin n // f i = c} := by
    rw [natCard_fiberSet]
    fin_cases c
    · change 2 ≤ (fiberSet f 0).card
      rw [fz]; exact sa
    · simpa [fo,card_compl] using so
  have conn (c : Fin 2) : (G.induce {i : Fin n | f i = c}).Connected := by
    fin_cases c
    · change (G.induce {i : Fin n | f i = 0}).Connected
      rw [z]; exact hs.1
    · change (G.induce {i : Fin n | f i = 1}).Connected
      rw [o]; exact hs.2
  refine ⟨univ.filter (fun c : ↥(core G) => c.val ∈ s),?_⟩
  ext i
  simp only [mem_expandedCoreSet,mem_filter,mem_univ,true_and]
  rw [← cutCode_zero s (starCenter hG hc i), ← cutCode_zero s i]
  change f (starCenter hG hc i) = 0 ↔ f i = 0
  rw [starCenter_agrees_in_fiber hG hc f sz conn i]

theorem matching_core_cut (hG : G.Connected) (hH : H.Connected) (hc : (core G).Nonempty)
    (hd : (core H).Nonempty) (same : SameConnected G H) (size : n = m)
    (properG : ∀ c ∈ core G, 2 ≤ coreWeight G c) (s : Finset ↥(core G))
    (hs : connectedCut (coreGraph G) s) :
    ∃ t : Finset ↥(core H), connectedCut (coreGraph H) t ∧
      (∑ c ∈ t, coreWeight H c) = ∑ c ∈ s, coreWeight G c := by
  classical
  subst m
  let a := expandedCoreSet hG hc s
  have cut : connectedCut G a := (expanded_cut hG hc s).mpr hs
  have sa : 2 ≤ a.card := by
    rw [show a.card = _ from card_expandedCoreSet hG hc s]
    exact component_weight_lower properG hs.1
  have so : 2 ≤ n-a.card := by
    have h := component_weight_lower properG (s:=sᶜ) (connectedCut_compl hs).1
    rw [← card_expandedCoreSet hG hc,expandedCoreSet_compl,card_compl,Fintype.card_fin] at h
    exact h
  have nz : 0 < Nat.card (CutOfSize G a.card) := Nat.card_pos_iff.mpr ⟨⟨⟨a,rfl,cut⟩⟩,inferInstance⟩
  rw [← connectedCoefficient_two,same,connectedCoefficient_two] at nz
  obtain ⟨⟨b,hb,bs,bo⟩⟩ := (Nat.card_pos_iff.mp nz).1
  have cb : connectedCut H b := ⟨bs,bo⟩
  obtain ⟨t,eq⟩ := cut_is_expanded hH hd b cb (hb ▸ sa) (hb ▸ so)
  refine ⟨t,(expanded_cut hH hd t).mp (eq ▸ cb),?_⟩
  rw [← card_expandedCoreSet hH hd,eq,hb]
  exact card_expandedCoreSet hG hc s

end
end StanleyContinuation
