import Research.TaskV.Stanley.StarBasics
import Mathlib.Data.Fintype.EquivFin

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

theorem starCenter_connected {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hc : (core G).Nonempty) (c : ↥(core G)) :
    (G.induce {x : Fin n | starCenter hG hc x = c}).Connected := by
  let center : {x : Fin n // starCenter hG hc x = c} := ⟨c,starCenter_core hG hc c⟩
  have reach (i : {x : Fin n // starCenter hG hc x = c}) :
      (G.induce {x : Fin n | starCenter hG hc x = c}).Reachable i center := by
    rcases (starCenter_iff hG hc i c).mp i.property with h | h
    · have : i = center := Subtype.ext h
      rw [this]
    · exact SimpleGraph.Adj.reachable (show (G.induce _).Adj i center from h.2)
  exact (SimpleGraph.connected_iff _).mpr ⟨fun i j => (reach i).trans (reach j).symm,⟨center⟩⟩

theorem starCenter_agrees_in_fiber {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.Connected) (hc : (core G).Nonempty) (f : Fin n → Fin k)
    (hsize : ∀ c, 2 ≤ Nat.card {i : Fin n // f i = c})
    (hconn : ∀ c, (G.induce {i : Fin n | f i = c}).Connected)
    (x : Fin n) : f (starCenter hG hc x) = f x := by
  classical
  by_cases h : x ∈ core G
  · exact congrArg (fun q : ↥(core G) => f q.val) (starCenter_core hG hc ⟨x,h⟩)
  let c := f x
  let s := {i : Fin n | f i = c}
  have sz : 1 < Fintype.card s := by
    rw [← Nat.card_eq_fintype_card]
    exact hsize c
  let : Nontrivial s := Fintype.one_lt_card_iff_nontrivial.mp sz
  obtain ⟨y,hy⟩ := (hconn c).preconnected.exists_adj_of_nontrivial (⟨x,rfl⟩ : s)
  have hxy : G.Adj x y := hy
  rw [starCenter_leaf_eq hG hc h hxy]
  exact y.property

def coreLabels {n : ℕ} (G : SimpleGraph (Fin n)) : ↥(core G) ≃ Fin (core G).card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe _)

theorem get_matching_profiles {n m k : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (heq : SameConnected G H) (sizes : Fin k → ℕ) (f : Fin n → Fin k)
    (hsize : ∀ c, Nat.card {i : Fin n // f i = c} = sizes c)
    (hconn : ∀ c, (G.induce {i : Fin n | f i = c}).Connected) :
    ∃ g : Fin m → Fin k,
      (∀ c, Nat.card {i : Fin m // g i = c} = sizes c) ∧
      ∀ c, (H.induce {i : Fin m | g i = c}).Connected := by
  classical
  have hp : 0 < connectedCoefficient G k sizes :=
    Nat.card_pos_iff.mpr ⟨⟨⟨f,hsize,hconn⟩⟩,inferInstance⟩
  rw [heq k sizes] at hp
  obtain ⟨⟨g,hg⟩⟩ := (Nat.card_pos_iff.mp hp).1
  exact ⟨g,hg⟩

theorem weightPreservingCoreEquiv {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (hG : G.Connected) (hH : H.Connected) (heq : SameConnected G H)
    (hcG : (core G).Nonempty) (hcH : (core H).Nonempty)
    (he : (core G).card = (core H).card)
    (hproper : ∀ c ∈ core G, 2 ≤ coreWeight G c) :
    ∃ e : ↥(core G) ≃ ↥(core H), ∀ c : ↥(core G), coreWeight H (e c) = coreWeight G c := by
  classical
  let e := coreLabels G
  let f := fun x => e (starCenter hG hcG x)
  let sizes := fun c => coreWeight G (e.symm c)
  have ef (i : Fin (core G).card) (x : Fin n) : f x = i ↔ starCenter hG hcG x = e.symm i :=
    e.eq_symm_apply.symm
  have hf (i : Fin (core G).card) :
      {x : Fin n | f x = i} = {x : Fin n | starCenter hG hcG x = e.symm i} :=
    Set.ext fun x => ef i x
  obtain ⟨g,hgs,hgc⟩ := get_matching_profiles heq sizes f
    (fun c => by
      change Nat.card ↑{x : Fin n | f x = c} = _
      rw [hf]
      exact starCenter_fiber_card hG hcG (e.symm c))
    (fun c => by rw [hf]; exact starCenter_connected hG hcG _)
  have gs (c : Fin (core G).card) : 2 ≤ Nat.card {x : Fin m // g x = c} :=
    hgs c ▸ hproper _ (e.symm c).property
  have hh := starCenter_agrees_in_fiber hH hcH g gs hgc
  let h := fun c : ↥(core H) => g c.val
  have surj : Function.Surjective h := by
    intro c
    obtain ⟨x⟩ := (hgc c).nonempty
    exact ⟨starCenter hH hcH x, (hh x).trans x.property⟩
  have bij : Function.Bijective h :=
    (Fintype.bijective_iff_surjective_and_card h).mpr ⟨surj,by simpa only [Fintype.card_coe, Fintype.card_fin] using he.symm⟩
  let d := Equiv.ofBijective h bij
  refine ⟨e.trans d.symm,?_⟩
  intro c
  let k := e c
  have hsf : {x : Fin m | g x = k} =
      {x : Fin m | starCenter hH hcH x = d.symm k} := by
    ext x
    change g x = k ↔ _
    rw [← hh x]
    exact d.eq_symm_apply.symm
  have hg := hgs k
  change Nat.card ↑{x : Fin m | g x = k} = _ at hg
  rw [hsf] at hg
  have hm := (starCenter_fiber_card hH hcH (d.symm k)).symm.trans hg
  simpa [k,sizes] using hm

end
end StanleyContinuation
