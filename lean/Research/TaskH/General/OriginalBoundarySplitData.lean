import Research.TaskH.General.OriginalBoundaryNoCrossHook

/-! INTERNAL actual split data. The constructor below derives every field
from the original full-critical equality graph and its actual boundary degree.
This structure is never added as a premise of the original-domain result. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open scoped Classical
open SimpleGraph _root_.TaskH.Challenge
variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

structure OriginalBoundarySplitData (v : V)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) where
  a : {z : V // z ≠ v}
  b : {z : V // z ≠ v}
  hva : G.Adj v a.val
  hvb : G.Adj v b.val
  hab : a.val ≠ b.val
  centers : originalSingletonCenters c = {a.val, b.val}
  S : Finset (Fin k)
  sideColors : S = (originalSingletonPalette c)ᶜ
  P : S → {z : V // z ≠ v}
  Q : S → {z : V // z ≠ v}
  rootP : ∀ i, G.Adj v (P i).val
  rootQ : ∀ i, G.Adj v (Q i).val
  colorP : ∀ i, c (P i) = i.val
  colorQ : ∀ i, c (Q i) = i.val
  hookP : ∀ i, G.Adj (P i).val a.val
  hookQ : ∀ i, G.Adj (Q i).val b.val
  notP : ∀ i, ¬G.Adj (P i).val b.val
  notQ : ∀ i, ¬G.Adj (Q i).val a.val
  pair : ∀ i (z : {z : V // z ≠ v}), G.Adj v z.val →
    (c z = i.val ↔ z = P i ∨ z = Q i)
  cross : ∀ i j, ¬G.Adj (P i).val (Q j).val

theorem equality_original_boundary_split_data [DecidableRel G.Adj]
    (hk : 6 ≤ k) (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1)) (v : V) (hv : G.degree v = 2 * k - 2)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) :
    Nonempty (OriginalBoundarySplitData v c) := by
  classical
  obtain ⟨a, b, hab, hcenters, _, hfib⟩ :=
    equality_original_boundary_singletons_and_pairs (by omega) hcrit hcount hnot v hv c
  have ha : a ∈ originalSingletonCenters c := by rw [hcenters]; exact Finset.mem_insert_self _ _
  have hb : b ∈ originalSingletonCenters c := by
    rw [hcenters]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨hva, hau⟩ := (mem_originalSingletonCenters c).mp ha
  obtain ⟨hvb, hbu⟩ := (mem_originalSingletonCenters c).mp hb
  let aD : {z : V // z ≠ v} := ⟨a, hva.ne.symm⟩
  let bD : {z : V // z ≠ v} := ⟨b, hvb.ne.symm⟩
  have hc := original_singleton_centers_color_ne c ha hb hab hva.ne.symm hvb.ne.symm
  let S := (originalSingletonPalette c)ᶜ
  have hca : ∀ i : S, i.val ≠ c aD := by
    intro i he
    apply Finset.mem_compl.mp i.property
    rw [he]
    exact original_singleton_color_mem_palette c ha hva.ne.symm
  have hcb : ∀ i : S, i.val ≠ c bD := by
    intro i he
    apply Finset.mem_compl.mp i.property
    rw [he]
    exact original_singleton_color_mem_palette c hb hvb.ne.symm
  have hchooseP : ∀ i : S, ∃ z : {z : V // z ≠ v},
      G.Adj v z.val ∧ c z = i.val ∧ G.Adj z.val a := by
    intro i
    obtain ⟨z, hzv, hvz, hzc, hza⟩ := equality_original_singleton_color_fiber_touches
      (by omega) hcrit hcount hvb hva c hbu hau hc.symm i.val (hcb i) (hca i)
    exact ⟨⟨z, hzv⟩, hvz, hzc, hza⟩
  have hchooseQ : ∀ i : S, ∃ z : {z : V // z ≠ v},
      G.Adj v z.val ∧ c z = i.val ∧ G.Adj z.val b := by
    intro i
    obtain ⟨z, hzv, hvz, hzc, hzb⟩ := equality_original_singleton_color_fiber_touches
      (by omega) hcrit hcount hva hvb c hau hbu hc i.val (hca i) (hcb i)
    exact ⟨⟨z, hzv⟩, hvz, hzc, hzb⟩
  choose P hrootP hcolorP hhookP using hchooseP
  choose Q hrootQ hcolorQ hhookQ using hchooseQ
  have hnotP : ∀ i, ¬G.Adj (P i).val b := by
    intro i hi
    exact equality_original_boundary_no_common_hook hk hcrit hcount hnot v hv c hab hcenters
      (hrootP i) (hhookP i) hi
  have hnotQ : ∀ i, ¬G.Adj (Q i).val a := by
    intro i hi
    exact equality_original_boundary_no_common_hook hk hcrit hcount hnot v hv c hab hcenters
      (hrootQ i) hi (hhookQ i)
  have hpq : ∀ i, P i ≠ Q i := by
    intro i he
    exact hnotQ i (by simpa only [← he] using hhookP i)
  have hpair : ∀ i (z : {z : V // z ≠ v}), G.Adj v z.val →
      (c z = i.val ↔ z = P i ∨ z = Q i) := by
    intro i z hvz
    let F := Finset.univ.filter (fun w : G.neighborSet v => _root_.TaskH.neighborColor v c w = i.val)
    let pN : G.neighborSet v := ⟨(P i).val, hrootP i⟩
    let qN : G.neighborSet v := ⟨(Q i).val, hrootQ i⟩
    have hpf : pN ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcolorP i⟩
    have hqf : qN ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcolorQ i⟩
    have hpqn : pN ≠ qN := fun he => hpq i (Subtype.ext (congrArg (fun w : G.neighborSet v => (w : V)) he))
    have hcard : F.card = 2 := hfib i.val (Finset.mem_compl.mp i.property)
    have hset : ({pN, qN} : Finset (G.neighborSet v)) = F := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hpf
        · have he : w = qN := Finset.mem_singleton.mp hw
          simpa only [he] using hqf
      · rw [Finset.card_pair hpqn, hcard]
    constructor
    · intro hzc
      have hm : (⟨z.val, hvz⟩ : G.neighborSet v) ∈ F :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzc⟩
      rw [← hset, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with he | he
      · exact Or.inl (Subtype.ext (congrArg (fun w : G.neighborSet v => (w : V)) he))
      · exact Or.inr (Subtype.ext (congrArg (fun w : G.neighborSet v => (w : V)) he))
    · rintro (rfl | rfl)
      · exact hcolorP i
      · exact hcolorQ i
  have hcross : ∀ i j, ¬G.Adj (P i).val (Q j).val := by
    intro i j
    apply equality_original_boundary_no_cross_hook hk hcrit hcount hnot v hv c hab hcenters
      (hrootP i) (hrootQ j) (hhookP i) (hhookQ j)
    · change c (P i) ∉ originalSingletonPalette c
      rw [hcolorP i]
      exact Finset.mem_compl.mp i.property
    · change c (Q j) ∉ originalSingletonPalette c
      rw [hcolorQ j]
      exact Finset.mem_compl.mp j.property
  exact ⟨
    { a := aD
      b := bD
      hva := hva
      hvb := hvb
      hab := hab
      centers := hcenters
      S := S
      sideColors := rfl
      P := P
      Q := Q
      rootP := hrootP
      rootQ := hrootQ
      colorP := hcolorP
      colorQ := hcolorQ
      hookP := hhookP
      hookQ := hhookQ
      notP := hnotP
      notQ := hnotQ
      pair := hpair
      cross := hcross }⟩

end TaskH.General
#print axioms TaskH.General.OriginalBoundarySplitData
#print axioms TaskH.General.equality_original_boundary_split_data
