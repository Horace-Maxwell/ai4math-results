import Research.TaskH.General.OriginalBoundarySplitData
import Research.TaskH.General.OriginalKempeSingletonCoverage

/-! A real missing edge on EACH side gives two locked rows on that side.
The old split is derived separately in the original graph; Kempe coverage is
applied only to the actual recoloring, without assuming a new split. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open scoped Classical
open SimpleGraph _root_.TaskH.Challenge
variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem OriginalBoundarySplitData.unique_a {v : V}
    {c : (G.induce {z | z ≠ v}).Coloring (Fin k)} (D : OriginalBoundarySplitData v c) :
    ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c D.a → z = D.a.val := by
  have ha : D.a.val ∈ originalSingletonCenters c := by
    rw [D.centers]
    exact Finset.mem_insert_self _ _
  exact ((mem_originalSingletonCenters c).mp ha).2

theorem OriginalBoundarySplitData.unique_b {v : V}
    {c : (G.induce {z | z ≠ v}).Coloring (Fin k)} (D : OriginalBoundarySplitData v c) :
    ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c D.b → z = D.b.val := by
  have hb : D.b.val ∈ originalSingletonCenters c := by
    rw [D.centers]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact ((mem_originalSingletonCenters c).mp hb).2

theorem OriginalBoundarySplitData.color_ne {v : V}
    {c : (G.induce {z | z ≠ v}).Coloring (Fin k)} (D : OriginalBoundarySplitData v c) :
    c D.a ≠ c D.b := by
  intro he
  exact D.hab (D.unique_a D.b.val D.b.property D.hvb he.symm).symm

theorem OriginalBoundarySplitData.side_color_ne {v : V}
    {c : (G.induce {z | z ≠ v}).Coloring (Fin k)} (D : OriginalBoundarySplitData v c)
    (i : D.S) : i.val ≠ c D.a ∧ i.val ≠ c D.b := by
  have hm : i.val ∉ originalSingletonPalette c := by
    apply Finset.mem_compl.mp
    rw [← D.sideColors]
    exact i.property
  rw [original_two_center_palette c D.centers D.a.property D.b.property] at hm
  exact not_or.mp hm

def OriginalBoundarySplitData.reversed {v : V}
    {c : (G.induce {z | z ≠ v}).Coloring (Fin k)} (D : OriginalBoundarySplitData v c) :
    OriginalBoundarySplitData v c where
  a := D.b
  b := D.a
  hva := D.hvb
  hvb := D.hva
  hab := D.hab.symm
  centers := D.centers.trans (Finset.pair_comm _ _)
  S := D.S
  sideColors := D.sideColors
  P := D.Q
  Q := D.P
  rootP := D.rootQ
  rootQ := D.rootP
  colorP := D.colorQ
  colorQ := D.colorP
  hookP := D.hookQ
  hookQ := D.hookP
  notP := D.notQ
  notQ := D.notP
  pair := fun i z hz => (D.pair i z hz).trans or_comm
  cross := fun i j h => D.cross j i h.symm

theorem OriginalBoundarySplitData.side_has_missing_edge [DecidableRel G.Adj]
    (hk : 6 ≤ k) (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1)) {v : V} (hv : G.degree v = 2 * k - 2)
    {c : (G.induce {z | z ≠ v}).Coloring (Fin k)} (D : OriginalBoundarySplitData v c) :
    ∃ i j : D.S, i ≠ j ∧ ¬G.Adj (D.P i).val (D.P j).val := by
  classical
  by_contra hn
  have hall : ∀ i j : D.S, i ≠ j → G.Adj (D.P i).val (D.P j).val := by
    intro i j hij
    by_contra he
    exact hn ⟨i, j, hij, he⟩
  let f : D.S → V := fun i => (D.P i).val
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    exact (D.colorP i).symm.trans ((congrArg c (Subtype.ext he)).trans (D.colorP j))
  let T := Finset.univ.image f
  have haT : D.a.val ∉ T := by
    rintro hh
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hh
    exact (D.side_color_ne i).1 ((D.colorP i).symm.trans (congrArg c (Subtype.ext hi)))
  have hvT : v ∉ T := by
    rintro hh
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hh
    exact (D.rootP i).ne hi.symm
  have hpal : (originalSingletonPalette c).card = 2 := by
    rw [original_singleton_palette_card, D.centers, Finset.card_pair D.hab]
  have hScard : D.S.card + 2 = k := by
    have hh := Finset.card_add_card_compl (originalSingletonPalette c)
    rw [hpal, ← D.sideColors, Fintype.card_fin] at hh
    omega
  have hTcard : T.card = D.S.card := by
    change (Finset.univ.image f).card = D.S.card
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_coe]
  let Q := insert v (insert D.a.val T)
  have hvAT : v ∉ insert D.a.val T := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨D.a.property.symm, hvT⟩
  have hQcard : Q.card = k := by
    change (insert v (insert D.a.val T)).card = k
    rw [Finset.card_insert_of_notMem hvAT, Finset.card_insert_of_notMem haT, hTcard]
    omega
  have hQ : G.IsClique (Q : Set V) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact False.elim (hxy rfl)
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact D.hva
        · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
          exact D.rootP i
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact D.hva.symm
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact False.elim (hxy rfl)
          · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
            exact (D.hookP i).symm
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact (D.rootP i).symm
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact D.hookP i
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
            exact hall i j (fun he => hxy (congrArg f he))
  exact equality_original_boundary_no_k_clique hk hcrit hcount hnot v hv Q hQ hQcard

theorem OriginalBoundarySplitData.unlocked_universal (hk : 6 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} {c : (G.induce {z | z ≠ v}).Coloring (Fin k)} (D : OriginalBoundarySplitData v c)
    (i j : D.S) (hji : j ≠ i)
    (hout : D.Q i ∉ _root_.TaskH.Seven.twoColorComponent c (c D.a) (c (D.P i)) D.a) :
    G.Adj (D.P i).val (D.P j).val := by
  have hjiColor : c (D.P j) ≠ c (D.P i) := by
    rw [D.colorP j, D.colorP i]
    exact fun he => hji (Subtype.ext he)
  apply equality_original_unlocked_row_meets_same_side (by omega) hcrit hcount
    c D.a D.b (D.P i) (D.Q i) (D.P j) (D.Q j) D.hvb (D.rootP i)
    (D.hookP i).symm D.unique_a D.unique_b D.color_ne
    (by rw [D.colorP i]; exact (D.side_color_ne i).2)
    (by rw [D.colorP j]; exact (D.side_color_ne j).1)
    (by rw [D.colorP j]; exact (D.side_color_ne j).2) hjiColor
    (fun z hz => by simpa only [D.colorP i] using D.pair i z hz)
    (fun z hz => by simpa only [D.colorP j] using D.pair j z hz) (D.cross i j) hout

theorem OriginalBoundarySplitData.two_locked_rows [DecidableRel G.Adj]
    (hk : 6 ≤ k) (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1)) {v : V} (hv : G.degree v = 2 * k - 2)
    {c : (G.induce {z | z ≠ v}).Coloring (Fin k)} (D : OriginalBoundarySplitData v c) :
    ∃ i j : D.S, i ≠ j ∧
      D.Q i ∈ _root_.TaskH.Seven.twoColorComponent c (c D.a) (c (D.P i)) D.a ∧
      D.Q j ∈ _root_.TaskH.Seven.twoColorComponent c (c D.a) (c (D.P j)) D.a := by
  classical
  obtain ⟨i, j, hij, hmissing⟩ := D.side_has_missing_edge hk hcrit hcount hnot hv
  refine ⟨i, j, hij, ?_, ?_⟩
  · by_contra hout
    exact hmissing (D.unlocked_universal hk hcrit hcount i j hij.symm hout)
  · by_contra hout
    exact hmissing (D.unlocked_universal hk hcrit hcount j i hij hout).symm

end TaskH.General
#print axioms TaskH.General.OriginalBoundarySplitData.unique_a
#print axioms TaskH.General.OriginalBoundarySplitData.unique_b
#print axioms TaskH.General.OriginalBoundarySplitData.color_ne
#print axioms TaskH.General.OriginalBoundarySplitData.side_color_ne
#print axioms TaskH.General.OriginalBoundarySplitData.reversed
#print axioms TaskH.General.OriginalBoundarySplitData.side_has_missing_edge
#print axioms TaskH.General.OriginalBoundarySplitData.unlocked_universal
#print axioms TaskH.General.OriginalBoundarySplitData.two_locked_rows
