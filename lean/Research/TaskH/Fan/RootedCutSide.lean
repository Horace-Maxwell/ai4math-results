import Research.TaskH.Fan.RootedCutCover

/-!
Actual x-side of a root-separating cut. The other original root is proved
outside, which supplies both the full nonroot degrees and strict order drop.
The remaining side-augmentation topology is not assumed or asserted here.
-/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

def rootedCutSide (G : SimpleGraph V) (b x : V) (hx : x ≠ b) : Set V :=
  {v | v = b ∨ ∃ hv : v ≠ b,
    (G.induce {a | a ≠ b}).connectedComponentMk ⟨v, hv⟩ =
      (G.induce {a | a ≠ b}).connectedComponentMk ⟨x, hx⟩}

theorem rootedCutSide_closed (G : SimpleGraph V) (b x : V) (hx : x ≠ b) :
    ∀ a ∈ rootedCutSide G b x hx, a ≠ b → ∀ d, G.Adj a d →
      d ∈ rootedCutSide G b x hx := by
  intro a ha hab d hadj
  rcases ha with ha | ⟨_ha, haC⟩
  · exact False.elim (hab ha)
  · by_cases hd : d = b
    · exact Or.inl hd
    · have hc : (G.induce {v | v ≠ b}).connectedComponentMk ⟨a, hab⟩ =
          (G.induce {v | v ≠ b}).connectedComponentMk ⟨d, hd⟩ :=
        ConnectedComponent.connectedComponentMk_eq_of_adj
          (G := G.induce {v | v ≠ b}) (v := ⟨a, hab⟩) (w := ⟨d, hd⟩) hadj
      exact Or.inr ⟨hd, hc.symm.trans haC⟩

theorem rootedCutSide_other_root_not_mem [Fintype V] (G : SimpleGraph V)
    (x y b : V) (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) : y ∉ rootedCutSide G b x hx := by
  intro hyS
  rcases hyS with hyS | ⟨_hy, hyC⟩
  · exact hy hyS
  · exact rooted_cut_roots_distinct G x y b hroot hx hy hbad hyC.symm

theorem rootedCutSide_cover [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b) :
    rootedCutSide G b x hx ∪ rootedCutSide G b y hy = Set.univ := by
  ext v
  constructor
  · exact fun _ => Set.mem_univ v
  · intro _hv
    by_cases hb : v = b
    · exact Or.inl (Or.inl hb)
    · rcases rooted_cut_vertex_cover G x y b hroot hx hy ⟨v, hb⟩ with hc | hc
      · exact Or.inl (Or.inr ⟨hb, hc⟩)
      · exact Or.inr (Or.inr ⟨hb, hc⟩)

theorem rootedCutSide_inter [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) :
    rootedCutSide G b x hx ∩ rootedCutSide G b y hy = {b} := by
  ext v
  change (v ∈ rootedCutSide G b x hx ∧ v ∈ rootedCutSide G b y hy) ↔ v = b
  constructor
  · rintro ⟨hvx, hvy⟩
    rcases hvx with hvx | ⟨_hvx, hcX⟩
    · exact hvx
    · rcases hvy with hvy | ⟨_hvy, hcY⟩
      · exact hvy
      · exact False.elim (rooted_cut_roots_distinct G x y b hroot hx hy hbad
          (hcX.symm.trans hcY))
  · intro he
    exact ⟨Or.inl he, Or.inl he⟩

theorem rootedCutSide_neighbor_ncard (G : SimpleGraph V) (b x : V) (hx : x ≠ b)
    (t : rootedCutSide G b x hx) (ht : t.1 ≠ b) :
    (G.neighborSet t.1).ncard =
      ((G.induce (rootedCutSide G b x hx)).neighborSet t).ncard := by
  apply Set.ncard_congr (fun a ha =>
    (⟨a, rootedCutSide_closed G b x hx t.1 t.2 ht a ha⟩ : rootedCutSide G b x hx))
  · intro a ha
    exact ha
  · intro a d ha hd he
    exact congrArg Subtype.val he
  · intro d hd
    exact ⟨d.1, hd, Subtype.ext rfl⟩

theorem rootedCutSide_nonroot_degree [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected) (hdeg : NonrootDegreeAtLeast G x y 3) :
    NonrootDegreeAtLeast (G.induce (rootedCutSide G b x hx))
      (⟨x, Or.inr ⟨hx, rfl⟩⟩ : rootedCutSide G b x hx)
      (⟨b, Or.inl rfl⟩ : rootedCutSide G b x hx) 3 := by
  intro t htx htb
  have htx' : t.1 ≠ x := fun he => htx (Subtype.ext he)
  have htb' : t.1 ≠ b := fun he => htb (Subtype.ext he)
  have hty' : t.1 ≠ y := by
    intro he
    exact rootedCutSide_other_root_not_mem G x y b hroot hx hy hbad (he ▸ t.2)
  rw [← rootedCutSide_neighbor_ncard G b x hx t htb']
  exact hdeg t.1 htx' hty'

theorem rootedCutSide_card_lt [Fintype V] (G : SimpleGraph V) (x y b : V)
    (hroot : RootedTwoConnected G x y) (hx : x ≠ b) (hy : y ≠ b)
    (hbad : ¬(G.induce {v | v ≠ b}).Connected)
    [Fintype (rootedCutSide G b x hx)] :
    Fintype.card (rootedCutSide G b x hx) < Fintype.card V := by
  exact Fintype.card_subtype_lt (p := fun v => v ∈ rootedCutSide G b x hx) (x := y)
    (rootedCutSide_other_root_not_mem G x y b hroot hx hy hbad)

#print axioms rootedCutSide
#print axioms rootedCutSide_closed
#print axioms rootedCutSide_other_root_not_mem
#print axioms rootedCutSide_cover
#print axioms rootedCutSide_inter
#print axioms rootedCutSide_neighbor_ncard
#print axioms rootedCutSide_nonroot_degree
#print axioms rootedCutSide_card_lt
end TaskH.Fan
