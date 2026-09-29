import Research.Backfill.Paper4.Proof.CutVertexMetric
import Research.Backfill.Paper4.Proof.DHFourPointBase

/-! The finite distance-hereditary four-point theorem by deletion of a nonterminal.
Connected deletions use heredity; disconnected deletions use their components and a cut vertex.
No pendant/twin pruning theorem is assumed. Acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4
namespace DHFourPoint

def Quad {V : Type*} (G : SimpleGraph V) (a b c d : V) : Prop :=
  Challenge.FP (G.dist a b + G.dist c d) (G.dist a c + G.dist b d)
    (G.dist a d + G.dist b c)

theorem quad_swap12 {V : Type*} (G : SimpleGraph V) (a b c d : V) :
    Quad G a b c d ↔ Quad G b a c d := by
  have h := G.dist_comm (u := a) (v := b)
  unfold Quad Challenge.FP
  omega

theorem quad_swap23 {V : Type*} (G : SimpleGraph V) (a b c d : V) :
    Quad G a b c d ↔ Quad G a c b d := by
  have h := G.dist_comm (u := b) (v := c)
  unfold Quad Challenge.FP
  omega

theorem quad_swap34 {V : Type*} (G : SimpleGraph V) (a b c d : V) :
    Quad G a b c d ↔ Quad G a b d c := by
  have h := G.dist_comm (u := c) (v := d)
  unfold Quad Challenge.FP
  omega

theorem quad_rotate {V : Type*} (G : SimpleGraph V) (a b c d : V) :
    Quad G a b c d ↔ Quad G b c d a :=
  (quad_swap12 G a b c d).trans
    ((quad_swap23 G b a c d).trans (quad_swap34 G b c a d))

theorem quad_repeat {V : Type*} (G : SimpleGraph V) (hc : G.Connected) (a b c : V) :
    Quad G a a b c := by
  have ht := hc.dist_triangle (u := b) (v := a) (w := c)
  have hba := G.dist_comm (u := b) (v := a)
  unfold Quad Challenge.FP
  simp only [SimpleGraph.dist_self]
  omega

theorem fp_add {A B C k : ℕ} (h : Challenge.FP A B C) :
    Challenge.FP (A + k) (B + k) (C + k) := by
  unfold Challenge.FP at *
  omega

/-- Heredity along an induced graph embedding, including every further induced set. -/
theorem dh_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hd : Challenge.IsDistanceHereditary G) (e : H ↪g G) (hc : H.Connected) :
    Challenge.IsDistanceHereditary H := by
  refine ⟨hc, ?_⟩
  intro s hs x y
  let ei : H.induce s ↪g G := e.comp (SimpleGraph.Embedding.induce (G := H) s)
  have h1 := DHExtensionCore.embedding_dist_eq hd ei hs x y
  have h2 := DHExtensionCore.embedding_dist_eq hd e hc x.val y.val
  exact h1.trans h2.symm

/-- The component of a after deleting v, together with v itself. -/
def side {V : Type*} (G : SimpleGraph V) (v : V) (a : ({v}ᶜ : Set V)) : Set V :=
  {x | x = v ∨ ∃ hx : x ≠ v, (G.induce {v}ᶜ).Reachable a ⟨x, hx⟩}

theorem root_mem_side {V : Type*} (G : SimpleGraph V) (v : V)
    (a : ({v}ᶜ : Set V)) : v ∈ side G v a := Or.inl rfl

theorem mem_side_iff {V : Type*} (G : SimpleGraph V) (v : V)
    (a x : ({v}ᶜ : Set V)) : x.val ∈ side G v a ↔ (G.induce {v}ᶜ).Reachable a x := by
  constructor
  · rintro (h | ⟨hx, hr⟩)
    · exact (x.property h).elim
    · exact hr
  · intro hr
    exact Or.inr ⟨x.property, hr⟩

theorem self_mem_side {V : Type*} (G : SimpleGraph V) (v : V)
    (a : ({v}ᶜ : Set V)) : a.val ∈ side G v a :=
  (mem_side_iff G v a a).mpr SimpleGraph.Reachable.rfl

theorem side_adj_closed {V : Type*} (G : SimpleGraph V) (v : V)
    (a : ({v}ᶜ : Set V)) {x y : V} (hx : x ∈ side G v a)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : G.Adj x y) : y ∈ side G v a := by
  have hr := (mem_side_iff G v a (⟨x, hxv⟩ : ({v}ᶜ : Set V))).mp hx
  have ha : (G.induce {v}ᶜ).Adj (⟨x, hxv⟩ : ({v}ᶜ : Set V)) ⟨y, hyv⟩ := hxy
  exact (mem_side_iff G v a ⟨y, hyv⟩).mpr (hr.trans ha.reachable)

theorem side_retract {V : Type*} (G : SimpleGraph V) (hc : G.Connected)
    (v : V) (a : ({v}ᶜ : Set V)) :
    (G.induce (side G v a)).Connected ∧
      ∀ x y : side G v a, (G.induce (side G v a)).dist x y = G.dist x.val y.val := by
  classical
  let s := side G v a
  let r : V → s := fun x => if hx : x ∈ s then ⟨x, hx⟩ else ⟨v, root_mem_side G v a⟩
  apply DHExtensionCore.induce_retract G s r hc
  · intro x
    simp [r, x.property]
  · intro x y hxy
    by_cases hx : x ∈ s
    · by_cases hy : y ∈ s
      · right
        simpa [r, hx, hy] using hxy
      · have hxv : x = v := by
          by_contra hxv
          have hyv : y ≠ v := by
            intro hyv
            exact hy (hyv.symm ▸ root_mem_side G v a)
          exact hy (side_adj_closed G v a hx hxv hyv hxy)
        left
        have hrx : r x = ⟨x, hx⟩ := by simp [r, hx]
        have hry : r y = ⟨v, root_mem_side G v a⟩ := by simp [r, hy]
        rw [hrx, hry]
        exact Subtype.ext hxv
    · by_cases hy : y ∈ s
      · have hyv : y = v := by
          by_contra hyv
          have hxv : x ≠ v := by
            intro hxv
            exact hx (hxv.symm ▸ root_mem_side G v a)
          exact hx (side_adj_closed G v a hy hyv hxv hxy.symm)
        left
        have hrx : r x = ⟨v, root_mem_side G v a⟩ := by simp [r, hx]
        have hry : r y = ⟨y, hy⟩ := by simp [r, hy]
        rw [hrx, hry]
        exact Subtype.ext hyv.symm
      · left
        simp [r, hx, hy]

theorem side_proper {V : Type*} (G : SimpleGraph V) (v : V)
    (a : ({v}ᶜ : Set V)) (hn : ¬ (G.induce {v}ᶜ).Connected) :
    ∃ z : V, z ∉ side G v a := by
  classical
  by_contra h
  have hall : ∀ z : V, z ∈ side G v a := by simpa only [not_exists, not_not] using h
  have : Nonempty ({v}ᶜ : Set V) := ⟨a⟩
  apply hn
  refine ⟨?_⟩
  intro x y
  have hax := (mem_side_iff G v a x).mp (hall x.val)
  have hay := (mem_side_iff G v a y).mp (hall y.val)
  exact hax.symm.trans hay

/-- A vertex-count induction hypothesis; only used internally in the genuine induction. -/
def Smaller (V : Type) [Fintype V] : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < Fintype.card V →
    Challenge.IsDistanceHereditary H → Challenge.FourPointBM H

theorem quad_three_in_side {V : Type} [Fintype V] (G : SimpleGraph V)
    (hd : Challenge.IsDistanceHereditary G) (ih : Smaller V) (v : V)
    (hn : ¬ (G.induce {v}ᶜ).Connected) (a b c d : ({v}ᶜ : Set V))
    (hab : (G.induce {v}ᶜ).Reachable a b) (hac : (G.induce {v}ᶜ).Reachable a c) :
    Quad G a.val b.val c.val d.val := by
  classical
  let s := side G v a
  have hs := side_retract G hd.1 v a
  have hdists : ∀ x y : s, (G.induce s).dist x y = G.dist x.val y.val := hs.2
  have hds : Challenge.IsDistanceHereditary (G.induce s) :=
    dh_of_embedding hd (SimpleGraph.Embedding.induce (G := G) s) hs.1
  obtain ⟨z, hz⟩ := side_proper G v a hn
  have hlt : Fintype.card s < Fintype.card V := Fintype.card_subtype_lt hz
  have hfp := ih s (G.induce s) hlt hds
  let aa : s := ⟨a.val, self_mem_side G v a⟩
  let bb : s := ⟨b.val, (mem_side_iff G v a b).mpr hab⟩
  let cc : s := ⟨c.val, (mem_side_iff G v a c).mpr hac⟩
  by_cases hdm : d.val ∈ s
  · let dd : s := ⟨d.val, hdm⟩
    have h := hfp aa bb cc dd
    simpa only [Quad, hdists] using h
  · let vv : s := ⟨v, root_mem_side G v a⟩
    have h := hfp aa bb cc vv
    have h' : Quad G a.val b.val c.val v := by
      simpa only [Quad, hdists] using h
    have had : ¬ (G.induce {v}ᶜ).Reachable a d := by
      intro hr
      exact hdm ((mem_side_iff G v a d).mpr hr)
    have hbd : ¬ (G.induce {v}ᶜ).Reachable b d := fun hr => had (hab.trans hr)
    have hcd : ¬ (G.induce {v}ᶜ).Reachable c d := fun hr => had (hac.trans hr)
    have da := CutVertexMetric.dist_eq_add_of_not_reachable_delete G hd.1 v a.val d.val
      a.property d.property had
    have db := CutVertexMetric.dist_eq_add_of_not_reachable_delete G hd.1 v b.val d.val
      b.property d.property hbd
    have dc := CutVertexMetric.dist_eq_add_of_not_reachable_delete G hd.1 v c.val d.val
      c.property d.property hcd
    unfold Quad Challenge.FP at h' ⊢
    omega

theorem quad_cross {V : Type*} (G : SimpleGraph V) (hc : G.Connected) (v : V)
    (a b c d : ({v}ᶜ : Set V))
    (hac : ¬ (G.induce {v}ᶜ).Reachable a c)
    (had : ¬ (G.induce {v}ᶜ).Reachable a d)
    (hbc : ¬ (G.induce {v}ᶜ).Reachable b c)
    (hbd : ¬ (G.induce {v}ᶜ).Reachable b d) :
    Quad G a.val b.val c.val d.val := by
  have dac := CutVertexMetric.dist_eq_add_of_not_reachable_delete G hc v a.val c.val
    a.property c.property hac
  have dad := CutVertexMetric.dist_eq_add_of_not_reachable_delete G hc v a.val d.val
    a.property d.property had
  have dbc := CutVertexMetric.dist_eq_add_of_not_reachable_delete G hc v b.val c.val
    b.property c.property hbc
  have dbd := CutVertexMetric.dist_eq_add_of_not_reachable_delete G hc v b.val d.val
    b.property d.property hbd
  have tab := hc.dist_triangle (u := a.val) (v := v) (w := b.val)
  have tcd := hc.dist_triangle (u := c.val) (v := v) (w := d.val)
  have hca := G.dist_comm (u := c.val) (v := v)
  have hba := G.dist_comm (u := b.val) (v := v)
  unfold Quad Challenge.FP
  omega

theorem quad_delete_disconnected {V : Type} [Fintype V] (G : SimpleGraph V)
    (hd : Challenge.IsDistanceHereditary G) (ih : Smaller V) (v : V)
    (hn : ¬ (G.induce {v}ᶜ).Connected) (a b c d : ({v}ᶜ : Set V)) :
    Quad G a.val b.val c.val d.val := by
  classical
  by_cases hab : (G.induce {v}ᶜ).Reachable a b
  · by_cases hac : (G.induce {v}ᶜ).Reachable a c
    · exact quad_three_in_side G hd ih v hn a b c d hab hac
    · by_cases had : (G.induce {v}ᶜ).Reachable a d
      · exact (quad_swap34 G a.val b.val c.val d.val).mpr
          (quad_three_in_side G hd ih v hn a b d c hab had)
      · have hbc : ¬ (G.induce {v}ᶜ).Reachable b c := fun h => hac (hab.trans h)
        have hbd : ¬ (G.induce {v}ᶜ).Reachable b d := fun h => had (hab.trans h)
        exact quad_cross G hd.1 v a b c d hac had hbc hbd
  · by_cases hac : (G.induce {v}ᶜ).Reachable a c
    · by_cases had : (G.induce {v}ᶜ).Reachable a d
      · exact (quad_swap23 G a.val b.val c.val d.val).mpr
          ((quad_swap34 G a.val c.val b.val d.val).mpr
            (quad_three_in_side G hd ih v hn a c d b hac had))
      · have hcb : ¬ (G.induce {v}ᶜ).Reachable c b := fun h => hab (hac.trans h)
        have hcd : ¬ (G.induce {v}ᶜ).Reachable c d := fun h => had (hac.trans h)
        exact (quad_swap23 G a.val b.val c.val d.val).mpr
          (quad_cross G hd.1 v a c b d hab had hcb hcd)
    · by_cases had : (G.induce {v}ᶜ).Reachable a d
      · have hdb : ¬ (G.induce {v}ᶜ).Reachable d b := fun h => hab (had.trans h)
        have hdc : ¬ (G.induce {v}ᶜ).Reachable d c := fun h => hac (had.trans h)
        exact (quad_swap34 G a.val b.val c.val d.val).mpr
          ((quad_swap23 G a.val b.val d.val c.val).mpr
            (quad_cross G hd.1 v a d b c hab hac hdb hdc))
      · by_cases hbc : (G.induce {v}ᶜ).Reachable b c
        · by_cases hbd : (G.induce {v}ᶜ).Reachable b d
          · exact (quad_rotate G a.val b.val c.val d.val).mpr
              (quad_three_in_side G hd ih v hn b c d a hbc hbd)
          · have hdb : ¬ (G.induce {v}ᶜ).Reachable d b := fun h => hbd h.symm
            have hdc : ¬ (G.induce {v}ᶜ).Reachable d c := fun h => hbd (hbc.trans h.symm)
            exact (quad_swap34 G a.val b.val c.val d.val).mpr
              ((quad_swap23 G a.val b.val d.val c.val).mpr
                (quad_cross G hd.1 v a d b c hab hac hdb hdc))
        · by_cases hbd : (G.induce {v}ᶜ).Reachable b d
          · have hcb : ¬ (G.induce {v}ᶜ).Reachable c b := fun h => hbc h.symm
            have hcd : ¬ (G.induce {v}ᶜ).Reachable c d := fun h => hbc (hbd.trans h.symm)
            exact (quad_swap23 G a.val b.val c.val d.val).mpr
              (quad_cross G hd.1 v a c b d hab had hcb hcd)
          · exact quad_cross G hd.1 v a b c d hac had hbc hbd

theorem quad_of_cover {V : Type*} (G : SimpleGraph V) (hc : G.Connected) (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hcover : ∀ x : V, x = a ∨ x = b ∨ x = c ∨ x = d) : Quad G a b c d := by
  classical
  let f : Fin 4 → V := ![a, b, c, d]
  have hinj : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hsurj : Function.Surjective f := by
    intro x
    rcases hcover x with h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
  let e : Fin 4 ≃ V := Equiv.ofBijective f ⟨hinj, hsurj⟩
  let H : SimpleGraph (Fin 4) := G.comap e
  let ei : H ≃g G := { toEquiv := e, map_rel_iff' := by intro i j; rfl }
  have hH : H.Connected := ei.connected_iff.mpr hc
  have h := DHFourPointBase.fin4_fourPoint H hH 0 1 2 3
  have d01 := DHExtensionCore.iso_dist_eq ei hH 0 1
  have d02 := DHExtensionCore.iso_dist_eq ei hH 0 2
  have d03 := DHExtensionCore.iso_dist_eq ei hH 0 3
  have d12 := DHExtensionCore.iso_dist_eq ei hH 1 2
  have d13 := DHExtensionCore.iso_dist_eq ei hH 1 3
  have d23 := DHExtensionCore.iso_dist_eq ei hH 2 3
  change G.dist a b = H.dist 0 1 at d01
  change G.dist a c = H.dist 0 2 at d02
  change G.dist a d = H.dist 0 3 at d03
  change G.dist b c = H.dist 1 2 at d12
  change G.dist b d = H.dist 1 3 at d13
  change G.dist c d = H.dist 2 3 at d23
  unfold Quad
  rw [d01, d02, d03, d12, d13, d23]
  exact h

theorem quad_of_smaller {V : Type} [Fintype V] (G : SimpleGraph V)
    (hd : Challenge.IsDistanceHereditary G) (ih : Smaller V) (a b c d : V) :
    Quad G a b c d := by
  classical
  by_cases hab : a = b
  · subst b
    exact quad_repeat G hd.1 a c d
  by_cases hac : a = c
  · subst c
    exact (quad_swap23 G a b a d).mpr (quad_repeat G hd.1 a b d)
  by_cases had : a = d
  · subst d
    exact (quad_swap34 G a b c a).mpr
      ((quad_swap23 G a b a c).mpr (quad_repeat G hd.1 a b c))
  by_cases hbc : b = c
  · subst c
    exact (quad_swap12 G a b b d).mpr
      ((quad_swap23 G b a b d).mpr (quad_repeat G hd.1 b a d))
  by_cases hbd : b = d
  · subst d
    exact (quad_swap34 G a b c b).mpr
      ((quad_swap12 G a b b c).mpr
        ((quad_swap23 G b a b c).mpr (quad_repeat G hd.1 b a c)))
  by_cases hcd : c = d
  · subst d
    exact (quad_rotate G a b c c).mpr
      ((quad_rotate G b c c a).mpr (quad_repeat G hd.1 c a b))
  by_cases hcover : ∀ x : V, x = a ∨ x = b ∨ x = c ∨ x = d
  · exact quad_of_cover G hd.1 a b c d hab hac had hbc hbd hcd hcover
  · push Not at hcover
    obtain ⟨v, hva, hvb, hvc, hvd⟩ := hcover
    let aa : ({v}ᶜ : Set V) := ⟨a, hva.symm⟩
    let bb : ({v}ᶜ : Set V) := ⟨b, hvb.symm⟩
    let cc : ({v}ᶜ : Set V) := ⟨c, hvc.symm⟩
    let dd : ({v}ᶜ : Set V) := ⟨d, hvd.symm⟩
    by_cases hcD : (G.induce {v}ᶜ).Connected
    · have hdD : Challenge.IsDistanceHereditary (G.induce {v}ᶜ) :=
        dh_of_embedding hd (SimpleGraph.Embedding.induce (G := G) {v}ᶜ) hcD
      have hlt : Fintype.card ({v}ᶜ : Set V) < Fintype.card V :=
        Fintype.card_subtype_lt (x := v) (by simp)
      have hfp := ih ({v}ᶜ : Set V) (G.induce {v}ᶜ) hlt hdD
      have h := hfp aa bb cc dd
      have hdists := hd.2 {v}ᶜ hcD
      simpa only [Quad, hdists] using h
    · exact quad_delete_disconnected G hd ih v hcD aa bb cc dd

theorem fourPoint_of_dh : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    Challenge.IsDistanceHereditary G → Challenge.FourPointBM G := by
  classical
  have main : ∀ n : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → Challenge.IsDistanceHereditary G → Challenge.FourPointBM G := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ G hcard hd
      have hsmall : Smaller V := by
        intro W _ H hlt hH
        exact ih (Fintype.card W) (hlt.trans_eq hcard) W H rfl hH
      intro a b c d
      exact quad_of_smaller G hd hsmall a b c d
  intro V _ G hd
  exact main (Fintype.card V) V G rfl hd

end DHFourPoint

theorem check_BandeltMulder_DH_fourPoint : Challenge.BandeltMulder_DH_fourPoint :=
  DHFourPoint.fourPoint_of_dh

#print axioms check_BandeltMulder_DH_fourPoint

end CodexPaper4
