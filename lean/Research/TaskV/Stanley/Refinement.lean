import Research.TaskV.Stanley.Histogram

namespace StanleyContinuation
noncomputable section

def recolor {V C D : Type*} (G : SimpleGraph V) (e : C ≃ D) :
    ProperAssignments G C ≃ ProperAssignments G D where
  toFun f := ⟨fun i => e (f.1 i), fun _ _ h => fun he => f.2 _ _ h (e.injective he)⟩
  invFun g := ⟨fun i => e.symm (g.1 i), fun _ _ h => fun he => g.2 _ _ h (e.symm.injective he)⟩
  left_inv _ := Subtype.ext (funext fun _ => e.symm_apply_apply _)
  right_inv _ := Subtype.ext (funext fun _ => e.apply_symm_apply _)

theorem histogram_recolor {V C D : Type*} {G : SimpleGraph V} (e : C ≃ D)
    (f : ProperAssignments G C) (c : C) :
    histogram ((recolor G e f).1) (e c) = histogram f.1 c := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  exact fun _ => e.apply_eq_iff_eq

theorem paletteEquiv {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (h : SameCSF G H) (C : Type*) [Fintype C] :
    ∃ e : ProperAssignments G C ≃ ProperAssignments H C,
      ∀ f, histogram (e f).1 = histogram f.1 := by
  classical
  let i := Fintype.equivFin C
  obtain ⟨j,hj⟩ := sameCSF_iff_histEquiv h (Fintype.card C)
  let e := ((recolor G i).trans j).trans (recolor H i).symm
  refine ⟨e, fun f => funext fun c => ?_⟩
  rw [← histogram_recolor i (e f) c, ← histogram_recolor i f c]
  have he : recolor H i (e f) = j (recolor G i f) :=
    (recolor H i).apply_symm_apply _
  rw [he, hj]

def Sized {V C : Type*} (s : C → ℕ) := {f : V → C // histogram f = s}
instance {V C : Type*} [Finite V] [Finite C] (s : C → ℕ) :
    Finite (Sized (V := V) s) := by unfold Sized; infer_instance

def GroupColor {V C D : Type*} (G : SimpleGraph V) (s : C → ℕ) :=
  {f : ProperAssignments G (C × D) // histogram (fun i => (f.1 i).1) = s}

theorem hist_fst {V C D : Type*} [Fintype V] [Fintype D] (f : V → C × D) (c : C) :
    histogram (fun i => (f i).1) c = ∑ d, histogram f (c,d) := by
  classical
  let g (i : {v // (f v).1 = c}) := (f i.1).2
  have he (d : D) : histogram g d = histogram f (c,d) := by
    apply Nat.card_congr
    exact {
      toFun := fun v => ⟨v.1.1, Prod.ext v.1.2 v.2⟩
      invFun := fun v => ⟨⟨v.1, congrArg Prod.fst v.2⟩, congrArg Prod.snd v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← funext he]
  change Nat.card {v // (f v).1 = c} = ∑ d, histogram g d
  rw [hist_total, Nat.card_eq_fintype_card]

theorem sameRefinementCard {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (h : SameCSF G H) {k q : ℕ} (s : Fin k → ℕ) :
    Nat.card (GroupColor (D := Fin q) G s) = Nat.card (GroupColor (D := Fin q) H s) := by
  classical
  obtain ⟨e,he⟩ := paletteEquiv h (Fin k × Fin q)
  apply Nat.card_congr
  apply e.subtypeEquiv
  intro f
  have hx : histogram (fun i => ((e f).1 i).1) = histogram (fun i => (f.1 i).1) := by
    funext c
    rw [hist_fst, hist_fst, he]
  rw [hx]

private theorem shade_transport {V C D : Type*} {G : SimpleGraph V} {f : V → C}
    (g : ∀ c, ProperAssignments (G.induce {i : V | f i = c}) D)
    (v : V) {c : C} (hc : f v = c) :
    (g (f v)).1 ⟨v,rfl⟩ = (g c).1 ⟨v,hc⟩ := by
  subst c
  rfl

/-- Separating the fine palette into k disjoint shade palettes. -/
def groupColorEquiv {V C D : Type*} (G : SimpleGraph V) (s : C → ℕ) :
    GroupColor (D := D) G s ≃
      Σ f : Sized (V := V) s, ∀ c, ProperAssignments (G.induce {i : V | f.1 i = c}) D where
  toFun z :=
    ⟨⟨fun v => (z.1.1 v).1, z.2⟩, fun c =>
      ⟨fun i => (z.1.1 i.1).2, fun x y hxy hshade =>
        z.1.2 x.1 y.1 hxy (Prod.ext (x.2.trans y.2.symm) hshade)⟩⟩
  invFun z := ⟨⟨fun v => (z.1.1 v, (z.2 (z.1.1 v)).1 ⟨v,rfl⟩), by
    intro x y hxy hcol
    have hfirst : z.1.1 x = z.1.1 y := congrArg Prod.fst hcol
    have hsecond := congrArg Prod.snd hcol
    let cx : {v | z.1.1 v = z.1.1 x} := ⟨x, rfl⟩
    let cy : {v | z.1.1 v = z.1.1 x} := ⟨y, hfirst.symm⟩
    apply (z.2 (z.1.1 x)).2 cx cy hxy
    suffices ht : (z.2 (z.1.1 y)).1 ⟨y,rfl⟩ = (z.2 (z.1.1 x)).1 cy from
      hsecond.trans ht
    exact shade_transport z.2 y hfirst.symm⟩, z.1.2⟩
  left_inv z := rfl
  right_inv z := by
    rcases z with ⟨⟨f,hf⟩,g⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    funext c
    apply Subtype.ext
    funext v
    rcases v with ⟨v,hv⟩
    subst c
    rfl
end
end StanleyContinuation
