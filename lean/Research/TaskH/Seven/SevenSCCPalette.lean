import Research.TaskH.Recolor

/-!
Finite palette and actual closed-recoloring lemmas for SCC confinement.
These helpers do not assume any graph component has a supplied coverage.
-/

set_option autoImplicit false

universe u v w

namespace TaskH.Seven

open SimpleGraph
open scoped Classical

variable {I : Type u} {A : Type v} {V : Type w}

noncomputable def palettePartialShift (σ : Equiv.Perm A) (B : Set A) (a : A) : A := by
  classical
  exact if a ∈ B then σ a else a

theorem palettePartialShift_closed (σ : Equiv.Perm A) (B : Set A)
    (hinj : Function.Injective (palettePartialShift σ B)) :
    ∀ ⦃a : A⦄, a ∈ B → σ a ∈ B := by
  classical
  intro a ha
  by_contra hn
  have he : palettePartialShift σ B a = palettePartialShift σ B (σ a) := by
    simp only [palettePartialShift, ite_eq_left ha, ite_eq_right hn]
  have hf : a = σ a := hinj he
  exact hn (hf ▸ ha)

theorem paletteClosed_eq_univ_of_orbit (σ : Equiv.Perm A) (B : Set A)
    (hclosed : ∀ ⦃a : A⦄, a ∈ B → σ a ∈ B)
    (horbit : ∀ a b : A, ∃ n : ℕ, (σ ^ n) a = b)
    (hne : B.Nonempty) : B = Set.univ := by
  obtain ⟨a, ha⟩ := hne
  have hpow : ∀ n : ℕ, (σ ^ n) a ∈ B := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih =>
      simpa only [pow_succ', Equiv.Perm.mul_apply] using hclosed ih
  apply Set.eq_univ_of_forall
  intro b
  obtain ⟨n, hn⟩ := horbit a b
  simpa only [hn] using hpow n

/-- Before and after an actual partial shift, injective color traces force
the set of shifted points to be empty or the entire trace. -/
theorem trace_partialShift_all (c d : V → A) (f : I → V)
    (hc : Function.Bijective (fun i => c (f i)))
    (hd : Function.Injective (fun i => d (f i)))
    (σ : Equiv.Perm A) (S : Set V)
    (hshift : ∀ i : I, d (f i) = if f i ∈ S then σ (c (f i)) else c (f i))
    (horbit : ∀ a b : A, ∃ n : ℕ, (σ ^ n) a = b)
    (hne : ∃ i : I, f i ∈ S) : ∀ j : I, f j ∈ S := by
  classical
  let e : I ≃ A := Equiv.ofBijective (fun i => c (f i)) hc
  let B : Set A := {a | f (e.symm a) ∈ S}
  have he : ∀ a : A, c (f (e.symm a)) = a := fun a => e.apply_symm_apply a
  have hval : ∀ a : A, palettePartialShift σ B a = d (f (e.symm a)) := by
    intro a
    rw [hshift]
    simp only [palettePartialShift, B, Set.mem_ofPred_eq, he]
  have hinj : Function.Injective (palettePartialShift σ B) := by
    intro a b hab
    have hdf : d (f (e.symm a)) = d (f (e.symm b)) :=
      (hval a).symm.trans (hab.trans (hval b))
    exact e.symm.injective (hd hdf)
  have hB : B.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    refine ⟨e i, ?_⟩
    simpa only [B, Set.mem_ofPred_eq, e.symm_apply_apply] using hi
  have hfull := paletteClosed_eq_univ_of_orbit σ B
    (palettePartialShift_closed σ B hinj) horbit hB
  intro j
  have hj : e j ∈ B := by rw [hfull]; trivial
  simpa only [B, Set.mem_ofPred_eq, e.symm_apply_apply] using hj

theorem trace_recolorClosed_all {G : SimpleGraph V} (c : G.Coloring A)
    (f : I → V) (hc : Function.Bijective (fun i => c (f i)))
    (σ : Equiv.Perm A) (S : Set V)
    (hclosed : ∀ ⦃a b : V⦄, a ∈ S → ColorStep G c σ a b → b ∈ S)
    (hd : Function.Injective (fun i => recolorClosed c σ S (@hclosed) (f i)))
    (horbit : ∀ a b : A, ∃ n : ℕ, (σ ^ n) a = b)
    (hne : ∃ i : I, f i ∈ S) : ∀ j : I, f j ∈ S := by
  apply trace_partialShift_all c (recolorClosed c σ S (@hclosed)) f hc hd σ S
    (fun i => recolorClosed_apply c σ S (@hclosed) (f i)) horbit hne

/-- The reachable closed set of each actual trace point contains the whole
trace. No topological ordering of a condensation digraph is required. -/
theorem trace_reachable_of_all_closed_recolors {G : SimpleGraph V}
    (c : G.Coloring A) (f : I → V)
    (hc : Function.Bijective (fun i => c (f i))) (σ : Equiv.Perm A)
    (horbit : ∀ a b : A, ∃ n : ℕ, (σ ^ n) a = b)
    (hrainbow : ∀ (S : Set V)
      (hclosed : ∀ ⦃a b : V⦄, a ∈ S → ColorStep G c σ a b → b ∈ S),
      Function.Injective (fun i => recolorClosed c σ S (@hclosed) (f i)))
    (i j : I) : Relation.ReflTransGen (ColorStep G c σ) (f i) (f j) := by
  let S : Set V := {z | Relation.ReflTransGen (ColorStep G c σ) (f i) z}
  have hclosed : ∀ ⦃a b : V⦄, a ∈ S → ColorStep G c σ a b → b ∈ S := by
    intro a b ha hab
    exact ha.tail hab
  have hall := trace_recolorClosed_all c f hc σ S (@hclosed)
    (hrainbow S (@hclosed)) horbit
    ⟨i, Relation.ReflTransGen.refl⟩
  exact hall j

end TaskH.Seven

#print axioms TaskH.Seven.palettePartialShift
#print axioms TaskH.Seven.palettePartialShift_closed
#print axioms TaskH.Seven.paletteClosed_eq_univ_of_orbit
#print axioms TaskH.Seven.trace_partialShift_all
#print axioms TaskH.Seven.trace_recolorClosed_all
#print axioms TaskH.Seven.trace_reachable_of_all_closed_recolors
