import Mathlib

/-!
The pure relation-theoretic layer sets in the good-cycle construction.

All finite lengths are witnessed by genuine chains. Infinite distance is
represented by absence from every bounded layer; no ENat subtraction occurs.
Reachability avoiding a layer is the ordinary reflexive transitive closure
of the relation with both endpoints outside that layer.
-/

universe u

namespace TaskH.LayerSets

variable {V : Type u}

/-- A genuine relation chain with an exact number of steps and a fixed root. -/
inductive Chain (R : V → V → Prop) (a : V) : ℕ → V → Prop where
  | nil : Chain R a 0 a
  | tail {n : ℕ} {x y : V} : Chain R a n x → R x y → Chain R a (n + 1) y

theorem Chain.mono {R Q : V → V → Prop} {a b : V} {n : ℕ}
    (h : Chain R a n b) (hRQ : ∀ ⦃x y : V⦄, R x y → Q x y) :
    Chain Q a n b := by
  induction h with
  | nil => exact .nil
  | tail _ hxy ih => exact .tail ih (hRQ hxy)

theorem Chain.to_reflTransGen {R : V → V → Prop} {a b : V} {n : ℕ}
    (h : Chain R a n b) : Relation.ReflTransGen R a b := by
  induction h with
  | nil => exact .refl
  | tail _ hxy ih => exact ih.tail hxy

theorem reflTransGen_iff_exists_chain {R : V → V → Prop} {a b : V} :
    Relation.ReflTransGen R a b ↔ ∃ n : ℕ, Chain R a n b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, .nil⟩
    | tail _ hxy ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, .tail hn hxy⟩
  · rintro ⟨n, hn⟩
    exact hn.to_reflTransGen

/-- Points reached from the root in strictly fewer than i relation steps. -/
def S (R : V → V → Prop) (root : V) (i : ℕ) : Set V :=
  {x | ∃ n : ℕ, n < i ∧ Chain R root n x}

/-- The relation with both endpoints outside A. -/
def AvoidStep (R : V → V → Prop) (A : Set V) (x y : V) : Prop :=
  x ∉ A ∧ y ∉ A ∧ R x y

/-- The relation with both endpoints inside A. -/
def InsideStep (R : V → V → Prop) (A : Set V) (x y : V) : Prop :=
  x ∈ A ∧ y ∈ A ∧ R x y

/-- Points outside S_i that reach Z without entering S_i, including zero-step paths. -/
def T (R : V → V → Prop) (root : V) (Z : Set V) (i : ℕ) : Set V :=
  {x | x ∉ S R root i ∧
    ∃ z : V, z ∈ Z ∧ Relation.ReflTransGen (AvoidStep R (S R root i)) x z}

variable {R : V → V → Prop} {root : V} {Z : Set V}

theorem S_zero : S R root 0 = ∅ := by
  ext x
  simp [S]

theorem S_mono {i j : ℕ} (hij : i ≤ j) : S R root i ⊆ S R root j := by
  rintro x ⟨n, hn, hchain⟩
  exact ⟨n, lt_of_lt_of_le hn hij, hchain⟩

theorem root_mem_S {i : ℕ} (hi : 0 < i) : root ∈ S R root i :=
  ⟨0, hi, .nil⟩

theorem avoidStep_mono {A B : Set V} (hAB : A ⊆ B) :
    AvoidStep R B ≤ AvoidStep R A := by
  intro x y hxy
  exact ⟨fun hx => hxy.1 (hAB hx), fun hy => hxy.2.1 (hAB hy), hxy.2.2⟩

/-- The target-reaching layers decrease when the forbidden root layer increases. -/
theorem T_antitone {i j : ℕ} (hij : i ≤ j) : T R root Z j ⊆ T R root Z i := by
  rintro x ⟨hx, z, hz, hpath⟩
  refine ⟨fun hxi => hx (S_mono hij hxi), z, hz, ?_⟩
  exact (Relation.ReflTransGen.mono (avoidStep_mono (S_mono hij))) _ _ hpath

theorem root_not_mem_T {i : ℕ} (hi : 1 ≤ i) : root ∉ T R root Z i := by
  intro hx
  exact hx.1 (root_mem_S (by omega))

/-- A target is in T_i exactly when it lies outside S_i. -/
theorem target_mem_T_iff {i : ℕ} {z : V} (hz : z ∈ Z) :
    z ∈ T R root Z i ↔ z ∉ S R root i := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, z, hz, .refl⟩

/-- One relation step into T_i can be prepended provided its tail avoids S_i. -/
theorem mem_T_of_step {i : ℕ} {x y : V} (hxy : R x y)
    (hx : x ∉ S R root i) (hy : y ∈ T R root Z i) : x ∈ T R root Z i := by
  rcases hy with ⟨hyn, z, hz, hpath⟩
  exact ⟨hx, z, hz, Relation.ReflTransGen.head ⟨hx, hyn, hxy⟩ hpath⟩

/-- A step crossing into T_i must start in the forbidden root layer S_i. -/
theorem boundary_mem_S {i : ℕ} {x y : V} (hxy : R x y)
    (hy : y ∈ T R root Z i) (hx : x ∉ T R root Z i) : x ∈ S R root i := by
  classical
  by_contra hxs
  exact hx (mem_T_of_step hxy hxs hy)

/-- The boundary tail is exactly in layer i-1 and remains target-reaching one layer earlier. -/
theorem boundary_exact_layer {i : ℕ} {x y : V} (hxy : R x y)
    (hy : y ∈ T R root Z i) (hx : x ∉ T R root Z i) :
    0 < i ∧ Chain R root (i - 1) x ∧
      x ∉ S R root (i - 1) ∧ x ∈ T R root Z (i - 1) := by
  classical
  obtain ⟨n, hn, hchain⟩ := boundary_mem_S hxy hy hx
  have hnlow : i ≤ n + 1 := by
    by_contra hbad
    apply hy.1
    exact ⟨n + 1, by omega, .tail hchain hxy⟩
  have hne : n = i - 1 := by omega
  have hxprev : x ∉ S R root (i - 1) := by
    rintro ⟨m, hm, hmchain⟩
    apply hy.1
    exact ⟨m + 1, by omega, .tail hmchain hxy⟩
  have hyp : y ∈ T R root Z (i - 1) := T_antitone (Nat.sub_le i 1) hy
  refine ⟨by omega, ?_, hxprev, mem_T_of_step hxy hxprev hyp⟩
  simpa only [hne] using hchain

theorem boundary_mem_T_prev_diff {i : ℕ} {x y : V} (hxy : R x y)
    (hy : y ∈ T R root Z i) (hx : x ∉ T R root Z i) :
    x ∈ T R root Z (i - 1) \ T R root Z i :=
  ⟨(boundary_exact_layer hxy hy hx).2.2.2, hx⟩

/-- A short root chain stays inside the same bounded root layer. -/
theorem Chain.inside_S {n : ℕ} {x : V} (h : Chain R root n x) :
    ∀ i : ℕ, n < i → Chain (InsideStep R (S R root i)) root n x := by
  induction h with
  | nil =>
    intro i _
    exact .nil
  | @tail n x y h hxy ih =>
    intro i hi
    refine .tail (ih i (by omega)) ?_
    exact ⟨⟨n, by omega, h⟩, ⟨n + 1, hi, .tail h hxy⟩, hxy⟩

/-- Every point of S_i is outside T_i. -/
theorem inside_S_avoids_T {i : ℕ} {x y : V}
    (hxy : InsideStep R (S R root i) x y) :
    AvoidStep R (T R root Z i) x y :=
  ⟨fun hx => hx.1 hxy.1, fun hy => hy.1 hxy.2.1, hxy.2.2⟩

/-- A root chain of length below i never enters T_i. -/
theorem Chain.avoids_T_of_short {n : ℕ} {x : V} (h : Chain R root n x)
    {i : ℕ} (hn : n < i) : Chain (AvoidStep R (T R root Z i)) root n x :=
  (h.inside_S i hn).mono (fun {_a _b} hxy => inside_S_avoids_T hxy)

theorem avoidReach_end_not_mem {A : Set V} {x z : V} (hx : x ∉ A)
    (hpath : Relation.ReflTransGen (AvoidStep R A) x z) : z ∉ A := by
  induction hpath with
  | refl => exact hx
  | tail _ hxy _ => exact hxy.2.1

/-- A path to a target can be chosen wholly within T_i, with both endpoints in T_i. -/
theorem reachable_inside_T {i : ℕ} {x z : V} (hx : x ∉ S R root i) (hz : z ∈ Z)
    (hpath : Relation.ReflTransGen (AvoidStep R (S R root i)) x z) :
    x ∈ T R root Z i ∧ z ∈ T R root Z i ∧
      Relation.ReflTransGen (InsideStep R (T R root Z i)) x z := by
  have hxT : x ∈ T R root Z i := ⟨hx, z, hz, hpath⟩
  have hzT : z ∈ T R root Z i :=
    (target_mem_T_iff hz).mpr (avoidReach_end_not_mem hx hpath)
  have go : ∀ {a : V}, Relation.ReflTransGen (AvoidStep R (S R root i)) a z →
      Relation.ReflTransGen (InsideStep R (T R root Z i)) a z := by
    intro a h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | @head a b hab hbz ih =>
      have haT : a ∈ T R root Z i :=
        ⟨hab.1, z, hz, Relation.ReflTransGen.head hab hbz⟩
      have hbT : b ∈ T R root Z i := ⟨hab.2.1, z, hz, hbz⟩
      exact Relation.ReflTransGen.head ⟨haT, hbT, hab.2.2⟩ ih
  exact ⟨hxT, hzT, go hpath⟩

theorem mem_T_exists_inside_path {i : ℕ} {x : V} (hx : x ∈ T R root Z i) :
    ∃ z : V, z ∈ Z ∧ z ∈ T R root Z i ∧
      Relation.ReflTransGen (InsideStep R (T R root Z i)) x z := by
  rcases hx with ⟨hxn, z, hz, hpath⟩
  have hinside := reachable_inside_T hxn hz hpath
  exact ⟨z, hz, hinside.2.1, hinside.2.2⟩

end TaskH.LayerSets

#print axioms TaskH.LayerSets.reflTransGen_iff_exists_chain
#print axioms TaskH.LayerSets.T_antitone
#print axioms TaskH.LayerSets.boundary_exact_layer
#print axioms TaskH.LayerSets.Chain.avoids_T_of_short
#print axioms TaskH.LayerSets.mem_T_exists_inside_path
