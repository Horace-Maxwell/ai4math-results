import Research.TaskH.Six.EqualityDegree

/-!
Actual four-edge simple paths rooted at a vertex. Their finite carrier is
built from successively available original graph neighbors, so its lower
bound is a graph count and not a supplied numerical premise.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def rootAvailable (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (S : Finset V) : Finset V := by
  classical
  exact G.neighborFinset x \ S

theorem mem_rootAvailable (x y : V) (S : Finset V) :
    y ∈ rootAvailable G x S ↔ G.Adj x y ∧ y ∉ S := by
  classical
  simp only [rootAvailable, Finset.mem_sdiff, G.mem_neighborFinset]

theorem rootAvailable_card_ge (x : V) (S : Finset V) (δ t : ℕ)
    (hd : δ ≤ G.degree x) (hS : S.card ≤ t) :
    δ - t ≤ (rootAvailable G x S).card := by
  classical
  have he := Finset.card_sdiff_add_card_inter (G.neighborFinset x) S
  have hi := Finset.card_le_card (Finset.inter_subset_right (s₁ := G.neighborFinset x) (s₂ := S))
  rw [G.card_neighborFinset_eq_degree] at he
  change δ - t ≤ (G.neighborFinset x \ S).card
  omega

/-- Four successive actual neighbor choices; every old path point is
excluded at the next step, while adjacency already excludes the current one. -/
noncomputable abbrev RootFourChoice (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Type u := by
  classical
  exact (a : G.neighborSet v) ×
    (b : ↥(rootAvailable G a.val {v})) ×
      (c : ↥(rootAvailable G b.val {v, a.val})) ×
        ↥(rootAvailable G c.val {v, a.val, b.val})

noncomputable def rootFourChoiceWord (v : V) (p : RootFourChoice G v) : Fin 5 → V :=
  ![v, p.1.val, p.2.1.val, p.2.2.1.val, p.2.2.2.val]

def IsRootFourPath (G : SimpleGraph V) (v : V) (f : Fin 5 → V) : Prop :=
  f 0 = v ∧ Function.Injective f ∧
    G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧
      G.Adj (f 2) (f 3) ∧ G.Adj (f 3) (f 4)

theorem rootFourChoiceWord_isPath (v : V) (p : RootFourChoice G v) :
    IsRootFourPath G v (rootFourChoiceWord v p) := by
  classical
  rcases p with ⟨a, b, c, d⟩
  have ha := a.property
  have ha0 : a.val ≠ v := a.property.ne.symm
  have hb := (mem_rootAvailable a.val b.val {v}).mp b.property
  have hc := (mem_rootAvailable b.val c.val {v, a.val}).mp c.property
  have hd := (mem_rootAvailable c.val d.val {v, a.val, b.val}).mp d.property
  have hb0 : b.val ≠ v := by simpa only [Finset.mem_singleton] using hb.2
  have hc0 : c.val ≠ v := by
    intro he
    exact hc.2 (Finset.mem_insert.mpr (Or.inl he))
  have hc1 : c.val ≠ a.val := by
    intro he
    exact hc.2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he)))
  have hd0 : d.val ≠ v := by
    intro he
    exact hd.2 (Finset.mem_insert.mpr (Or.inl he))
  have hd1 : d.val ≠ a.val := by
    intro he
    exact hd.2 (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inl he))))
  have hd2 : d.val ≠ b.val := by
    intro he
    exact hd.2 (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he)))))
  refine ⟨rfl, ?_, ha, hb.1, hc.1, hd.1⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [rootFourChoiceWord, ha.ne, hb.1.ne, hc.1.ne, hd.1.ne]

theorem rootFourChoiceWord_injective (v : V) :
    Function.Injective (rootFourChoiceWord (G := G) v) := by
  intro p q he
  rcases p with ⟨a, b, c, d⟩
  rcases q with ⟨a', b', c', d'⟩
  have ha : a = a' := Subtype.ext (congrFun he 1)
  subst a'
  have hb : b = b' := Subtype.ext (congrFun he 2)
  subst b'
  have hc : c = c' := Subtype.ext (congrFun he 3)
  subst c'
  have hd : d = d' := Subtype.ext (congrFun he 4)
  subst d'
  rfl

noncomputable def rootFourPaths (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Finset (Fin 5 → V) := by
  classical
  exact Finset.univ.image (rootFourChoiceWord (G := G) v)

theorem mem_rootFourPaths_spec (v : V) (f : Fin 5 → V) (hf : f ∈ rootFourPaths G v) :
    IsRootFourPath G v f := by
  classical
  obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hf
  exact rootFourChoiceWord_isPath v p

theorem rootFourPaths_card (v : V) :
    (rootFourPaths G v).card = Fintype.card (RootFourChoice G v) := by
  classical
  rw [rootFourPaths, Finset.card_image_of_injective _ (rootFourChoiceWord_injective v),
    Finset.card_univ]

theorem rootFourPaths_card_ge (δ : ℕ) (hmin : ∀ x : V, δ ≤ G.degree x) (v : V) :
    G.degree v * (δ - 1) * (δ - 2) * (δ - 3) ≤ (rootFourPaths G v).card := by
  classical
  have h2 : ∀ a : G.neighborSet v, δ - 1 ≤ (rootAvailable G a.val {v}).card := by
    intro a
    exact rootAvailable_card_ge a.val {v} δ 1 (hmin a.val) (by simp)
  have h3 : ∀ (a : G.neighborSet v) (b : ↥(rootAvailable G a.val {v})),
      δ - 2 ≤ (rootAvailable G b.val {v, a.val}).card := by
    intro a b
    apply rootAvailable_card_ge b.val {v, a.val} δ 2 (hmin b.val)
    have hh := Finset.card_insert_le v ({a.val} : Finset V)
    simp only [Finset.card_singleton] at hh
    exact hh
  have h4 : ∀ (a : G.neighborSet v) (b : ↥(rootAvailable G a.val {v}))
      (c : ↥(rootAvailable G b.val {v, a.val})),
      δ - 3 ≤ (rootAvailable G c.val {v, a.val, b.val}).card := by
    intro a b c
    apply rootAvailable_card_ge c.val {v, a.val, b.val} δ 3 (hmin c.val)
    have hh := Finset.card_insert_le v ({a.val, b.val} : Finset V)
    have hk := Finset.card_insert_le a.val ({b.val} : Finset V)
    simp only [Finset.card_singleton] at hk
    omega
  rw [rootFourPaths_card]
  calc
    G.degree v * (δ - 1) * (δ - 2) * (δ - 3) =
        ∑ _a : G.neighborSet v, (δ - 1) * (δ - 2) * (δ - 3) := by
      simp [G.card_neighborSet_eq_degree, Nat.mul_assoc]
    _ ≤ ∑ a : G.neighborSet v,
        ∑ b : ↥(rootAvailable G a.val {v}),
          ∑ c : ↥(rootAvailable G b.val {v, a.val}),
            (rootAvailable G c.val {v, a.val, b.val}).card := by
      apply Finset.sum_le_sum
      intro a _ha
      calc
        (δ - 1) * (δ - 2) * (δ - 3) ≤
            (rootAvailable G a.val {v}).card * (δ - 2) * (δ - 3) :=
          Nat.mul_le_mul_right (δ - 3) (Nat.mul_le_mul_right (δ - 2) (h2 a))
        _ = ∑ _b : ↥(rootAvailable G a.val {v}), (δ - 2) * (δ - 3) := by
          simp [Nat.mul_assoc]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro b _hb
          calc
            (δ - 2) * (δ - 3) ≤
                (rootAvailable G b.val {v, a.val}).card * (δ - 3) :=
              Nat.mul_le_mul_right (δ - 3) (h3 a b)
            _ = ∑ _c : ↥(rootAvailable G b.val {v, a.val}), (δ - 3) := by simp
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro c _hc
              exact h4 a b c
    _ = Fintype.card (RootFourChoice G v) := by
      simp only [RootFourChoice, Fintype.card_sigma, Fintype.card_coe]

end TaskH.Six

#print axioms TaskH.Six.rootAvailable
#print axioms TaskH.Six.mem_rootAvailable
#print axioms TaskH.Six.rootAvailable_card_ge
#print axioms TaskH.Six.RootFourChoice
#print axioms TaskH.Six.rootFourChoiceWord
#print axioms TaskH.Six.IsRootFourPath
#print axioms TaskH.Six.rootFourChoiceWord_isPath
#print axioms TaskH.Six.rootFourChoiceWord_injective
#print axioms TaskH.Six.rootFourPaths
#print axioms TaskH.Six.mem_rootFourPaths_spec
#print axioms TaskH.Six.rootFourPaths_card
#print axioms TaskH.Six.rootFourPaths_card_ge
