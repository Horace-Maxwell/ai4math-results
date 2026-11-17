import Research.TaskH.Five.FiveSparsePattern

/-!
Uniform-color groups use a single deleted-vertex coloring at each application.
The resulting finite degree budget is on actual graph neighbor sets.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

def ForcedTo (G : SimpleGraph V) (f : Fin 5 → V) (a : Fin 5) (y : V) : Prop :=
  ∀ (w : V) (c : (G.induce {x | x ≠ w}).Coloring (Fin 5))
    (hfw : ∀ i, f i ≠ w) (hyw : y ≠ w),
    c ⟨y, hyw⟩ = c ⟨f a, hfw a⟩

theorem anchor_forcedTo (f : Fin 5 → V) (a : Fin 5) : ForcedTo G f a (f a) := by
  intro w c hfw hyw
  rfl

variable [Fintype V] [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem forced_group_independent (hcrit : IsCriticalPlus 5 G)
    (hn : 9 ≤ Fintype.card V) (f : Fin 5 → V) (a : Fin 5) (Z : Finset V)
    (hforce : ∀ x ∈ Z, ForcedTo G f a x) :
    ∀ x ∈ Z, ∀ y ∈ Z, ¬ G.Adj x y := by
  intro x hx y hy hxy
  obtain ⟨w, hwS, hwT⟩ := exists_deletedVertex_away hn f {x, y}
    (by exact (Finset.card_le_two).trans (by decide))
  have hfw : ∀ i, f i ≠ w := by
    intro i hi
    apply hwS
    rw [← hi]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hxw : x ≠ w := by
    intro hi
    apply hwT
    simp [← hi]
  have hyw : y ≠ w := by
    intro hi
    apply hwT
    simp [← hi]
  obtain ⟨c⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  have hxcol := hforce x hx w c hfw hxw
  have hycol := hforce y hy w c hfw hyw
  have hxy' : (G.induce {z | z ≠ w}).Adj ⟨x, hxw⟩ ⟨y, hyw⟩ := hxy
  exact (c.valid hxy') (hxcol.trans hycol.symm)

theorem forced_group_four_neighbors_budget
    (hcrit : IsCriticalPlus 5 G) (hn : 9 ≤ Fintype.card V)
    (f : Fin 5 → V) (a : Fin 5) (Z : Finset V)
    (hS : (patternVertexSet f).card = 5)
    (hinter : (patternVertexSet f ∩ Z).card = 1)
    (hforce : ∀ x ∈ Z, ForcedTo G f a x)
    (hdeg : ∀ x : V, 6 ≤ G.degree x)
    (hin : ∀ x ∈ Z, (neighborsIn G (patternVertexSet f) x).card ≤ 2)
    (hcommon : ∀ z ∈ (patternVertexSet f)ᶜ, ∀ x ∈ Z, ∀ y ∈ Z,
      G.Adj x z → G.Adj y z → x = y) :
    5 * Z.card + 4 ≤ Fintype.card V := by
  classical
  let S := patternVertexSet f
  let T : Finset V := (S ∪ Z)ᶜ
  have hind := forced_group_independent hcrit hn f a Z hforce
  have hrow : ∀ x ∈ Z, 4 ≤ (neighborsIn G T x).card := by
    intro x hx
    have hp := neighborsIn_partition (G := G) S x
    have hd := hdeg x
    have hi := hin x hx
    change (neighborsIn G S x).card ≤ 2 at hi
    change (neighborsIn G S x).card + (neighborsIn G Sᶜ x).card = G.degree x at hp
    have he : neighborsIn G T x = neighborsIn G Sᶜ x := by
      ext y
      simp only [neighborsIn, Finset.mem_filter, T, Finset.mem_compl,
        Finset.mem_union]
      constructor
      · tauto
      · rintro ⟨hyS, hxy⟩
        have hyZ : y ∉ Z := fun hy => hind x hx y hy hxy
        exact ⟨not_or.mpr ⟨hyS, hyZ⟩, hxy⟩
    rw [he]
    omega
  have hcol : ∀ z ∈ T, (Z.filter (fun x => G.Adj x z)).card ≤ 1 := by
    intro z hz
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hzm : z ∈ Sᶜ := by
      have hh := Finset.mem_compl.mp hz
      exact Finset.mem_compl.mpr (fun h => hh (Finset.mem_union_left _ h))
    exact hcommon z hzm x (Finset.mem_filter.mp hx).1 y
      (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2
  have hbound : 4 * Z.card ≤ T.card := by
    calc
      _ = ∑ _x ∈ Z, 4 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ Z, (neighborsIn G T x).card := Finset.sum_le_sum hrow
      _ = ∑ z ∈ T, (Z.filter (fun x => G.Adj x z)).card := by
        convert FiniteBudget.relation_double_count Z T G.Adj using 1 <;>
          apply Finset.sum_congr rfl
        all_goals
          intro x _
          congr 1
          ext z
          simp only [neighborsIn, Finset.mem_filter]
      _ ≤ ∑ _z ∈ T, 1 := Finset.sum_le_sum hcol
      _ = T.card := by simp
  have hu := Finset.card_union_add_card_inter S Z
  have hc := Finset.card_add_card_compl (S ∪ Z)
  change S.card = 5 at hS
  change (S ∩ Z).card = 1 at hinter
  change (S ∪ Z).card + T.card = Fintype.card V at hc
  omega

end TaskH.Five

#print axioms TaskH.Five.anchor_forcedTo
#print axioms TaskH.Five.forced_group_independent
#print axioms TaskH.Five.forced_group_four_neighbors_budget
