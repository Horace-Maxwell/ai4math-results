import Research.TaskJ.Rank.Challenge

namespace TaskJ.Rank.Values

open Challenge

private theorem central {n : ℕ} {t g : Equiv.Perm (Fin n)} :
    g ∈ equivariantGroup t ↔ t * g = g * t := by
  simp [equivariantGroup, Subgroup.mem_centralizer_iff]

private theorem rank_ge_two {G : Type*} [Group G] [Group.FG G] {a b : G}
    (hb : a * b ≠ b * a) : 2 ≤ Group.rank G := by
  classical
  by_contra! h
  obtain ⟨S, hcard, hgen⟩ := Group.rank_spec G
  obtain ⟨c,hc⟩ := Finset.card_le_one_iff_subset_singleton.mp (show S.card ≤ 1 by omega)
  have hle : Subgroup.closure (S : Set G) ≤ Subgroup.closure ({c} : Set G) :=
    Subgroup.closure_mono (by simpa only [Finset.coe_singleton] using (Finset.coe_subset.mpr hc))
  rw [hgen] at hle
  obtain ⟨i,hi⟩ := Subgroup.mem_closure_singleton.mp (hle (show a ∈ (⊤ : Subgroup G) from trivial))
  obtain ⟨j,hj⟩ := Subgroup.mem_closure_singleton.mp (hle (show b ∈ (⊤ : Subgroup G) from trivial))
  exact hb (hi ▸ hj ▸ zpow_mul_comm c i j)

private def x : Equiv.Perm (Fin 5) :=
  fiveSwap * (Equiv.swap 2 3 * Equiv.swap 3 4)
private def y : Equiv.Perm (Fin 5) := Equiv.swap 2 3
private def gx : equivariantGroup fiveSwap := ⟨x, central.mpr (by decide +kernel)⟩
private def gy : equivariantGroup fiveSwap := ⟨y, central.mpr (by decide +kernel)⟩

local instance : Fintype (Equiv.Perm (Fin 5)) := fintypePerm
local instance : Fintype (Equiv.Perm (Fin 2)) := fintypePerm

/-- In this actual action the twelve equivariant permutations are xⁱ and xⁱy. -/
private theorem normalForms :
    ∀ g : Equiv.Perm (Fin 5), fiveSwap * g = g * fiveSwap →
      ∃ i : Fin 6, g = x ^ (i : ℕ) ∨ g = x ^ (i : ℕ) * y := by
  decide +kernel

theorem five : FivePointRank := by
  classical
  change Group.rank (equivariantGroup fiveSwap) = 2
  apply le_antisymm
  · let S : Finset (equivariantGroup fiveSwap) := {gx, gy}
    have hgen : Subgroup.closure (S : Set (equivariantGroup fiveSwap)) = ⊤ := by
      apply top_unique
      intro g _
      have hx : gx ∈ Subgroup.closure (S : Set _) := Subgroup.subset_closure (by simp [S])
      have hy : gy ∈ Subgroup.closure (S : Set _) := Subgroup.subset_closure (by simp [S])
      obtain ⟨i,hi | hi⟩ := normalForms g.val (central.mp g.property)
      · have e : g = gx ^ (i : ℕ) := Subtype.ext hi
        exact e ▸ (Subgroup.pow_mem _ hx _)
      · have e : g = gx ^ (i : ℕ) * gy := Subtype.ext hi
        exact e ▸ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hx _) hy)
    apply (Group.rank_le hgen).trans
    simpa [S] using Finset.card_insert_le gx ({gy} : Finset (equivariantGroup fiveSwap))
  · apply rank_ge_two (a := gx) (b := gy)
    intro h
    have he : x * y = y * x := congrArg Subtype.val h
    exact (by decide +kernel : x * y ≠ y * x) he

private def generator : equivariantGroup twoSwap := ⟨twoSwap, central.mpr rfl⟩

private theorem twoForms : ∀ g : Equiv.Perm (Fin 2), g = 1 ∨ g = twoSwap := by
  decide +kernel

theorem two : TwoPointRank := by
  classical
  change Group.rank (equivariantGroup twoSwap) = 1
  have hgen : Subgroup.closure ({generator} : Set (equivariantGroup twoSwap)) = ⊤ := by
    apply top_unique
    intro g _
    rcases twoForms g.val with hg | hg
    · have e : g = 1 := Subtype.ext hg
      exact e ▸ Subgroup.one_mem _
    · have e : g = generator := Subtype.ext hg
      exact e ▸ Subgroup.subset_closure (by simp)
  have hu : Group.rank (equivariantGroup twoSwap) ≤ 1 := by
    simpa using (Group.rank_le (S := {generator}) (by simpa using hgen))
  have hn : ¬ Subsingleton (equivariantGroup twoSwap) := by
    intro hs
    have he : twoSwap = 1 := congrArg Subtype.val (hs.elim generator 1)
    exact (by decide +kernel : twoSwap ≠ 1) he
  have hpos : Group.rank (equivariantGroup twoSwap) ≠ 0 :=
    fun e => hn (Group.rank_eq_zero_iff.mp e)
  omega

end TaskJ.Rank.Values
#print axioms TaskJ.Rank.Values.two
#print axioms TaskJ.Rank.Values.five
