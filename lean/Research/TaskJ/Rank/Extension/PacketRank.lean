import Research.TaskJ.Rank.Extension.OrbitStructure

namespace TaskJ.Rank.Extension.Family

noncomputable section
open scoped Classical

variable {n : ℕ} (D : Family n)

private theorem cyclic_basis (i : Fin n) :
    ∃ c : D.Weyl i, Subgroup.closure ({c} : Set (D.Weyl i)) = ⊤ := by
  have hc : IsCyclic (D.Weyl i) := (D.weylFiber i).isCyclic.mpr inferInstance
  obtain ⟨c,hc⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hc
  exact ⟨c, Subgroup.zpowers_eq_closure c ▸ hc⟩

private theorem weyl_rank_le_one (i : Fin n) : Group.rank (D.Weyl i) ≤ 1 := by
  classical
  obtain ⟨c,hc⟩ := D.cyclic_basis i
  have hs : Subgroup.closure (({c} : Finset (D.Weyl i)) : Set (D.Weyl i)) = ⊤ := by simpa using hc
  simpa using Group.rank_le hs

theorem valid_exists : ∃ B : D.Bases, D.Valid B := by
  classical
  choose gen hgen using D.cyclic_basis
  refine ⟨fun i => {gen i}, fun i => ⟨?_, ?_⟩⟩
  · simpa using hgen i
  · simp [max_eq_left (D.weyl_rank_le_one i)]

/-- Every legal basis on a Weyl factor is a singleton, and the order of its
element is the width of the corresponding cyclic orbit. -/
private theorem describe_basis {B : D.Bases} (hB : D.Valid B) (i : Fin n) :
    ∃ c : D.Weyl i, B i = {c} ∧ orderOf c = (D.width i : ℕ) := by
  classical
  have hc : (B i).card = 1 := (hB i).2.trans (max_eq_left (D.weyl_rank_le_one i))
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hc
  have hz : Subgroup.zpowers c = ⊤ := by
    rw [Subgroup.zpowers_eq_closure]
    simpa [hc] using (hB i).1
  exact ⟨c,hc,(orderOf_eq_card_of_zpowers_eq_top hz).trans (D.weyl_card i)⟩

theorem packets_eq {B : D.Bases} (hB : D.Valid B)
    (hwide : ∀ i, 1 < (D.width i : ℕ))
    (hcop : ∀ {i j}, i ≠ j → ¬ Nat.Coprime (D.width i : ℕ) (D.width j : ℕ)) :
    D.packets B = n := by
  classical
  choose gen hgen hord using D.describe_basis hB
  have nonidentity (i : Fin n) : gen i ≠ 1 := by
    intro he
    have ho := hord i
    rw [he,orderOf_one] at ho
    have := hwide i
    omega
  let pick (i : Fin n) : D.Item B := ⟨i,gen i,by simp [hgen i],nonidentity i⟩
  have uniqueItem (z : D.Item B) : pick z.1 = z := by
    rcases z with ⟨i,c,hc,hne⟩
    rw [hgen i,Finset.mem_singleton] at hc
    subst c
    rfl
  have fitsN : D.Fits B n := by
    refine ⟨fun z => z.1, ?_⟩
    intro x y hne he
    exact (hne ((uniqueItem x).symm.trans ((congrArg pick he).trans (uniqueItem y)))).elim
  have lower {k : ℕ} (hf : D.Fits B k) : n ≤ k := by
    obtain ⟨f, hf⟩ := hf
    have hinj : Function.Injective (fun i : Fin n => f (pick i)) := by
      intro i j he
      by_contra hij
      have hne : pick i ≠ pick j := fun h => hij (congrArg Sigma.fst h)
      have c := (hf (pick i) (pick j) hne he).2
      change Nat.Coprime (orderOf (gen i)) (orderOf (gen j)) at c
      rw [hord i, hord j] at c
      exact hcop hij c
    simpa using Fintype.card_le_of_injective _ hinj
  change sInf {k : ℕ | D.Fits B k} = n
  exact le_antisymm (csInf_le' fitsN) (le_csInf ⟨n,fitsN⟩ fun _ hk => lower hk)

end
end TaskJ.Rank.Extension.Family
