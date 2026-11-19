import Research.TaskJ.Rank.Extension.RankCRT
import Mathlib.SetTheory.Cardinal.NatCard

namespace TaskJ.Rank.Extension.CRT

/-- Two copies of a finite nontrivial cyclic group need precisely two generators. -/
theorem square_rank (G : Type*) [Group G] [Finite G] [Nontrivial G] [IsCyclic G] :
    Group.rank (G × G) = 2 := by
  classical
  apply le_antisymm
  · obtain ⟨c,hc⟩ := exists_zpow_surjective G
    let S : Finset (G × G) := {(c,1),(1,c)}
    have hL : (c,1) ∈ Subgroup.closure (S : Set (G × G)) :=
      Subgroup.subset_closure (by simp [S])
    have hR : (1,c) ∈ Subgroup.closure (S : Set (G × G)) :=
      Subgroup.subset_closure (by simp [S])
    have hg : Subgroup.closure (S : Set (G × G)) = ⊤ := by
      apply top_unique
      rintro ⟨x,y⟩ _
      obtain ⟨a,rfl⟩ := hc x
      obtain ⟨b,rfl⟩ := hc y
      simpa using (Subgroup.closure (S : Set (G × G))).mul_mem
        ((Subgroup.closure (S : Set (G × G))).zpow_mem hL a)
        ((Subgroup.closure (S : Set (G × G))).zpow_mem hR b)
    apply (Group.rank_le hg).trans
    simpa [S] using Finset.card_insert_le (c,1) ({(1,c)} : Finset (G×G))
  · by_contra! h
    obtain ⟨S,hcard,hgen⟩ := Group.rank_spec (G × G)
    obtain ⟨c,hc⟩ := Finset.card_le_one_iff_subset_singleton.mp (show S.card ≤ 1 by omega)
    have hle := Subgroup.closure_mono (show (S : Set (G×G)) ⊆ {c} from
      by simpa only [Finset.coe_singleton] using Finset.coe_subset.mpr hc)
    rw [hgen] at hle
    have : IsCyclic (G × G) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨c,by
      rw [Subgroup.zpowers_eq_closure]
      exact top_unique hle⟩
    have hh := coprime_card_of_isCyclic_prod G G
    have hcard := Finite.one_lt_card (α := G)
    simp [Nat.Coprime] at hh
    omega

end TaskJ.Rank.Extension.CRT
