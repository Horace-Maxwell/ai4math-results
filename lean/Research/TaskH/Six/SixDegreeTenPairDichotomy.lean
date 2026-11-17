import Research.TaskH.Six.SixDegreeTenFrame
import Research.TaskH.Six.SixNeighborPathRule

/-!
The actual four two-vertex fibers have precisely two possible center-attachment
shapes. A split fiber and a different common fiber close a genuine nonrainbow
hexagon. Both alternatives are derived from the original following-cycle cover.
The edge between the centers is not prescribed here.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {v : V} {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}

def DegreeTenAssignable (F : DegreeTenColorFrame v c) (i : Fin 4) : Prop :=
  ∃ u w : Fin 2, u ≠ w ∧
    G.Adj (degreeTenCenter F 0).val (degreeTenPair F i u).val ∧
    G.Adj (degreeTenCenter F 1).val (degreeTenPair F i w).val

def DegreeTenCommon (F : DegreeTenColorFrame v c) (i : Fin 4) : Prop :=
  ∃ r : Fin 2,
    G.Adj (degreeTenCenter F 0).val (degreeTenPair F i r).val ∧
    G.Adj (degreeTenCenter F 1).val (degreeTenPair F i r).val

def DegreeTenSplitAt (F : DegreeTenColorFrame v c) (i : Fin 4) (r : Fin 2) : Prop :=
  G.Adj (degreeTenCenter F 0).val (degreeTenPair F i r).val ∧
    ¬ G.Adj (degreeTenCenter F 1).val (degreeTenPair F i r).val ∧
    G.Adj (degreeTenCenter F 1).val (degreeTenPair F i (r + 1)).val ∧
    ¬ G.Adj (degreeTenCenter F 0).val (degreeTenPair F i (r + 1)).val

def DegreeTenCommonAt (F : DegreeTenColorFrame v c) (i : Fin 4) (r : Fin 2) : Prop :=
  G.Adj (degreeTenCenter F 0).val (degreeTenPair F i r).val ∧
    G.Adj (degreeTenCenter F 1).val (degreeTenPair F i r).val ∧
    ¬ G.Adj (degreeTenCenter F 0).val (degreeTenPair F i (r + 1)).val ∧
    ¬ G.Adj (degreeTenCenter F 1).val (degreeTenPair F i (r + 1)).val

theorem degreeTen_assignable_common_incompatible (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (i j : Fin 4) (hij : i ≠ j)
    (hi : DegreeTenAssignable F i) (hj : DegreeTenCommon F j) : False := by
  obtain ⟨u, w, huw, hau, hbw⟩ := hi
  obtain ⟨r, har, hbr⟩ := hj
  let P : Fin 5 → V := ![(degreeTenPair F i u).val, (degreeTenCenter F 0).val,
    (degreeTenPair F j r).val, (degreeTenCenter F 1).val, (degreeTenPair F i w).val]
  have hCC : (degreeTenCenter F 0).val ≠ (degreeTenCenter F 1).val :=
    (degreeTenCenter_val_injective F).ne (by decide)
  have hUW : (degreeTenPair F i u).val ≠ (degreeTenPair F i w).val :=
    (degreeTenPair_all_val_injective F).ne
      (show ((i, u) : Fin 4 × Fin 2) ≠ (i, w) from
        fun he => huw (congrArg Prod.snd he))
  have hUR : (degreeTenPair F i u).val ≠ (degreeTenPair F j r).val :=
    (degreeTenPair_all_val_injective F).ne
      (show ((i, u) : Fin 4 × Fin 2) ≠ (j, r) from
        fun he => hij (congrArg Prod.fst he))
  have hWR : (degreeTenPair F i w).val ≠ (degreeTenPair F j r).val :=
    (degreeTenPair_all_val_injective F).ne
      (show ((i, w) : Fin 4 × Fin 2) ≠ (j, r) from
        fun he => hij (congrArg Prod.fst he))
  have hCP : ∀ a b d, (degreeTenCenter F a).val ≠ (degreeTenPair F b d).val :=
    degreeTenCenter_pair_ne F
  have hPC : ∀ a b d, (degreeTenPair F b d).val ≠ (degreeTenCenter F a).val :=
    fun a b d => (hCP a b d).symm
  have h0u := degreeTenCenter_pair_ne F 0 i u
  have h0r := degreeTenCenter_pair_ne F 0 j r
  have h0w := degreeTenCenter_pair_ne F 0 i w
  have h1u := degreeTenCenter_pair_ne F 1 i u
  have h1r := degreeTenCenter_pair_ne F 1 j r
  have h1w := degreeTenCenter_pair_ne F 1 i w
  have hPi : Function.Injective P := by
    intro a b he
    fin_cases a <;> fin_cases b <;> simp_all [P]
  have hPv : ∀ a, P a ≠ v := by
    intro a
    fin_cases a
    · exact (degreeTenPair F i u).property.ne.symm
    · exact (degreeTenCenter F 0).property.ne.symm
    · exact (degreeTenPair F j r).property.ne.symm
    · exact (degreeTenCenter F 1).property.ne.symm
    · exact (degreeTenPair F i w).property.ne.symm
  have hcolors := rainbow_five_path_colors_injective hr v c P hPi hPv
    (degreeTenPair F i u).property hau.symm har hbr.symm hbw
    (degreeTenPair F i w).property.symm
  have hcolor : c ⟨P 0, hPv 0⟩ = c ⟨P 4, hPv 4⟩ :=
    (degreeTenPair_color F i u).trans (degreeTenPair_color F i w).symm
  exact (by decide : (0 : Fin 5) ≠ 4) (hcolors hcolor)

theorem degreeTen_pair_assignable_or_common
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (i : Fin 4) :
    DegreeTenAssignable F i ∨ DegreeTenCommon F i := by
  obtain ⟨u, hu⟩ := degreeTenCenter_covers_each_pair hcrit hs hr F 0 i
  obtain ⟨w, hw⟩ := degreeTenCenter_covers_each_pair hcrit hs hr F 1 i
  by_cases he : u = w
  · exact Or.inr ⟨u, hu, by simpa only [he] using hw⟩
  · exact Or.inl ⟨u, w, he, hu, hw⟩

theorem degreeTen_common_exact_of_not_assignable
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (i : Fin 4) (hnot : ¬ DegreeTenAssignable F i) :
    ∃ r : Fin 2, DegreeTenCommonAt F i r := by
  obtain ⟨u, hu⟩ := degreeTenCenter_covers_each_pair hcrit hs hr F 0 i
  obtain ⟨w, hw⟩ := degreeTenCenter_covers_each_pair hcrit hs hr F 1 i
  have he : u = w := by
    by_contra hne
    exact hnot ⟨u, w, hne, hu, hw⟩
  have hbu : G.Adj (degreeTenCenter F 1).val (degreeTenPair F i u).val := by
    simpa only [he] using hw
  have hother : (u + 1 : Fin 2) ≠ u := by fin_cases u <;> decide +kernel
  refine ⟨u, hu, hbu, ?_, ?_⟩
  · intro h
    exact hnot ⟨u + 1, u, hother, h, hbu⟩
  · intro h
    exact hnot ⟨u, u + 1, hother.symm, hu, h⟩

theorem degreeTen_split_of_not_common
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (i : Fin 4) (hnot : ¬ DegreeTenCommon F i) :
    ∃ r : Fin 2, DegreeTenSplitAt F i r := by
  obtain ⟨u, hu⟩ := degreeTenCenter_covers_each_pair hcrit hs hr F 0 i
  obtain ⟨w, hw⟩ := degreeTenCenter_covers_each_pair hcrit hs hr F 1 i
  have hne : u ≠ w := by
    intro he
    exact hnot ⟨u, hu, by simpa only [he] using hw⟩
  have hwother : w = u + 1 := by
    fin_cases u <;> fin_cases w <;> simp_all
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · intro h
    exact hnot ⟨u, hu, h⟩
  · simpa only [hwother] using hw
  · intro h
    exact hnot ⟨u + 1, h, by simpa only [hwother] using hw⟩

theorem degreeTen_pair_dichotomy
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) :
    (∃ ε : Fin 4 → Fin 2, ∀ i, DegreeTenSplitAt F i (ε i)) ∨
      ∃ r : Fin 4 → Fin 2, ∀ i, DegreeTenCommonAt F i (r i) := by
  classical
  by_cases hassign : ∃ i, DegreeTenAssignable F i
  · obtain ⟨i, hi⟩ := hassign
    have hnoCommon : ∀ j, ¬ DegreeTenCommon F j := by
      intro j hj
      by_cases hij : i ≠ j
      · exact degreeTen_assignable_common_incompatible hr F i j hij hi hj
      · have he : i = j := not_ne_iff.mp hij
        subst j
        let k : Fin 4 := i + 1
        have hki : k ≠ i := by fin_cases i <;> decide +kernel
        have hknot : ¬ DegreeTenCommon F k := fun hk =>
          degreeTen_assignable_common_incompatible hr F i k hki.symm hi hk
        have hk : DegreeTenAssignable F k :=
          (degreeTen_pair_assignable_or_common hcrit hs hr F k).resolve_right hknot
        exact degreeTen_assignable_common_incompatible hr F k i hki hk hj
    choose ε hε using fun i => degreeTen_split_of_not_common hcrit hs hr F i (hnoCommon i)
    exact Or.inl ⟨ε, hε⟩
  · have hn : ∀ i, ¬ DegreeTenAssignable F i := fun i hi => hassign ⟨i, hi⟩
    choose r hr' using fun i => degreeTen_common_exact_of_not_assignable hcrit hs hr F i (hn i)
    exact Or.inr ⟨r, hr'⟩

end TaskH.Six

#print axioms TaskH.Six.DegreeTenAssignable
#print axioms TaskH.Six.DegreeTenCommon
#print axioms TaskH.Six.DegreeTenSplitAt
#print axioms TaskH.Six.DegreeTenCommonAt
#print axioms TaskH.Six.degreeTen_assignable_common_incompatible
#print axioms TaskH.Six.degreeTen_pair_assignable_or_common
#print axioms TaskH.Six.degreeTen_common_exact_of_not_assignable
#print axioms TaskH.Six.degreeTen_split_of_not_common
#print axioms TaskH.Six.degreeTen_pair_dichotomy
