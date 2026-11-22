import Research.TaskS.B.Split
import Research.TaskS.B.RationalLine

open scoped BigOperators
open Module
namespace TaskS.B.Rounding

/-- The single-period input. All finite index types here may be taken in the first universe. -/
def LineBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (q : ι → ℕ), (∀ j, 0 < q j) → ∀ x : ι → ℝ,
    ∃ t : ℝ, ∑ j, Int.fract (x j + (q j : ℝ) * t) ≤ ((Fintype.card ι : ℝ) - 1) / 2

def CastsInto {ι : Type} (K : Submodule ℚ (ι → ℚ)) (H : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ z ∈ K, (fun j => (z j : ℝ)) ∈ H

private theorem part_cast {ι : Type} {K : Submodule ℚ (ι → ℚ)} {H : Submodule ℝ (ι → ℝ)}
    (h : CastsInto K H) (p : ι → Prop) : CastsInto (part K p) (part H p) := by
  intro y hy
  obtain ⟨z, hz, he⟩ := part_iff.mp hy
  exact part_iff.mpr ⟨_, h z hz, fun j => congrArg Rat.cast (he j)⟩

private theorem supported_cast {ι : Type} {K : Submodule ℚ (ι → ℚ)} {H : Submodule ℝ (ι → ℝ)}
    (h : CastsInto K H) (p : ι → Prop) : CastsInto (supported K p) (supported H p) := by
  intro y hy
  obtain ⟨z, hz, he, h0⟩ := supported_iff.mp hy
  exact supported_iff.mpr ⟨_, h z hz, fun j => congrArg Rat.cast (he j),
    fun j hj => by simp [h0 j hj]⟩

theorem round (hsaw : LineBound) (ι : Type) [Fintype ι] [Nonempty ι]
    (K : Submodule ℚ (ι → ℚ)) (H : Submodule ℝ (ι → ℝ)) (hKH : CastsInto K H)
    (q : K) (hq : ∀ j, 0 < q.val j) (x : ι → ℝ) :
    ∃ h ∈ H, ∑ j, Int.fract (x j + h j) ≤ ((Fintype.card ι : ℝ) - finrank ℚ K) / 2 := by
  classical
  by_cases hd : finrank ℚ K = 1
  · obtain ⟨w, hw, hwK⟩ := integer_direction K q hq
    obtain ⟨t, ht⟩ := hsaw ι w hw x
    refine ⟨t • (fun j => (w j : ℝ)), H.smul_mem _ ?_, ?_⟩
    · simpa using hKH _ hwK
    · simpa [hd, mul_comm t] using ht
  obtain ⟨v, hv, ⟨j0, hj0⟩, ⟨jp, hjp⟩⟩ := positive_split K q hq hd
  let p := fun j => 0 < v.val j
  let T := {j : ι // ¬ p j}
  let S := {j : ι // p j}
  have hj0p : ¬ p j0 := by change ¬ 0 < v.val j0; simp [hj0]
  let : Nonempty T := ⟨⟨j0,hj0p⟩⟩
  let : Nonempty S := ⟨⟨jp,hjp⟩⟩
  have hTlt : Fintype.card T < Fintype.card ι :=
    Fintype.card_subtype_lt (x := jp) (not_not_intro hjp)
  have hSlt : Fintype.card S < Fintype.card ι := Fintype.card_subtype_lt hj0p
  have hqT : (fun j : T => q.val j) ∈ part K (fun j => ¬ p j) :=
    part_iff.mpr ⟨q.val, q.property, fun _ => rfl⟩
  obtain ⟨hT, hhT, hcostT⟩ := round hsaw T (part K (fun j => ¬ p j))
    (part H (fun j => ¬ p j)) (part_cast hKH _) ⟨_, hqT⟩ (fun j => hq j) (fun j => x j)
  obtain ⟨g, hg, hgT⟩ := part_iff.mp hhT
  have hqS : (fun j : S => v.val j) ∈ supported K p := supported_iff.mpr
    ⟨v.val, v.property, fun _ => rfl, fun j h => le_antisymm (le_of_not_gt h) (hv j)⟩
  obtain ⟨hS, hhS, hcostS⟩ := round hsaw S (supported K p) (supported H p)
    (supported_cast hKH _) ⟨_, hqS⟩ (fun j => j.property) (fun j => x j + g j)
  obtain ⟨f, hf, hfS, hfT⟩ := supported_iff.mp hhS
  refine ⟨g + f, H.add_mem hg hf, ?_⟩
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  have h1 : (∑ j : S, Int.fract (x j + (g + f) j)) = ∑ j : S, Int.fract ((x j + g j) + hS j) :=
    Finset.sum_congr rfl fun j _ => by change Int.fract (x j + (g j + f j)) = _; rw [hfS j, add_assoc]
  have h2 : (∑ j : T, Int.fract (x j + (g + f) j)) = ∑ j : T, Int.fract (x j + hT j) :=
    Finset.sum_congr rfl fun j _ => by change Int.fract (x j + (g j + f j)) = _; rw [hfT j j.property, add_zero, hgT j]
  rw [h1, h2]
  have hcNat : Fintype.card T + Fintype.card S = Fintype.card ι := by
    change Fintype.card {j // ¬ p j} + Fintype.card {j // p j} = _
    rw [Fintype.card_subtype_compl]
    exact Nat.sub_add_cancel (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)
  have hc : (Fintype.card T : ℝ) + (Fintype.card S : ℝ) = Fintype.card ι := by exact_mod_cast hcNat
  have hr : (finrank ℚ (part K fun j => ¬ p j) : ℝ) + (finrank ℚ (supported K p) : ℝ)
      = finrank ℚ K := by exact_mod_cast part_rank K p
  linarith
termination_by Fintype.card ι
decreasing_by all_goals first | exact hTlt | exact hSlt

end TaskS.B.Rounding
