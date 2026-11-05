import Research.Backfill.Paper7.EightCycleRank

/-! NEW SOURCE ONLY. Linear maps for the actual constrained unit recurrence.
All dimension arguments use the real Wmat kernel, without support tables. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

def unitResidual (p : Fin 8 → ℕ) : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun y i := y (prv 8 i)+y (nxt 8 i)-(1-(p i : ℝ))*y i
  map_add' y z := by funext i; simp only [Pi.add_apply]; ring
  map_smul' a y := by funext i; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring
#print axioms Paper7EightCycle.unitResidual

theorem unitResidual_apply (p : Fin 8 → ℕ) (y : Fin 8 → ℝ) (i : Fin 8) :
    unitResidual p y i = y (prv 8 i)+y (nxt 8 i)-(1-(p i : ℝ))*y i := rfl
#print axioms Paper7EightCycle.unitResidual_apply

theorem unitResidual_zero_off_support (p q : Fin 8 → ℕ) (y : Fin 8 → ℝ)
    (hy : y ∈ LinearMap.ker (Matrix.toLin' (Wmat 8 p q 1)))
    (i : Fin 8) (hi : i ∉ Kq 8 q) : unitResidual p y i = 0 := by
  have hh := Paper7Lemma22Gaps.kernel_recurrence_off_support 8 p q 1 y hy i hi
  rw [unitResidual_apply]
  nlinarith only [hh]
#print axioms Paper7EightCycle.unitResidual_zero_off_support

def supportResidualMap (p q : Fin 8 → ℕ) :
    LinearMap.ker (Matrix.toLin' (Wmat 8 p q 1)) →ₗ[ℝ]
      ({i : Fin 8 // i ∈ Kq 8 q} → ℝ) where
  toFun y i := unitResidual p y.1 i.1
  map_add' y z := by funext i; exact congrFun ((unitResidual p).map_add y.1 z.1) i.1
  map_smul' a y := by funext i; exact congrFun ((unitResidual p).map_smul a y.1) i.1
#print axioms Paper7EightCycle.supportResidualMap

theorem saturated_unit_punctured_solution (p q : Fin 8 → ℕ)
    (hd : deltaE 8 p q 1 = (Kq 8 q).card) (k : Fin 8) (hk : k ∈ Kq 8 q) :
    ∃ y : Fin 8 → ℝ, y ≠ 0 ∧ y k = 0 ∧ ∀ i, i ≠ k → unitResidual p y i = 0 := by
  let V := LinearMap.ker (Matrix.toLin' (Wmat 8 p q 1))
  let J := {i : Fin 8 // i ∈ (Kq 8 q).erase k}
  let F : V →ₗ[ℝ] (J → ℝ) :=
    (LinearMap.funLeft ℝ ℝ (fun i : J => i.1)).comp ((unitResidual p).comp V.subtype)
  have hdim : Module.finrank ℝ (J → ℝ) = (Kq 8 q).card-1 := by
    simp only [J,Module.finrank_fintype_fun_eq_card,Fintype.card_coe,Finset.card_erase_of_mem hk]
  have hex : ∃ y : V, F y = 0 ∧ y ≠ 0 := by
    by_contra hh
    have hz : ∀ y : V, F y = 0 → y = 0 := by
      intro y hy
      by_contra hne
      exact hh ⟨y,hy,hne⟩
    have hinj : Function.Injective F := by
      intro y z hyz
      apply sub_eq_zero.mp
      apply hz
      rw [map_sub,hyz,sub_self]
    have hle := F.finrank_le_finrank_of_injective hinj
    have hsource : Module.finrank ℝ V = (Kq 8 q).card := hd
    have hpos : 0 < (Kq 8 q).card := Finset.card_pos.mpr ⟨k,hk⟩
    rw [hsource,hdim] at hle
    omega
  obtain ⟨y,hy,hyn⟩ := hex
  refine ⟨y.1,?_,Paper7Lemma22Gaps.kernel_zero_on_support 8 p q 1 y.1 y.2 k hk,?_⟩
  · intro hz
    apply hyn
    exact Subtype.ext hz
  · intro i hik
    by_cases hi : i ∈ Kq 8 q
    · have hmem : i ∈ (Kq 8 q).erase k := Finset.mem_erase.mpr ⟨hik,hi⟩
      exact congrFun hy ⟨i,hmem⟩
    · exact unitResidual_zero_off_support p q y.1 y.2 i hi
#print axioms Paper7EightCycle.saturated_unit_punctured_solution

end Paper7EightCycle
