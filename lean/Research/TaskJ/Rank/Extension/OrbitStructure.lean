import Research.TaskJ.Rank.Extension.Challenge
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace TaskJ.Rank.Extension.Family

noncomputable section
open scoped Classical

variable {n : ℕ} (D : Family n)

theorem projection_surjective (i : Fin n) : Function.Surjective (D.projection i) := by
  intro y
  obtain ⟨x,hx⟩ := ZMod.castHom_surjective (D.divides i) y.toAdd
  exact ⟨Multiplicative.ofAdd x, congrArg Multiplicative.ofAdd hx⟩

@[simp] theorem action_point (i : Fin n) (x : D.Fiber i) (g : D.Actor) :
    D.action g ⟨i,x⟩ = ⟨i,D.projection i g * x⟩ := rfl

theorem stabilizer_eq (x : D.Point) : D.stabilizer x = (D.projection x.1).ker := by
  rcases x with ⟨i,x⟩
  ext g
  change (Sigma.mk i (D.projection i g * x) : D.Point) = ⟨i,x⟩ ↔ D.projection i g = 1
  simp

@[simp] theorem box_eq_ker (i : Fin n) : D.boxGroup i = (D.projection i).ker :=
  D.stabilizer_eq ⟨i,1⟩

theorem stabilizer_box (x : D.Point) : D.stabilizer x = D.boxGroup x.1 := by
  rw [D.stabilizer_eq, D.box_eq_ker]

theorem orbit_eq (x : D.Point) : D.orbit x = {y | y.1 = x.1} := by
  rcases x with ⟨i,x⟩
  ext ⟨j,y⟩
  constructor
  · rintro ⟨g,h⟩
    exact (congrArg Sigma.fst h).symm
  · intro h
    change j=i at h
    subst j
    obtain ⟨g,hg⟩ := D.projection_surjective i (y * x⁻¹)
    refine ⟨g,?_⟩
    simp [hg]

def weylFiber (i : Fin n) : D.Weyl i ≃* D.Fiber i := by
  unfold Weyl
  rw [D.box_eq_ker]
  exact QuotientGroup.quotientKerEquivOfSurjective _ (D.projection_surjective i)

theorem fiber_card (i : Fin n) : Nat.card (D.Fiber i) = (D.width i : ℕ) := by
  change Nat.card (ZMod (D.width i : ℕ)) = _
  exact Nat.card_zmod _

theorem weyl_card (i : Fin n) : Nat.card (D.Weyl i) = (D.width i : ℕ) :=
  (Nat.card_congr (D.weylFiber i).toEquiv).trans (D.fiber_card i)

theorem box_injective (hw : Function.Injective D.width) : Function.Injective D.boxGroup := by
  intro i j h
  apply hw
  apply Subtype.ext
  have eq := congrArg (fun H : Subgroup D.Actor => Nat.card (D.Actor ⧸ H)) h
  exact (D.weyl_card i).symm.trans (eq.trans (D.weyl_card j))

theorem action_injective_of_common_ker
    (hk : ∀ g : D.Actor, (∀ i, D.projection i g = 1) → g = 1) : Function.Injective D.action := by
  apply (injective_iff_map_eq_one _).2
  intro g hg
  apply hk
  intro i
  have h := DFunLike.congr_fun (show D.action g = 1 from hg) (⟨i,1⟩ : D.Point)
  have hh : (Sigma.mk i (D.projection i g * 1) : D.Point) = ⟨i,1⟩ := h
  simpa using hh

def boxMap (i : Fin n) : D.boxes := ⟨D.boxGroup i, ⟨⟨i,1⟩,rfl⟩⟩

def boxesEquiv (hw : Function.Injective D.width) : Fin n ≃ D.boxes :=
  Equiv.ofBijective D.boxMap ⟨
    fun _ _ h => D.box_injective hw (congrArg Subtype.val h),
    fun ⟨_,x,hx⟩ => ⟨x.1,Subtype.ext ((D.stabilizer_box x).symm.trans hx)⟩⟩

theorem r_eq (hw : Function.Injective D.width) : D.r = n :=
  (Nat.card_congr (D.boxesEquiv hw).symm).trans (Nat.card_fin n)

theorem orbit_subsingleton (hw : Function.Injective D.width) (H : D.boxes) :
    Subsingleton (D.orbitsInBox H.val) := by
  constructor
  rintro ⟨A,⟨x,hx⟩,rfl⟩ ⟨B,⟨y,hy⟩,rfl⟩
  apply Subtype.ext
  have hi : x.1 = y.1 := D.box_injective hw
    ((D.stabilizer_box x).symm.trans (hx.trans (hy.symm.trans (D.stabilizer_box y))))
  simp [orbit_eq,hi]

theorem orbit_one (hw : Function.Injective D.width) (H : D.boxes) :
    Nat.card (D.orbitsInBox H.val) = 1 := by
  apply (Nat.card_eq_one_iff_unique).2
  refine ⟨D.orbit_subsingleton hw H,?_⟩
  obtain ⟨x,hx⟩ := H.property
  exact ⟨⟨D.orbit x,⟨⟨x,hx⟩,rfl⟩⟩⟩

theorem kappa_eq (hw : Function.Injective D.width) : D.kappa = n := by
  let e : {H : D.boxes // Nat.card (D.orbitsInBox H.val) = 1} ≃ D.boxes :=
    Equiv.subtypeUnivEquiv (D.orbit_one hw)
  exact (Nat.card_congr e).trans (D.r_eq hw)

theorem capitalLambda_eq (hn : 0 < n) (hw : Function.Injective D.width)
    (hwide : ∀ i, 1 < (D.width i : ℕ)) : D.capitalLambda = 0 := by
  unfold capitalLambda
  split
  · rename_i h
    exfalso
    rcases h with ⟨_,ha⟩|⟨H,hH⟩
    · let i : Fin n := ⟨0,hn⟩
      have : Subsingleton (D.Weyl i) := ha (D.boxMap i)
      have hh : Nat.card (D.Weyl i) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
      rw [D.weyl_card] at hh
      have := hwide i
      omega
    · rw [D.orbit_one hw H] at hH
      omega
  · rfl

end
end TaskJ.Rank.Extension.Family
