import Research.TaskJ.Rank.Extension.Challenge
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Prod

namespace TaskJ.Rank.Extension.CRT

open scoped BigOperators

noncomputable section

variable {n : ℕ}

private def separate (A B : Fin n → ℕ) :
    (∀ i, ZMod (A i) × ZMod (B i)) ≃+ (∀ i, ZMod (A i)) × (∀ i, ZMod (B i)) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun z i := (z.1 i,z.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Split each row by the coprime incoming/outgoing factors, then collect each column by CRT. -/
def familySquare (D : Family n) (A B : Fin n → ℕ)
    (width : ∀ i, (D.width i : ℕ) = A i * B i)
    (prodA : ∏ i, A i = (D.modulus : ℕ)) (prodB : ∏ i, B i = (D.modulus : ℕ))
    (hA : Pairwise (fun i j => (A i).Coprime (A j)))
    (hB : Pairwise (fun i j => (B i).Coprime (B j))) (hAB : ∀ i, (A i).Coprime (B i)) :
    (∀ i, D.Fiber i) ≃* D.Actor × D.Actor := by
  let row := RingEquiv.piCongrRight (fun i => (ZMod.ringEquivCongr (width i)).trans
    (ZMod.chineseRemainder (hAB i)))
  let colA := (ZMod.prodEquivPi A hA).symm.trans (ZMod.ringEquivCongr prodA)
  let colB := (ZMod.prodEquivPi B hB).symm.trans (ZMod.ringEquivCongr prodB)
  let result := (row.toAddEquiv.trans (separate A B)).trans
    (AddEquiv.prodCongr colA.toAddEquiv colB.toAddEquiv)
  exact result.toMultiplicative

theorem residues_determine (m : ℕ) (A : Fin n → ℕ) (hprod : ∏ i, A i = m)
    (hcop : Pairwise (fun i j => (A i).Coprime (A j))) (x y : ZMod m)
    (h : ∀ i (hd : A i ∣ m), ZMod.castHom hd (ZMod (A i)) x = ZMod.castHom hd (ZMod (A i)) y) :
    x = y := by
  subst m
  apply (ZMod.prodEquivPi A hcop).injective
  funext i
  simp only [ZMod.prodEquivPi_apply]
  exact h i _

theorem projection_injective (D : Family n) (A : Fin n → ℕ)
    (hprod : ∏ i, A i = (D.modulus : ℕ)) (hcop : Pairwise (fun i j => (A i).Coprime (A j)))
    (hd : ∀ i, A i ∣ (D.width i : ℕ)) :
    Function.Injective (fun g : D.Actor => fun i => D.projection i g) := by
  intro x y he
  change Multiplicative.toAdd x = Multiplicative.toAdd y
  apply residues_determine (D.modulus : ℕ) A hprod hcop
  intro i _
  have hr := congrFun he i
  change ZMod.castHom (D.divides i) (ZMod (D.width i : ℕ)) _ =
    ZMod.castHom (D.divides i) (ZMod (D.width i : ℕ)) _ at hr
  have hs := congrArg (ZMod.castHom (hd i) (ZMod (A i))) hr
  simpa only [← RingHom.comp_apply, ZMod.castHom_comp] using hs

theorem faithful (D : Family n) (A : Fin n → ℕ)
    (hprod : ∏ i, A i = (D.modulus : ℕ)) (hcop : Pairwise (fun i j => (A i).Coprime (A j)))
    (hd : ∀ i, A i ∣ (D.width i : ℕ)) : Function.Injective D.action := by
  intro x y he
  apply projection_injective D A hprod hcop hd
  funext i
  have hp := congrArg (fun f : Equiv.Perm D.Point => f ⟨i,1⟩) he
  change Sigma.mk i (D.projection i x * 1) = Sigma.mk i (D.projection i y * 1) at hp
  simpa using hp

end
end TaskJ.Rank.Extension.CRT
