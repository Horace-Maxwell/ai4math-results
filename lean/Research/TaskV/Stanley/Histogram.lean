import Research.TaskV.Stanley.ProfileDefs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

namespace StanleyContinuation

noncomputable section
open Finset

def histogram {V C : Type*} (f : V → C) (c : C) : ℕ := Nat.card {v // f v = c}

def Proper {V C : Type*} (G : SimpleGraph V) (f : V → C) : Prop :=
  ∀ u v, G.Adj u v → f u ≠ f v

def ProperAssignments {V : Type*} (G : SimpleGraph V) (C : Type*) :=
  {f : V → C // Proper G f}

instance {V C : Type*} [Finite V] [Finite C] (G : SimpleGraph V) :
    Finite (ProperAssignments G C) := by
  unfold ProperAssignments
  infer_instance

theorem hist_total {V C : Type*} [Fintype V] [Fintype C] (f : V → C) :
    ∑ c, histogram f c = Fintype.card V := by
  classical
  simpa [histogram, Nat.card_eq_fintype_card, Fintype.card_sigma] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv f)

theorem injective_histogram {n : ℕ} (i : Fin n) :
    histogram (id : Fin n → Fin n) i = 1 := by
  classical
  exact Nat.card_eq_one_iff_exists.mpr ⟨⟨i,rfl⟩, fun y => Subtype.ext y.property⟩

theorem self_coefficient_pos {n : ℕ} (G : SimpleGraph (Fin n)) :
    0 < colorCoefficient G n (fun _ => 1) := by
  classical
  unfold colorCoefficient
  rw [Nat.card_pos_iff]
  constructor
  · exact ⟨⟨id, (fun _ _ h => h.ne), fun c => injective_histogram c⟩⟩
  · infer_instance

theorem sameOrder_of_sameCSF {n m : ℕ} {G : SimpleGraph (Fin n)}
    {H : SimpleGraph (Fin m)} (h : SameCSF G H) : n = m := by
  classical
  have hp := self_coefficient_pos G
  rw [h n (fun _ => 1)] at hp
  obtain ⟨⟨f, hf⟩, _⟩ := Nat.card_pos_iff.mp hp
  have hsum := hist_total f
  simpa only [show histogram f = fun _ => 1 from funext hf.2, sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] using hsum

private def histFiberEquiv {n k : ℕ} (G : SimpleGraph (Fin n)) (s : Fin k → ℕ) :
    {f : ProperAssignments G (Fin k) // histogram f.1 = s} ≃
      {f : Fin n → Fin k // Proper G f ∧ ∀ c, histogram f c = s c} where
  toFun f := ⟨f.1.1, f.1.2, congrFun f.2⟩
  invFun f := ⟨⟨f.1, f.2.1⟩, funext f.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sameCSF_iff_histEquiv {n m : ℕ} {G : SimpleGraph (Fin n)}
    {H : SimpleGraph (Fin m)} (h : SameCSF G H) (k : ℕ) :
    ∃ e : ProperAssignments G (Fin k) ≃ ProperAssignments H (Fin k),
      ∀ f, histogram (e f).1 = histogram f.1 := by
  classical
  have hcard (s : Fin k → ℕ) :
      Nat.card {f : ProperAssignments G (Fin k) // histogram f.1 = s} =
        Nat.card {f : ProperAssignments H (Fin k) // histogram f.1 = s} := by
    rw [Nat.card_congr (histFiberEquiv G s), Nat.card_congr (histFiberEquiv H s)]
    exact h k s
  let fibers (s : Fin k → ℕ) :
      {f : ProperAssignments G (Fin k) // histogram f.1 = s} ≃
        {f : ProperAssignments H (Fin k) // histogram f.1 = s} :=
    Classical.choice (Finite.card_eq.mp (hcard s))
  exact ⟨Equiv.ofFiberEquiv fibers, Equiv.ofFiberEquiv_map fibers⟩

end
end StanleyContinuation
