import Research.TaskR.A7.Kernel

namespace TaskR.A7.Interpret

open Kernel Challenge

set_option maxHeartbeats 900000

private theorem mul_ext {u v w : G} (he : ∀ t, act u t = act v (act w t)) : u = v*w :=
  Subtype.ext (Equiv.ext he)

private def edgeFin (i : Fin 2519) : Fin 2519 := ⟨edge i.val, Nat.mod_lt _ (by decide)⟩

variable (h : Good valid 0 2520)
include h

private theorem valid_at (i : Nat) (hi : i < 2520) : valid i = true := by
  simpa using h i hi

private theorem row_at (i : Nat) (hi : i < 2520) : rowOK i = true :=
  (Bool.and_eq_true_iff.mp (valid_at h i hi)).1

private theorem step_at (i : Fin 2519) : stepOK i = true := by
  have ht := (Bool.and_eq_true_iff.mp (valid_at h i.val (by omega))).2
  simpa [i.isLt] using ht

private theorem act_raw (i : Nat) (hi : i < 2520) (k : Fin 7) :
    act (vertex i) k = raw i k :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (row_at h i hi)).1 k

private theorem vertex_rank (i : Fin 2520) : rank (pack (act (vertex i))) = i.val := by
  rw [funext (act_raw h i i.isLt)]
  exact eq_of_beq (Bool.and_eq_true_iff.mp (row_at h i i.isLt)).2

noncomputable def ordering : Fin 2520 ≃ G :=
  Equiv.ofBijective (fun i => vertex i.val)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
      intro i j hij
      apply Fin.ext
      rw [← vertex_rank h i, ← vertex_rank h j]
      exact congrArg (fun g => rank (pack (act g))) hij, by
      change Fintype.card (Fin 2520) = Fintype.card (alternatingGroup (Fin 7))
      rw [card_alternatingGroup, Fintype.card_fin, Fintype.card_fin]
      decide⟩)

noncomputable def matching : Fin 2519 ≃ Fin 2519 := Equiv.ofBijective edgeFin
  ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
    intro i j hij
    have atIndex (k : Fin 2519) : Data.edgeBack (edgeFin k).val = k.val :=
      eq_of_beq (Bool.and_eq_true_iff.mp (step_at h k)).1
    apply Fin.ext
    rw [← atIndex i, ← atIndex j, hij], rfl⟩)

theorem first : ordering h 0 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro k
  fin_cases k <;> rfl

private theorem eq_mul_of_raw {i j k : Nat} (hi : i < 2520) (hj : j < 2520) (hk : k < 2520)
    (e : ∀ t, raw j (raw k t) = raw i t) : vertex i = vertex j * vertex k := by
  apply mul_ext
  intro t
  exact (act_raw h i hi t).trans ((e t).symm.trans
    (((congrArg (raw j) (act_raw h k hk t).symm).trans
      (act_raw h j hj (act (vertex k) t)).symm)))

theorem edges (i : Fin 2519) :
    difference (ordering h) i = ordering h (matching h i).succ ∨
    difference (ordering h) i = (ordering h (matching h i).succ)⁻¹ := by
  have hj : edge i.val < 2519 := Nat.mod_lt _ (by decide)
  have he := (Bool.and_eq_true_iff.mp (step_at h i)).2
  change (vertex i.val)⁻¹ * vertex (i.val+1) = vertex (edge i.val+1) ∨
    (vertex i.val)⁻¹ * vertex (i.val+1) = (vertex (edge i.val+1))⁻¹
  split at he
  · left
    apply inv_mul_eq_iff_eq_mul.mpr
    exact eq_mul_of_raw h (by omega) (by omega) (by omega) (of_decide_eq_true he)
  · right
    apply inv_mul_eq_iff_eq_mul.mpr
    apply eq_mul_inv_iff_mul_eq.mpr
    exact (eq_mul_of_raw h (by omega) (by omega) (by omega) (of_decide_eq_true he)).symm

end TaskR.A7.Interpret
