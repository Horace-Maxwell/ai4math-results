import Research.TaskH.Seven.ColorCycle
import Research.TaskH.Seven.Definitions
import Research.TaskH.CycleOrientation

/-!
All 5040 linear orders parameterize genuine seven-color cyclic orders. A
fixed oriented seven-cycle has at most seven such parameters: its initial
rank determines the entire permutation. No graph-count premise occurs.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph

/-- Conjugate the fixed successor cycle by the chosen rank permutation. -/
def orderedColorCycle (π : Equiv.Perm (Fin 7)) : Equiv.Perm (Fin 7) :=
  π.trans ((finRotate 7).trans π.symm)

theorem orderedColorCycle_apply (π : Equiv.Perm (Fin 7)) (a : Fin 7) :
    π (orderedColorCycle π a) = finRotate 7 (π a) := by
  simp [orderedColorCycle]

theorem orderedColorCycle_no_two_step (π : Equiv.Perm (Fin 7)) (a : Fin 7) :
    orderedColorCycle π (orderedColorCycle π a) ≠ a := by
  intro h
  have he := congrArg π h
  simp only [orderedColorCycle_apply] at he
  exact rotate_no_two_step (π a) he

theorem orderedColorCycle_no_fixed (π : Equiv.Perm (Fin 7)) (a : Fin 7) :
    orderedColorCycle π a ≠ a := by
  intro h
  exact orderedColorCycle_no_two_step π a
    ((congrArg (orderedColorCycle π) h).trans h)

variable {V : Type u} {G : SimpleGraph V}

theorem follows_orderedColorCycle_iff {x y : V} (p : G.Walk x y)
    (c : V → Fin 7) (π : Equiv.Perm (Fin 7)) :
    Follows p c (orderedColorCycle π) ↔
      Follows p (fun z => π (c z)) (finRotate 7) := by
  constructor
  · intro h d hd
    change π (c d.snd) = finRotate 7 (π (c d.fst))
    rw [h d hd, orderedColorCycle_apply]
  · intro h d hd
    apply π.injective
    rw [orderedColorCycle_apply]
    exact h d hd

theorem follows_rotate_seven_length_dvd {x : V} (p : G.Walk x x)
    (c : V → Fin 7) (hf : Follows p c (finRotate 7)) : 7 ∣ p.length := by
  have hc := follows_getVert p c (finRotate 7) hf p.length (le_refl _)
  rw [Walk.getVert_length] at hc
  exact (rotate_pow_fixed_iff (c x) p.length).mp hc.symm

/-- A seven-element finite orbit calculation, independent of any graph. -/
theorem rotate_seven_orbit_surjective (a : Fin 7) :
    Function.Surjective (fun i : Fin 7 => ((finRotate 7) ^ i.val) a) := by
  have ht : ∀ a b : Fin 7, ∃ i : Fin 7, ((finRotate 7) ^ i.val) a = b := by
    decide +kernel
  exact ht a

/-- Same first rank and same traversal force the same entire color order. -/
theorem following_orders_eq_of_start {x : V} (p : G.Walk x x)
    (hlen : p.length = 7) (c : V → Fin 7) (π ρ : Equiv.Perm (Fin 7))
    (hπ : Follows p (fun z => π (c z)) (finRotate 7))
    (hρ : Follows p (fun z => ρ (c z)) (finRotate 7))
    (hstart : π (c x) = ρ (c x)) : π = ρ := by
  apply Equiv.ext
  intro a
  obtain ⟨i, hi⟩ := rotate_seven_orbit_surjective (π (c x)) (π a)
  have hib : i.val ≤ p.length := by have := i.isLt; omega
  have hpi := follows_getVert p (fun z => π (c z)) (finRotate 7) hπ i.val hib
  have hri := follows_getVert p (fun z => ρ (c z)) (finRotate 7) hρ i.val hib
  have hca : c (p.getVert i.val) = a := π.injective (hpi.trans hi)
  have he : π (c (p.getVert i.val)) = ρ (c (p.getVert i.val)) := by
    rw [hpi, hri, hstart]
  simpa only [hca] using he

noncomputable def followingOrders {x : V} (p : G.Walk x x) (c : V → Fin 7) :
    Finset (Equiv.Perm (Fin 7)) := by
  classical
  exact Finset.univ.filter (fun π => Follows p (fun z => π (c z)) (finRotate 7))

theorem mem_followingOrders {x : V} (p : G.Walk x x) (c : V → Fin 7)
    (π : Equiv.Perm (Fin 7)) : π ∈ followingOrders p c ↔
      Follows p (fun z => π (c z)) (finRotate 7) := by
  classical
  simp only [followingOrders, Finset.mem_filter, Finset.mem_univ, true_and]

theorem followingOrders_card_le_seven {x : V} (p : G.Walk x x)
    (hlen : p.length = 7) (c : V → Fin 7) : (followingOrders p c).card ≤ 7 := by
  classical
  have hcard : (followingOrders p c).card ≤ (Finset.univ : Finset (Fin 7)).card := by
    apply Finset.card_le_card_of_injOn (fun π => π (c x))
    · intro _π _hπ
      exact Finset.mem_univ _
    · intro π hπ ρ hρ he
      exact following_orders_eq_of_start p hlen c π ρ
        ((mem_followingOrders p c π).mp hπ) ((mem_followingOrders p c ρ).mp hρ) he
  simpa only [Finset.card_univ, Fintype.card_fin] using hcard

end TaskH.Seven

#print axioms TaskH.Seven.orderedColorCycle
#print axioms TaskH.Seven.orderedColorCycle_apply
#print axioms TaskH.Seven.orderedColorCycle_no_two_step
#print axioms TaskH.Seven.orderedColorCycle_no_fixed
#print axioms TaskH.Seven.follows_orderedColorCycle_iff
#print axioms TaskH.Seven.follows_rotate_seven_length_dvd
#print axioms TaskH.Seven.rotate_seven_orbit_surjective
#print axioms TaskH.Seven.following_orders_eq_of_start
#print axioms TaskH.Seven.followingOrders
#print axioms TaskH.Seven.mem_followingOrders
#print axioms TaskH.Seven.followingOrders_card_le_seven
