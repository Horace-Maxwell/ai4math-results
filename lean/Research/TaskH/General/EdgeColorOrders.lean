import Research.TaskH.General.ColorCycle
import Research.TaskH.EdgeCycles

/-!
All rank permutations of k colors parameterize actual cyclic color orders.
For a following closed walk of length k, its first rank determines the full
permutation, giving the graph-independent multiplicity bound k.
Only the existing generic Follows / follows_getVert API is used from the
shared EdgeCycles parent; no fixed-color conclusion is invoked.
-/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph

variable {k : ℕ}

/-- Conjugate the k-color successor by the chosen rank permutation. -/
def orderedColorCycle (π : Equiv.Perm (Fin k)) : Equiv.Perm (Fin k) :=
  π.trans ((finRotate k).trans π.symm)

theorem orderedColorCycle_apply (π : Equiv.Perm (Fin k)) (a : Fin k) :
    π (orderedColorCycle π a) = finRotate k (π a) := by
  simp [orderedColorCycle]

theorem orderedColorCycle_no_two_step (hk : 3 ≤ k)
    (π : Equiv.Perm (Fin k)) (a : Fin k) :
    orderedColorCycle π (orderedColorCycle π a) ≠ a := by
  intro h
  have he := congrArg π h
  simp only [orderedColorCycle_apply] at he
  exact rotate_no_two_step hk (π a) he

theorem orderedColorCycle_no_fixed (hk : 3 ≤ k)
    (π : Equiv.Perm (Fin k)) (a : Fin k) : orderedColorCycle π a ≠ a := by
  intro h
  have he := congrArg π h
  rw [orderedColorCycle_apply] at he
  exact rotate_no_fixed hk (π a) he

variable {V : Type u} {G : SimpleGraph V}

theorem follows_orderedColorCycle_iff {x y : V} (p : G.Walk x y)
    (c : V → Fin k) (π : Equiv.Perm (Fin k)) :
    Follows p c (orderedColorCycle π) ↔
      Follows p (fun z => π (c z)) (finRotate k) := by
  constructor
  · intro h d hd
    change π (c d.snd) = finRotate k (π (c d.fst))
    rw [h d hd, orderedColorCycle_apply]
  · intro h d hd
    apply π.injective
    rw [orderedColorCycle_apply]
    exact h d hd

theorem follows_rotate_length_dvd (hk : 3 ≤ k) {x : V} (p : G.Walk x x)
    (c : V → Fin k) (hf : Follows p c (finRotate k)) : k ∣ p.length := by
  have hc := follows_getVert p c (finRotate k) hf p.length (le_refl _)
  rw [Walk.getVert_length] at hc
  exact (rotate_pow_fixed_iff hk (c x) p.length).mp hc.symm

theorem follows_orderedColorCycle_length_dvd (hk : 3 ≤ k) {x : V}
    (p : G.Walk x x) (c : V → Fin k) (π : Equiv.Perm (Fin k))
    (hf : Follows p c (orderedColorCycle π)) : k ∣ p.length := by
  exact follows_rotate_length_dvd hk p (fun z => π (c z))
    ((follows_orderedColorCycle_iff p c π).mp hf)

/-- Same first rank and same length-k traversal force the same full order. -/
theorem following_orders_eq_of_start (hk : 3 ≤ k) {x : V} (p : G.Walk x x)
    (hlen : p.length = k) (c : V → Fin k) (π ρ : Equiv.Perm (Fin k))
    (hπ : Follows p (fun z => π (c z)) (finRotate k))
    (hρ : Follows p (fun z => ρ (c z)) (finRotate k))
    (hstart : π (c x) = ρ (c x)) : π = ρ := by
  apply Equiv.ext
  intro a
  obtain ⟨i, hi⟩ := rotate_orbit_surjective hk (π (c x)) (π a)
  have hib : i.val ≤ p.length := by have := i.isLt; omega
  have hpi := follows_getVert p (fun z => π (c z)) (finRotate k) hπ i.val hib
  have hri := follows_getVert p (fun z => ρ (c z)) (finRotate k) hρ i.val hib
  have hca : c (p.getVert i.val) = a := π.injective (hpi.trans hi)
  have he : π (c (p.getVert i.val)) = ρ (c (p.getVert i.val)) := by
    rw [hpi, hri, hstart]
  simpa only [hca] using he

noncomputable def followingOrders {x : V} (p : G.Walk x x) (c : V → Fin k) :
    Finset (Equiv.Perm (Fin k)) := by
  classical
  exact Finset.univ.filter (fun π => Follows p (fun z => π (c z)) (finRotate k))

theorem mem_followingOrders {x : V} (p : G.Walk x x) (c : V → Fin k)
    (π : Equiv.Perm (Fin k)) : π ∈ followingOrders p c ↔
      Follows p (fun z => π (c z)) (finRotate k) := by
  classical
  simp only [followingOrders, Finset.mem_filter, Finset.mem_univ, true_and]

theorem followingOrders_card_le (hk : 3 ≤ k) {x : V} (p : G.Walk x x)
    (hlen : p.length = k) (c : V → Fin k) : (followingOrders p c).card ≤ k := by
  classical
  have hcard : (followingOrders p c).card ≤ (Finset.univ : Finset (Fin k)).card := by
    apply Finset.card_le_card_of_injOn (fun π => π (c x))
    · intro _π _hπ
      exact Finset.mem_univ _
    · intro π hπ ρ hρ he
      exact following_orders_eq_of_start hk p hlen c π ρ
        ((mem_followingOrders p c π).mp hπ) ((mem_followingOrders p c ρ).mp hρ) he
  simpa only [Finset.card_univ, Fintype.card_fin] using hcard

end TaskH.General

#print axioms TaskH.General.orderedColorCycle
#print axioms TaskH.General.orderedColorCycle_apply
#print axioms TaskH.General.orderedColorCycle_no_two_step
#print axioms TaskH.General.orderedColorCycle_no_fixed
#print axioms TaskH.General.follows_orderedColorCycle_iff
#print axioms TaskH.General.follows_rotate_length_dvd
#print axioms TaskH.General.follows_orderedColorCycle_length_dvd
#print axioms TaskH.General.following_orders_eq_of_start
#print axioms TaskH.General.followingOrders
#print axioms TaskH.General.mem_followingOrders
#print axioms TaskH.General.followingOrders_card_le
