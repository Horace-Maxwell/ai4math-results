import Research.TaskJ.Rank.Extension.Challenge
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

namespace TaskJ.Rank.Extension.Arithmetic

noncomputable section
open scoped BigOperators

variable {n : ℕ}

/-- Distinct directed edges receive distinct primes. Using 1 on the diagonal
lets rows and columns range over the same finite index type. -/
def label (i j : Fin n) : ℕ :=
  if i = j then 1 else Nat.nth Nat.Prime (Nat.pair i.val j.val)

theorem label_prime {i j : Fin n} (h : i ≠ j) : (label i j).Prime := by
  rw [label, ite_eq_right h]
  exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _

theorem label_pos (i j : Fin n) : 0 < label i j := by
  by_cases h : i = j
  · simp [label,h]
  · exact (label_prime h).pos

private theorem labels_coprime {i j u v : Fin n} (hne : (i,j) ≠ (u,v)) :
    (label i j).Coprime (label u v) := by
  by_cases h : i = j
  · simp [label,h]
  by_cases h' : u = v
  · simp [label,h']
  apply (Nat.coprime_primes (label_prime h) (label_prime h')).2
  simp only [label, ite_eq_right h, ite_eq_right h']
  intro he
  have hm := Nat.pair_eq_pair.mp (Nat.nth_injective Nat.infinite_setOfPred_prime he)
  exact hne (Prod.ext (Fin.ext hm.1) (Fin.ext hm.2))

def outgoing (i : Fin n) : ℕ := ∏ j : Fin n, label i j

def incoming (i : Fin n) : ℕ := ∏ j : Fin n, label j i

def modulus (n : ℕ) : ℕ := ∏ i : Fin n, outgoing i

theorem outgoing_pos (i : Fin n) : 0 < outgoing i :=
  Finset.prod_pos fun j _ => label_pos i j

theorem incoming_pos (i : Fin n) : 0 < incoming i :=
  Finset.prod_pos fun j _ => label_pos j i

theorem modulus_pos (n : ℕ) : 0 < modulus n :=
  Finset.prod_pos fun i _ => outgoing_pos i

theorem prod_incoming (n : ℕ) : (∏ i : Fin n, incoming i) = modulus n :=
  Finset.prod_comm

theorem outgoing_pairwise (n : ℕ) :
    Pairwise (fun i j : Fin n => (outgoing i).Coprime (outgoing j)) := by
  intro i j hij
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro u
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro v
  exact labels_coprime (fun h => hij (congrArg Prod.fst h))

theorem incoming_pairwise (n : ℕ) :
    Pairwise (fun i j : Fin n => (incoming i).Coprime (incoming j)) := by
  intro i j hij
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro u
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro v
  exact labels_coprime (fun h => hij (congrArg Prod.snd h))

theorem cross_coprime (i : Fin n) : (outgoing i).Coprime (incoming i) := by
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro u
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro v
  by_cases h : i = u
  · simp [label,h]
  · exact labels_coprime (fun he => h ((congrArg Prod.snd he).symm))

private theorem width_dvd (i : Fin n) : outgoing i * incoming i ∣ modulus n := by
  apply (cross_coprime i).mul_dvd_of_dvd_of_dvd
  · exact Finset.dvd_prod_of_mem outgoing (Finset.mem_univ i)
  · rw [← prod_incoming]
    exact Finset.dvd_prod_of_mem incoming (Finset.mem_univ i)

def family (n : ℕ) : Family n where
  modulus := ⟨modulus n, modulus_pos n⟩
  width i := ⟨outgoing i * incoming i, Nat.mul_pos (outgoing_pos i) (incoming_pos i)⟩
  divides := width_dvd

theorem width_eq (i : Fin n) :
    ((family n).width i : ℕ) = outgoing i * incoming i := rfl

theorem prod_out (n : ℕ) :
    (∏ i : Fin n, outgoing i) = ((family n).modulus : ℕ) := rfl

theorem prod_in (n : ℕ) :
    (∏ i : Fin n, incoming i) = ((family n).modulus : ℕ) := prod_incoming n

private theorem from_dvd (i j : Fin n) : label i j ∣ ((family n).width i : ℕ) :=
  dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (label i) (Finset.mem_univ j)) _

private theorem to_dvd (i j : Fin n) : label i j ∣ ((family n).width j : ℕ) :=
  dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun t => label t j) (Finset.mem_univ i)) _

private theorem third {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  by_contra! h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i,j} := by
    intro x _
    by_cases hxi : x = i
    · simp [hxi]
    · simp [h x hxi]
  have hcard := Finset.card_le_card hsub
  have htwo := Finset.card_insert_le i ({j} : Finset (Fin n))
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at *
  omega

theorem width_gt_one (hn : 3 ≤ n) (i : Fin n) : 1 < ((family n).width i : ℕ) := by
  obtain ⟨k,hki,_⟩ := third hn i i
  exact (label_prime hki.symm).one_lt.trans_le
    (Nat.le_of_dvd ((family n).width i).property (from_dvd i k))

theorem width_non_coprime {i j : Fin n} (h : i ≠ j) :
    ¬ Nat.Coprime ((family n).width i : ℕ) ((family n).width j : ℕ) := by
  intro hc
  exact (label_prime h).ne_one (Nat.eq_one_of_dvd_coprimes hc (from_dvd i j) (to_dvd i j))

theorem width_injective (hn : 3 ≤ n) : Function.Injective (family n).width := by
  intro i j hij
  by_contra hne
  obtain ⟨k,hki,hkj⟩ := third hn i j
  have hr : (label i k).Coprime (outgoing j) :=
    Nat.coprime_fintype_prod_right_iff.mpr fun t => labels_coprime (fun e => hne (congrArg Prod.fst e))
  have hs : (label i k).Coprime (incoming j) :=
    Nat.coprime_fintype_prod_right_iff.mpr fun t => labels_coprime (fun e => hkj (congrArg Prod.snd e))
  have hd := from_dvd i k
  rw [hij] at hd
  exact (label_prime hki.symm).ne_one ((hr.mul_right hs).eq_one_of_dvd hd)

end
end TaskJ.Rank.Extension.Arithmetic
