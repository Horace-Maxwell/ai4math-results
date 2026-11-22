import Research.TaskR.A7.Challenge
import Research.TaskR.A7.Data
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace TaskR.A7.Kernel

open Challenge

/-- A base-six digit selects a nonzero point and hence a genuine star transposition. -/
def point (v : Nat) : Fin 7 := (⟨v % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6).succ

def pair (v : Nat) : G :=
  ⟨Equiv.swap 0 (point v) * Equiv.swap 0 (point (v / 6)),
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
      ⟨0, _, (Fin.succ_ne_zero _).symm, rfl⟩ ⟨0, _, (Fin.succ_ne_zero _).symm, rfl⟩⟩

def word : Nat → Nat → G
  | 0, _ => 1
  | n + 1, v => pair v * word n (v / 36)

def vertex (i : Nat) : G := word 4 (Data.words i)

def act (g : G) (k : Fin 7) : Fin 7 := g.val k

def raw (i : Nat) (k : Fin 7) : Fin 7 :=
  ⟨((Data.images i >>> (3 * k.val)) % 8) % 7, Nat.mod_lt _ (by decide)⟩

def pack (f : Fin 7 → Fin 7) : Nat :=
  (f 0).val + 8 * ((f 1).val + 8 * ((f 2).val + 8 * ((f 3).val +
    8 * ((f 4).val + 8 * ((f 5).val + 8 * (f 6).val)))))

def rank (x : Nat) : Nat := Data.rankTable ((x + Data.shifts (x % 257)) % Data.hashMod)

def edge (i : Nat) : Nat := (Data.edgeTags i / 2) % 2519

def positive (i : Nat) : Bool := Data.edgeTags i % 2 == 0

def rowOK (i : Nat) : Bool :=
  (decide (∀ k : Fin 7, act (vertex i) k = raw i k)) &&
    (rank (pack (raw i)) == i)

def stepOK (i : Nat) : Bool :=
  (Data.edgeBack (edge i) == i) &&
    (if positive i then decide (∀ k : Fin 7, raw i (raw (edge i + 1) k) = raw (i+1) k)
     else decide (∀ k : Fin 7, raw (i+1) (raw (edge i + 1) k) = raw i k))

def valid (i : Nat) : Bool := rowOK i && (if i < 2519 then stepOK i else true)

def interval (p : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => p (start+n) && interval p start n

def Good (p : Nat → Bool) (s n : Nat) : Prop := ∀ i < n, p (s+i) = true

theorem interval_sound {p : Nat → Bool} {s n : Nat} (h : interval p s n = true) : Good p s n := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    obtain ⟨last,init⟩ := Bool.and_eq_true_iff.mp h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih init i hi
    · exact last

theorem merge {p : Nat → Bool} {s m n : Nat} (h : Good p s m) (k : Good p (s+m) n) :
    Good p s (m+n) := by
  intro i hi
  by_cases hm : i < m
  · exact h i hm
  · have := k (i-m) (by omega)
    convert this using 2
    omega

end TaskR.A7.Kernel
