import Research.TaskU.H5.Profile
import Research.TaskU.H5.CycNorm

namespace TaskU.H5.Spectrum
open Finset
open scoped BigOperators

def seedA (s : Fin 5) : ℤ := ![1,-1,2,-2,5] s

def posOne (a b : F) : ℤ :=
  if (a,b) ∈ ({(0,0),(0,1),(0,2),(1,0),(4,1)} : Finset (F × F)) then 1 else 0

def posTwo (a b : F) : ℤ :=
  if (a,b) ∈ ({(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(4,0),(4,1),(4,4)}
    : Finset (F × F)) then 1 else 0

def posFive (a b : F) : ℤ :=
  1 - (if a=0 ∧ (b=0 ∨ b=1) then 1 else 0) + (if b=0 ∧ (a=1 ∨ a=4) then 1 else 0)

def seed (s : Fin 5) (a b : F) : ℤ :=
  ![posOne a b, -posOne a (-b), posTwo a b, -posTwo a (-b), posFive a b] s

def abRay (P : F → F → ℤ) (u v : F) : Cyc5.V :=
  profile fun r => ∑ a : F, ∑ b : F, if u*a+v*b=r then P a b else 0

def abAug (P : F → F → ℤ) : ℤ := ∑ a, ∑ b, P a b

theorem seedData : ∀ s : Fin 5, abAug (seed s) = 5 * seedA s ∧
    Cyc5.norm (abRay (seed s) 1 0) = 25 ∧
    ∀ j : F, Cyc5.norm (abRay (seed s) j 1) = 5 := by decide +kernel

theorem seed_residues : ∀ r : F, ∃ s : Fin 5, (seedA s : F) = r := by decide +kernel

end TaskU.H5.Spectrum
