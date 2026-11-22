import Research.TaskU.H5B.ChallengeB
import Research.TaskU.H5.CycPhase
import Research.TaskU.H5.CycPos

namespace TaskU.H5.Spectrum
abbrev Q5 := ZMod 5
abbrev R5 := Q5 × Q5 × Q5 × Q5
open Cyc5 (V)

def red (v : V) : R5 := (v.a,v.b,v.c,v.d)
def liftR (r : R5) : V := ⟨r.1.val,r.2.1.val,r.2.2.1.val,r.2.2.2.val⟩

theorem red_lift (r : R5) : red (liftR r) = r := by
  simp [red,liftR]

def rm (v w : R5) : R5 := red (Cyc5.mul (liftR v) (liftR w))
def rc (v : R5) : R5 := red (Cyc5.conj (liftR v))
def rs (v : R5) : Q5 := v.1+v.2.1+v.2.2.1+v.2.2.2

theorem red_mul (v w : V) : red (Cyc5.mul v w) = rm (red v) (red w) := by
  simp [rm,red,liftR,Cyc5.mul]

theorem red_conj (v : V) : red (Cyc5.conj v) = rc (red v) := by
  simp [rc,red,liftR,Cyc5.conj]

theorem red_congr {v w : V} : ChallengeB.congrFive v w ↔ red v = red w := by
  simp only [ChallengeB.congrFive,red,Prod.mk.injEq,ZMod.intCast_eq_intCast_iff]
  rfl
 
def phi : V := ⟨0,0,-1,-1⟩
def p3 : V := Cyc5.mul Cyc5.pi (Cyc5.mul Cyc5.pi Cyc5.pi)

def vp (x : V) : ℕ → V
  | 0 => Cyc5.scalar 1
  | n+1 => Cyc5.mul x (vp x n)

def unitRep (i : Q5) (j : Fin 20) : V := Cyc5.mul (Cyc5.rootAt i) (vp phi j.val)

def shape (d : Q5) : V := Cyc5.add (Cyc5.scalar 1) (Cyc5.mul (Cyc5.scalar (d.val:ℤ)) p3)

theorem unitRep_norm : ∀ i j, Cyc5.norm (unitRep i j) = 1 := by decide +kernel

theorem unit_inverse {u : V} (h : Cyc5.norm u=1) :
    ∃ v, Cyc5.mul u v = Cyc5.scalar 1 ∧ Cyc5.norm v = 1 := by
  let v := Cyc5.mul (Cyc5.conj u) (Cyc5.mul (Cyc5.sigma2 u) (Cyc5.sigma3 u))
  have he : Cyc5.mul u v = Cyc5.scalar 1 := by
    rw [← h, ← Cyc5.norm_prod, Cyc5.mul_assoc]
  refine ⟨v,he,?_⟩
  have hn := congrArg Cyc5.norm he
  rw [Cyc5.norm_mul,h,one_mul] at hn
  exact hn

theorem norm_of_unit {u v : V} (h : Cyc5.mul u v=Cyc5.scalar 1) : Cyc5.norm u=1 := by
  have hn := congrArg Cyc5.norm h
  rw [Cyc5.norm_mul] at hn
  change Cyc5.norm u*Cyc5.norm v=1 at hn
  have := Cyc5.norm_nonneg u
  exact (Int.mul_eq_one_iff_eq_one_or_neg_one.mp hn).elim (fun k => k.1) (fun k => by omega)

end TaskU.H5.Spectrum
