import Mathlib

set_option autoImplicit false

namespace RM714Timing

def monoVal (s x : Nat) : Bool := Nat.beq (x &&& s) s

def polyVal (L : List Nat) (x : Nat) : Bool :=
  L.foldl (fun b s => xor b (monoVal s x)) false

def weightNat (L : List Nat) : Nat := (List.range (2 ^ 14)).countP (fun x => polyVal L x)

def w354 : List Nat := [1931, 10612, 11380, 14452, 15494]

theorem weightNat_w354 : weightNat w354 = 354 := by decide +kernel

end RM714Timing
