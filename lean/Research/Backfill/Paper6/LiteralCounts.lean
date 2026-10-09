import Research.Backfill.Paper6.LiteralNumeric

set_option autoImplicit false

namespace Paper6LiteralLouWang

def vennWeight3 (r1 r2 r3 r4 r5 r6 r7 : ℕ) : ℤ :=
  (1 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r3 + r5 + r7)) +
    (1 : ℤ) * (2 : ℤ) ^ (12 - (r2 + r3 + r6 + r7)) +
    (-2 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r2 + r3 + r5 + r6 + r7)) +
    (1 : ℤ) * (2 : ℤ) ^ (12 - (r4 + r5 + r6 + r7)) +
    (-2 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r3 + r4 + r5 + r6 + r7)) +
    (-2 : ℤ) * (2 : ℤ) ^ (12 - (r2 + r3 + r4 + r5 + r6 + r7)) +
    (4 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r2 + r3 + r4 + r5 + r6 + r7))

def countBounds3 (r1 r2 r3 r4 r5 r6 r7 : ℕ) : Prop :=
  r1 + r2 + r3 + r4 + r5 + r6 + r7 ≤ 12 ∧
  r1 + r3 + r5 + r7 ≤ 6 ∧
  r2 + r3 + r6 + r7 ≤ 6 ∧
  r4 + r5 + r6 + r7 ≤ 6

def suffix3 (r7 r6 : ℕ) : Bool :=
  allLe (min (12 - (r7 + r6)) (min (6 - (r7)) ((6 - (r7 + r6))))) fun r5 =>
  allLe (min (12 - (r7 + r6 + r5)) (min (6 - (r7 + r5)) ((6 - (r7 + r6))))) fun r3 =>
  allLe (min (12 - (r7 + r6 + r5 + r3)) ((6 - (r7 + r6 + r5)))) fun r4 =>
  allLe (min (12 - (r7 + r6 + r5 + r3 + r4)) ((6 - (r7 + r6 + r3)))) fun r2 =>
  allLe (min (12 - (r7 + r6 + r5 + r3 + r4 + r2)) ((6 - (r7 + r5 + r3)))) fun r1 =>
    okayWeight (vennWeight3 r1 r2 r3 r4 r5 r6 r7)

def checkCounts3 : Bool :=
  allLe (min (12 - (0)) (min (6 - (0)) (min (6 - (0)) ((6 - (0)))))) fun r7 =>
  allLe (min (12 - (r7)) (min (6 - (r7)) ((6 - (r7))))) fun r6 =>
    suffix3 r7 r6

theorem counts_complete3 (r1 r2 r3 r4 r5 r6 r7 : ℕ)
    (hb : countBounds3 r1 r2 r3 r4 r5 r6 r7) (hc : checkCounts3 = true) :
    okayWeight (vennWeight3 r1 r2 r3 r4 r5 r6 r7) = true := by
  rcases hb with ⟨h0, h1, h2, h3⟩
  unfold checkCounts3 at hc
  have selected0 := allLe_sound _ _ hc r7 (by omega)
  have selected1 := allLe_sound _ _ selected0 r6 (by omega)
  unfold suffix3 at selected1
  have selected2 := allLe_sound _ _ selected1 r5 (by omega)
  have selected3 := allLe_sound _ _ selected2 r3 (by omega)
  have selected4 := allLe_sound _ _ selected3 r4 (by omega)
  have selected5 := allLe_sound _ _ selected4 r2 (by omega)
  have selected6 := allLe_sound _ _ selected5 r1 (by omega)
  exact selected6

def vennWeight4 (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : ℕ) : ℤ :=
  (1 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r3 + r5 + r7 + r9 + r11 + r13 + r15)) +
    (1 : ℤ) * (2 : ℤ) ^ (12 - (r2 + r3 + r6 + r7 + r10 + r11 + r14 + r15)) +
    (-2 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r2 + r3 + r5 + r6 + r7 + r9 + r10 + r11 + r13 + r14 + r15)) +
    (1 : ℤ) * (2 : ℤ) ^ (12 - (r4 + r5 + r6 + r7 + r12 + r13 + r14 + r15)) +
    (-2 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r3 + r4 + r5 + r6 + r7 + r9 + r11 + r12 + r13 + r14 + r15)) +
    (-2 : ℤ) * (2 : ℤ) ^ (12 - (r2 + r3 + r4 + r5 + r6 + r7 + r10 + r11 + r12 + r13 + r14 + r15)) +
    (4 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r2 + r3 + r4 + r5 + r6 + r7 + r9 + r10 + r11 + r12 + r13 + r14 + r15)) +
    (1 : ℤ) * (2 : ℤ) ^ (12 - (r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15)) +
    (-2 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r3 + r5 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15)) +
    (-2 : ℤ) * (2 : ℤ) ^ (12 - (r2 + r3 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15)) +
    (4 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r2 + r3 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15)) +
    (-2 : ℤ) * (2 : ℤ) ^ (12 - (r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15)) +
    (4 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15)) +
    (4 : ℤ) * (2 : ℤ) ^ (12 - (r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15)) +
    (-8 : ℤ) * (2 : ℤ) ^ (12 - (r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15))

def countBounds4 (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : ℕ) : Prop :=
  r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 ≤ 12 ∧
  r1 + r3 + r5 + r7 + r9 + r11 + r13 + r15 ≤ 6 ∧
  r2 + r3 + r6 + r7 + r10 + r11 + r14 + r15 ≤ 6 ∧
  r4 + r5 + r6 + r7 + r12 + r13 + r14 + r15 ≤ 6 ∧
  r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 ≤ 6

def suffix4 (r15 r14 r13 r11 r7 : ℕ) : Bool :=
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7)) (min (6 - (r15 + r14 + r13 + r7)) ((6 - (r15 + r14 + r13 + r11))))) fun r12 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12)) (min (6 - (r15 + r14 + r11 + r7)) ((6 - (r15 + r14 + r13 + r11 + r12))))) fun r10 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10)) (min (6 - (r15 + r13 + r11 + r7)) ((6 - (r15 + r14 + r13 + r11 + r12 + r10))))) fun r9 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9)) (min (6 - (r15 + r14 + r11 + r7 + r10)) ((6 - (r15 + r14 + r13 + r7 + r12))))) fun r6 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6)) (min (6 - (r15 + r13 + r11 + r7 + r9)) ((6 - (r15 + r14 + r13 + r7 + r12 + r6))))) fun r5 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5)) (min (6 - (r15 + r13 + r11 + r7 + r9 + r5)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6))))) fun r3 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3)) ((6 - (r15 + r14 + r13 + r11 + r12 + r10 + r9)))) fun r8 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8)) ((6 - (r15 + r14 + r13 + r7 + r12 + r6 + r5)))) fun r4 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6 + r3)))) fun r2 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4 + r2)) ((6 - (r15 + r13 + r11 + r7 + r9 + r5 + r3)))) fun r1 =>
    okayWeight (vennWeight4 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)

def suffix4Depth6 (r15 r14 r13 r11 r7 r12 : ℕ) : Bool :=
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12)) (min (6 - (r15 + r14 + r11 + r7)) ((6 - (r15 + r14 + r13 + r11 + r12))))) fun r10 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10)) (min (6 - (r15 + r13 + r11 + r7)) ((6 - (r15 + r14 + r13 + r11 + r12 + r10))))) fun r9 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9)) (min (6 - (r15 + r14 + r11 + r7 + r10)) ((6 - (r15 + r14 + r13 + r7 + r12))))) fun r6 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6)) (min (6 - (r15 + r13 + r11 + r7 + r9)) ((6 - (r15 + r14 + r13 + r7 + r12 + r6))))) fun r5 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5)) (min (6 - (r15 + r13 + r11 + r7 + r9 + r5)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6))))) fun r3 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3)) ((6 - (r15 + r14 + r13 + r11 + r12 + r10 + r9)))) fun r8 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8)) ((6 - (r15 + r14 + r13 + r7 + r12 + r6 + r5)))) fun r4 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6 + r3)))) fun r2 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4 + r2)) ((6 - (r15 + r13 + r11 + r7 + r9 + r5 + r3)))) fun r1 =>
    okayWeight (vennWeight4 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)

def suffix4Depth7 (r15 r14 r13 r11 r7 r12 r10 : ℕ) : Bool :=
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10)) (min (6 - (r15 + r13 + r11 + r7)) ((6 - (r15 + r14 + r13 + r11 + r12 + r10))))) fun r9 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9)) (min (6 - (r15 + r14 + r11 + r7 + r10)) ((6 - (r15 + r14 + r13 + r7 + r12))))) fun r6 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6)) (min (6 - (r15 + r13 + r11 + r7 + r9)) ((6 - (r15 + r14 + r13 + r7 + r12 + r6))))) fun r5 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5)) (min (6 - (r15 + r13 + r11 + r7 + r9 + r5)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6))))) fun r3 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3)) ((6 - (r15 + r14 + r13 + r11 + r12 + r10 + r9)))) fun r8 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8)) ((6 - (r15 + r14 + r13 + r7 + r12 + r6 + r5)))) fun r4 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6 + r3)))) fun r2 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4 + r2)) ((6 - (r15 + r13 + r11 + r7 + r9 + r5 + r3)))) fun r1 =>
    okayWeight (vennWeight4 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)

def suffix4Depth8 (r15 r14 r13 r11 r7 r12 r10 r9 : ℕ) : Bool :=
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9)) (min (6 - (r15 + r14 + r11 + r7 + r10)) ((6 - (r15 + r14 + r13 + r7 + r12))))) fun r6 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6)) (min (6 - (r15 + r13 + r11 + r7 + r9)) ((6 - (r15 + r14 + r13 + r7 + r12 + r6))))) fun r5 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5)) (min (6 - (r15 + r13 + r11 + r7 + r9 + r5)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6))))) fun r3 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3)) ((6 - (r15 + r14 + r13 + r11 + r12 + r10 + r9)))) fun r8 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8)) ((6 - (r15 + r14 + r13 + r7 + r12 + r6 + r5)))) fun r4 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6 + r3)))) fun r2 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4 + r2)) ((6 - (r15 + r13 + r11 + r7 + r9 + r5 + r3)))) fun r1 =>
    okayWeight (vennWeight4 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)

def suffix4Depth9 (r15 r14 r13 r11 r7 r12 r10 r9 r6 : ℕ) : Bool :=
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6)) (min (6 - (r15 + r13 + r11 + r7 + r9)) ((6 - (r15 + r14 + r13 + r7 + r12 + r6))))) fun r5 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5)) (min (6 - (r15 + r13 + r11 + r7 + r9 + r5)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6))))) fun r3 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3)) ((6 - (r15 + r14 + r13 + r11 + r12 + r10 + r9)))) fun r8 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8)) ((6 - (r15 + r14 + r13 + r7 + r12 + r6 + r5)))) fun r4 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6 + r3)))) fun r2 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4 + r2)) ((6 - (r15 + r13 + r11 + r7 + r9 + r5 + r3)))) fun r1 =>
    okayWeight (vennWeight4 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)

def suffix4Depth10 (r15 r14 r13 r11 r7 r12 r10 r9 r6 r5 : ℕ) : Bool :=
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5)) (min (6 - (r15 + r13 + r11 + r7 + r9 + r5)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6))))) fun r3 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3)) ((6 - (r15 + r14 + r13 + r11 + r12 + r10 + r9)))) fun r8 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8)) ((6 - (r15 + r14 + r13 + r7 + r12 + r6 + r5)))) fun r4 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4)) ((6 - (r15 + r14 + r11 + r7 + r10 + r6 + r3)))) fun r2 =>
  allLe (min (12 - (r15 + r14 + r13 + r11 + r7 + r12 + r10 + r9 + r6 + r5 + r3 + r8 + r4 + r2)) ((6 - (r15 + r13 + r11 + r7 + r9 + r5 + r3)))) fun r1 =>
    okayWeight (vennWeight4 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)

def checkCounts4 : Bool :=
  allLe (min (12 - (0)) (min (6 - (0)) (min (6 - (0)) (min (6 - (0)) ((6 - (0))))))) fun r15 =>
  allLe (min (12 - (r15)) (min (6 - (r15)) (min (6 - (r15)) ((6 - (r15)))))) fun r14 =>
  allLe (min (12 - (r15 + r14)) (min (6 - (r15)) (min (6 - (r15 + r14)) ((6 - (r15 + r14)))))) fun r13 =>
  allLe (min (12 - (r15 + r14 + r13)) (min (6 - (r15 + r13)) (min (6 - (r15 + r14)) ((6 - (r15 + r14 + r13)))))) fun r11 =>
  allLe (min (12 - (r15 + r14 + r13 + r11)) (min (6 - (r15 + r13 + r11)) (min (6 - (r15 + r14 + r11)) ((6 - (r15 + r14 + r13)))))) fun r7 =>
    suffix4 r15 r14 r13 r11 r7

theorem counts_complete4 (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : ℕ)
    (hb : countBounds4 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (hc : checkCounts4 = true) :
    okayWeight (vennWeight4 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) = true := by
  rcases hb with ⟨h0, h1, h2, h3, h4⟩
  unfold checkCounts4 at hc
  have selected0 := allLe_sound _ _ hc r15 (by omega)
  have selected1 := allLe_sound _ _ selected0 r14 (by omega)
  have selected2 := allLe_sound _ _ selected1 r13 (by omega)
  have selected3 := allLe_sound _ _ selected2 r11 (by omega)
  have selected4 := allLe_sound _ _ selected3 r7 (by omega)
  unfold suffix4 at selected4
  have selected5 := allLe_sound _ _ selected4 r12 (by omega)
  have selected6 := allLe_sound _ _ selected5 r10 (by omega)
  have selected7 := allLe_sound _ _ selected6 r9 (by omega)
  have selected8 := allLe_sound _ _ selected7 r6 (by omega)
  have selected9 := allLe_sound _ _ selected8 r5 (by omega)
  have selected10 := allLe_sound _ _ selected9 r3 (by omega)
  have selected11 := allLe_sound _ _ selected10 r8 (by omega)
  have selected12 := allLe_sound _ _ selected11 r4 (by omega)
  have selected13 := allLe_sound _ _ selected12 r2 (by omega)
  have selected14 := allLe_sound _ _ selected13 r1 (by omega)
  exact selected14

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.vennWeight3
#print axioms Paper6LiteralLouWang.countBounds3
#print axioms Paper6LiteralLouWang.suffix3
#print axioms Paper6LiteralLouWang.checkCounts3
#print axioms Paper6LiteralLouWang.counts_complete3
#print axioms Paper6LiteralLouWang.suffix4Depth6
#print axioms Paper6LiteralLouWang.suffix4Depth7
#print axioms Paper6LiteralLouWang.suffix4Depth8
#print axioms Paper6LiteralLouWang.suffix4Depth9
#print axioms Paper6LiteralLouWang.suffix4Depth10
#print axioms Paper6LiteralLouWang.vennWeight4
#print axioms Paper6LiteralLouWang.countBounds4
#print axioms Paper6LiteralLouWang.suffix4
#print axioms Paper6LiteralLouWang.checkCounts4
#print axioms Paper6LiteralLouWang.counts_complete4
