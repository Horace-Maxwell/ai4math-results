import Research.Backfill.Paper6.PairNumeric

set_option autoImplicit false

namespace Paper6FiveExclusion

def pairWeight0  : ℤ :=
  (1 : ℤ) * (2 : ℤ) ^ (14 - (7 + (0))) +
    (1 : ℤ) * (2 : ℤ) ^ (14 - (7 + (0))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (14))

def pairBounds0  : Prop :=
  0 ≤ 7 ∧
  0 ≤ 7

def pairSuffix0Depth0  : Bool :=
    okayWeight (pairWeight0 )

def checkPairs0 : Bool := pairSuffix0Depth0

theorem pair_counts_complete0 
    (hc : checkPairs0 = true) :
    okayWeight (pairWeight0 ) = true := by
  exact hc

def pairWeight1 (a1 b1 : ℕ) : ℤ :=
  (1 : ℤ) * (2 : ℤ) ^ (14 - (7 + (0))) +
    (1 : ℤ) * (2 : ℤ) ^ (14 - (7 + (0))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (14)) +
    (1 : ℤ) * (2 : ℤ) ^ (14 - ((a1) + (b1))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (b1))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (a1))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (14))

def pairBounds1 (a1 b1 : ℕ) : Prop :=
  a1 ≤ 7 ∧
  b1 ≤ 7 ∧
  a1 + b1 ≤ 7

def pairSuffix1Depth0  : Bool :=
  allLe (min (7 - (0)) ((7 - (0)))) fun a1 =>
  allLe (min (7 - (0)) ((7 - (a1)))) fun b1 =>
    okayWeight (pairWeight1 a1 b1)

def checkPairs1 : Bool := pairSuffix1Depth0

theorem pair_counts_complete1 (a1 b1 : ℕ)
    (hb : pairBounds1 a1 b1) (hc : checkPairs1 = true) :
    okayWeight (pairWeight1 a1 b1) = true := by
  rcases hb with ⟨h0, h1, h2⟩
  unfold checkPairs1 pairSuffix1Depth0 at hc
  have selected0 := allLe_sound _ _ hc a1 (by omega)
  have selected1 := allLe_sound _ _ selected0 b1 (by omega)
  exact selected1

def pairWeight2 (a1 a2 a3 b1 b2 b3 : ℕ) : ℤ :=
  (1 : ℤ) * (2 : ℤ) ^ (14 - (7 + (0))) +
    (1 : ℤ) * (2 : ℤ) ^ (14 - (7 + (0))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (14)) +
    (1 : ℤ) * (2 : ℤ) ^ (14 - ((a1 + a3) + (b1 + b3))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (b1 + b3))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (a1 + a3))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (14)) +
    (1 : ℤ) * (2 : ℤ) ^ (14 - ((a2 + a3) + (b2 + b3))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (b2 + b3))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (a2 + a3))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (14)) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - ((a1 + a2 + a3) + (b1 + b2 + b3))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (7 + (b1 + b2 + b3))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (7 + (a1 + a2 + a3))) +
    (-8 : ℤ) * (2 : ℤ) ^ (14 - (14))

def pairBounds2 (a1 a2 a3 b1 b2 b3 : ℕ) : Prop :=
  a1 + a2 + a3 ≤ 7 ∧
  b1 + b2 + b3 ≤ 7 ∧
  a1 + a3 + b1 + b3 ≤ 7 ∧
  a2 + a3 + b2 + b3 ≤ 7

def pairSuffix2Depth0  : Bool :=
  allLe (min (7 - (0)) (min (7 - (0)) ((7 - (0))))) fun a3 =>
  allLe (min (7 - (0)) (min (7 - (a3)) ((7 - (a3))))) fun b3 =>
  allLe (min (7 - (a3)) ((7 - (a3 + b3)))) fun a2 =>
  allLe (min (7 - (b3)) ((7 - (a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a3 + a2)) ((7 - (a3 + b3)))) fun a1 =>
  allLe (min (7 - (b3 + b2)) ((7 - (a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight2 a1 a2 a3 b1 b2 b3)

def pairSuffix2Depth1 (a3 : ℕ) : Bool :=
  allLe (min (7 - (0)) (min (7 - (a3)) ((7 - (a3))))) fun b3 =>
  allLe (min (7 - (a3)) ((7 - (a3 + b3)))) fun a2 =>
  allLe (min (7 - (b3)) ((7 - (a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a3 + a2)) ((7 - (a3 + b3)))) fun a1 =>
  allLe (min (7 - (b3 + b2)) ((7 - (a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight2 a1 a2 a3 b1 b2 b3)

def checkPairs2 : Bool := pairSuffix2Depth0

theorem pair_counts_complete2 (a1 a2 a3 b1 b2 b3 : ℕ)
    (hb : pairBounds2 a1 a2 a3 b1 b2 b3) (hc : checkPairs2 = true) :
    okayWeight (pairWeight2 a1 a2 a3 b1 b2 b3) = true := by
  rcases hb with ⟨h0, h1, h2, h3⟩
  unfold checkPairs2 pairSuffix2Depth0 at hc
  have selected0 := allLe_sound _ _ hc a3 (by omega)
  have selected1 := allLe_sound _ _ selected0 b3 (by omega)
  have selected2 := allLe_sound _ _ selected1 a2 (by omega)
  have selected3 := allLe_sound _ _ selected2 b2 (by omega)
  have selected4 := allLe_sound _ _ selected3 a1 (by omega)
  have selected5 := allLe_sound _ _ selected4 b1 (by omega)
  exact selected5

def pairWeight3 (a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : ℕ) : ℤ :=
  (1 : ℤ) * (2 : ℤ) ^ (14 - (7 + (0))) +
    (1 : ℤ) * (2 : ℤ) ^ (14 - (7 + (0))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (14)) +
    (1 : ℤ) * (2 : ℤ) ^ (14 - ((a1 + a3 + a5 + a7) + (b1 + b3 + b5 + b7))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (b1 + b3 + b5 + b7))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (a1 + a3 + a5 + a7))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (14)) +
    (1 : ℤ) * (2 : ℤ) ^ (14 - ((a2 + a3 + a6 + a7) + (b2 + b3 + b6 + b7))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (b2 + b3 + b6 + b7))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (a2 + a3 + a6 + a7))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (14)) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - ((a1 + a2 + a3 + a5 + a6 + a7) + (b1 + b2 + b3 + b5 + b6 + b7))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (7 + (b1 + b2 + b3 + b5 + b6 + b7))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (7 + (a1 + a2 + a3 + a5 + a6 + a7))) +
    (-8 : ℤ) * (2 : ℤ) ^ (14 - (14)) +
    (1 : ℤ) * (2 : ℤ) ^ (14 - ((a4 + a5 + a6 + a7) + (b4 + b5 + b6 + b7))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (b4 + b5 + b6 + b7))) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - (7 + (a4 + a5 + a6 + a7))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (14)) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - ((a1 + a3 + a4 + a5 + a6 + a7) + (b1 + b3 + b4 + b5 + b6 + b7))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (7 + (b1 + b3 + b4 + b5 + b6 + b7))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (7 + (a1 + a3 + a4 + a5 + a6 + a7))) +
    (-8 : ℤ) * (2 : ℤ) ^ (14 - (14)) +
    (-2 : ℤ) * (2 : ℤ) ^ (14 - ((a2 + a3 + a4 + a5 + a6 + a7) + (b2 + b3 + b4 + b5 + b6 + b7))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (7 + (b2 + b3 + b4 + b5 + b6 + b7))) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - (7 + (a2 + a3 + a4 + a5 + a6 + a7))) +
    (-8 : ℤ) * (2 : ℤ) ^ (14 - (14)) +
    (4 : ℤ) * (2 : ℤ) ^ (14 - ((a1 + a2 + a3 + a4 + a5 + a6 + a7) + (b1 + b2 + b3 + b4 + b5 + b6 + b7))) +
    (-8 : ℤ) * (2 : ℤ) ^ (14 - (7 + (b1 + b2 + b3 + b4 + b5 + b6 + b7))) +
    (-8 : ℤ) * (2 : ℤ) ^ (14 - (7 + (a1 + a2 + a3 + a4 + a5 + a6 + a7))) +
    (16 : ℤ) * (2 : ℤ) ^ (14 - (14))

def pairBounds3 (a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : ℕ) : Prop :=
  a1 + a2 + a3 + a4 + a5 + a6 + a7 ≤ 7 ∧
  b1 + b2 + b3 + b4 + b5 + b6 + b7 ≤ 7 ∧
  a1 + a3 + a5 + a7 + b1 + b3 + b5 + b7 ≤ 7 ∧
  a2 + a3 + a6 + a7 + b2 + b3 + b6 + b7 ≤ 7 ∧
  a4 + a5 + a6 + a7 + b4 + b5 + b6 + b7 ≤ 7

def pairSuffix3Depth0  : Bool :=
  allLe (min (7 - (0)) (min (7 - (0)) (min (7 - (0)) ((7 - (0)))))) fun a7 =>
  allLe (min (7 - (0)) (min (7 - (a7)) (min (7 - (a7)) ((7 - (a7)))))) fun b7 =>
  allLe (min (7 - (a7)) (min (7 - (a7 + b7)) ((7 - (a7 + b7))))) fun a6 =>
  allLe (min (7 - (b7)) (min (7 - (a7 + b7 + a6)) ((7 - (a7 + b7 + a6))))) fun b6 =>
  allLe (min (7 - (a7 + a6)) (min (7 - (a7 + b7)) ((7 - (a7 + b7 + a6 + b6))))) fun a5 =>
  allLe (min (7 - (b7 + b6)) (min (7 - (a7 + b7 + a5)) ((7 - (a7 + b7 + a6 + b6 + a5))))) fun b5 =>
  allLe (min (7 - (a7 + a6 + a5)) (min (7 - (a7 + b7 + a5 + b5)) ((7 - (a7 + b7 + a6 + b6))))) fun a3 =>
  allLe (min (7 - (b7 + b6 + b5)) (min (7 - (a7 + b7 + a5 + b5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a3))))) fun b3 =>
  allLe (min (7 - (a7 + a6 + a5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5)))) fun a4 =>
  allLe (min (7 - (b7 + b6 + b5 + b3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5 + a4)))) fun b4 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3)))) fun a2 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4 + a2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3)))) fun a1 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4 + b2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7)

def pairSuffix3Depth1 (a7 : ℕ) : Bool :=
  allLe (min (7 - (0)) (min (7 - (a7)) (min (7 - (a7)) ((7 - (a7)))))) fun b7 =>
  allLe (min (7 - (a7)) (min (7 - (a7 + b7)) ((7 - (a7 + b7))))) fun a6 =>
  allLe (min (7 - (b7)) (min (7 - (a7 + b7 + a6)) ((7 - (a7 + b7 + a6))))) fun b6 =>
  allLe (min (7 - (a7 + a6)) (min (7 - (a7 + b7)) ((7 - (a7 + b7 + a6 + b6))))) fun a5 =>
  allLe (min (7 - (b7 + b6)) (min (7 - (a7 + b7 + a5)) ((7 - (a7 + b7 + a6 + b6 + a5))))) fun b5 =>
  allLe (min (7 - (a7 + a6 + a5)) (min (7 - (a7 + b7 + a5 + b5)) ((7 - (a7 + b7 + a6 + b6))))) fun a3 =>
  allLe (min (7 - (b7 + b6 + b5)) (min (7 - (a7 + b7 + a5 + b5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a3))))) fun b3 =>
  allLe (min (7 - (a7 + a6 + a5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5)))) fun a4 =>
  allLe (min (7 - (b7 + b6 + b5 + b3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5 + a4)))) fun b4 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3)))) fun a2 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4 + a2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3)))) fun a1 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4 + b2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7)

def pairSuffix3Depth2 (a7 b7 : ℕ) : Bool :=
  allLe (min (7 - (a7)) (min (7 - (a7 + b7)) ((7 - (a7 + b7))))) fun a6 =>
  allLe (min (7 - (b7)) (min (7 - (a7 + b7 + a6)) ((7 - (a7 + b7 + a6))))) fun b6 =>
  allLe (min (7 - (a7 + a6)) (min (7 - (a7 + b7)) ((7 - (a7 + b7 + a6 + b6))))) fun a5 =>
  allLe (min (7 - (b7 + b6)) (min (7 - (a7 + b7 + a5)) ((7 - (a7 + b7 + a6 + b6 + a5))))) fun b5 =>
  allLe (min (7 - (a7 + a6 + a5)) (min (7 - (a7 + b7 + a5 + b5)) ((7 - (a7 + b7 + a6 + b6))))) fun a3 =>
  allLe (min (7 - (b7 + b6 + b5)) (min (7 - (a7 + b7 + a5 + b5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a3))))) fun b3 =>
  allLe (min (7 - (a7 + a6 + a5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5)))) fun a4 =>
  allLe (min (7 - (b7 + b6 + b5 + b3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5 + a4)))) fun b4 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3)))) fun a2 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4 + a2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3)))) fun a1 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4 + b2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7)

def pairSuffix3Depth3 (a7 b7 a6 : ℕ) : Bool :=
  allLe (min (7 - (b7)) (min (7 - (a7 + b7 + a6)) ((7 - (a7 + b7 + a6))))) fun b6 =>
  allLe (min (7 - (a7 + a6)) (min (7 - (a7 + b7)) ((7 - (a7 + b7 + a6 + b6))))) fun a5 =>
  allLe (min (7 - (b7 + b6)) (min (7 - (a7 + b7 + a5)) ((7 - (a7 + b7 + a6 + b6 + a5))))) fun b5 =>
  allLe (min (7 - (a7 + a6 + a5)) (min (7 - (a7 + b7 + a5 + b5)) ((7 - (a7 + b7 + a6 + b6))))) fun a3 =>
  allLe (min (7 - (b7 + b6 + b5)) (min (7 - (a7 + b7 + a5 + b5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a3))))) fun b3 =>
  allLe (min (7 - (a7 + a6 + a5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5)))) fun a4 =>
  allLe (min (7 - (b7 + b6 + b5 + b3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5 + a4)))) fun b4 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3)))) fun a2 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4 + a2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3)))) fun a1 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4 + b2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7)

def pairSuffix3Depth4 (a7 b7 a6 b6 : ℕ) : Bool :=
  allLe (min (7 - (a7 + a6)) (min (7 - (a7 + b7)) ((7 - (a7 + b7 + a6 + b6))))) fun a5 =>
  allLe (min (7 - (b7 + b6)) (min (7 - (a7 + b7 + a5)) ((7 - (a7 + b7 + a6 + b6 + a5))))) fun b5 =>
  allLe (min (7 - (a7 + a6 + a5)) (min (7 - (a7 + b7 + a5 + b5)) ((7 - (a7 + b7 + a6 + b6))))) fun a3 =>
  allLe (min (7 - (b7 + b6 + b5)) (min (7 - (a7 + b7 + a5 + b5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a3))))) fun b3 =>
  allLe (min (7 - (a7 + a6 + a5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5)))) fun a4 =>
  allLe (min (7 - (b7 + b6 + b5 + b3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5 + a4)))) fun b4 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3)))) fun a2 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4 + a2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3)))) fun a1 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4 + b2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7)

def pairSuffix3Depth5 (a7 b7 a6 b6 a5 : ℕ) : Bool :=
  allLe (min (7 - (b7 + b6)) (min (7 - (a7 + b7 + a5)) ((7 - (a7 + b7 + a6 + b6 + a5))))) fun b5 =>
  allLe (min (7 - (a7 + a6 + a5)) (min (7 - (a7 + b7 + a5 + b5)) ((7 - (a7 + b7 + a6 + b6))))) fun a3 =>
  allLe (min (7 - (b7 + b6 + b5)) (min (7 - (a7 + b7 + a5 + b5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a3))))) fun b3 =>
  allLe (min (7 - (a7 + a6 + a5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5)))) fun a4 =>
  allLe (min (7 - (b7 + b6 + b5 + b3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5 + a4)))) fun b4 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3)))) fun a2 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4 + a2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3)))) fun a1 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4 + b2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7)

def pairSuffix3Depth6 (a7 b7 a6 b6 a5 b5 : ℕ) : Bool :=
  allLe (min (7 - (a7 + a6 + a5)) (min (7 - (a7 + b7 + a5 + b5)) ((7 - (a7 + b7 + a6 + b6))))) fun a3 =>
  allLe (min (7 - (b7 + b6 + b5)) (min (7 - (a7 + b7 + a5 + b5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a3))))) fun b3 =>
  allLe (min (7 - (a7 + a6 + a5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5)))) fun a4 =>
  allLe (min (7 - (b7 + b6 + b5 + b3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5 + a4)))) fun b4 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3)))) fun a2 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4 + a2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3)))) fun a1 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4 + b2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7)

def pairSuffix3Depth7 (a7 b7 a6 b6 a5 b5 a3 : ℕ) : Bool :=
  allLe (min (7 - (b7 + b6 + b5)) (min (7 - (a7 + b7 + a5 + b5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a3))))) fun b3 =>
  allLe (min (7 - (a7 + a6 + a5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5)))) fun a4 =>
  allLe (min (7 - (b7 + b6 + b5 + b3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5 + a4)))) fun b4 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3)))) fun a2 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4 + a2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3)))) fun a1 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4 + b2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7)

def pairSuffix3Depth8 (a7 b7 a6 b6 a5 b5 a3 b3 : ℕ) : Bool :=
  allLe (min (7 - (a7 + a6 + a5 + a3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5)))) fun a4 =>
  allLe (min (7 - (b7 + b6 + b5 + b3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5 + a4)))) fun b4 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3)))) fun a2 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4 + a2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3)))) fun a1 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4 + b2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7)

def pairSuffix3Depth9 (a7 b7 a6 b6 a5 b5 a3 b3 a4 : ℕ) : Bool :=
  allLe (min (7 - (b7 + b6 + b5 + b3)) ((7 - (a7 + b7 + a6 + b6 + a5 + b5 + a4)))) fun b4 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3)))) fun a2 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4)) ((7 - (a7 + b7 + a6 + b6 + a3 + b3 + a2)))) fun b2 =>
  allLe (min (7 - (a7 + a6 + a5 + a3 + a4 + a2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3)))) fun a1 =>
  allLe (min (7 - (b7 + b6 + b5 + b3 + b4 + b2)) ((7 - (a7 + b7 + a5 + b5 + a3 + b3 + a1)))) fun b1 =>
    okayWeight (pairWeight3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7)

def checkPairs3 : Bool := pairSuffix3Depth0

theorem pair_counts_complete3 (a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : ℕ)
    (hb : pairBounds3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7) (hc : checkPairs3 = true) :
    okayWeight (pairWeight3 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7) = true := by
  rcases hb with ⟨h0, h1, h2, h3, h4⟩
  unfold checkPairs3 pairSuffix3Depth0 at hc
  have selected0 := allLe_sound _ _ hc a7 (by omega)
  have selected1 := allLe_sound _ _ selected0 b7 (by omega)
  have selected2 := allLe_sound _ _ selected1 a6 (by omega)
  have selected3 := allLe_sound _ _ selected2 b6 (by omega)
  have selected4 := allLe_sound _ _ selected3 a5 (by omega)
  have selected5 := allLe_sound _ _ selected4 b5 (by omega)
  have selected6 := allLe_sound _ _ selected5 a3 (by omega)
  have selected7 := allLe_sound _ _ selected6 b3 (by omega)
  have selected8 := allLe_sound _ _ selected7 a4 (by omega)
  have selected9 := allLe_sound _ _ selected8 b4 (by omega)
  have selected10 := allLe_sound _ _ selected9 a2 (by omega)
  have selected11 := allLe_sound _ _ selected10 b2 (by omega)
  have selected12 := allLe_sound _ _ selected11 a1 (by omega)
  have selected13 := allLe_sound _ _ selected12 b1 (by omega)
  exact selected13

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.pairSuffix0Depth0
#print axioms Paper6FiveExclusion.pairWeight0
#print axioms Paper6FiveExclusion.pairBounds0
#print axioms Paper6FiveExclusion.checkPairs0
#print axioms Paper6FiveExclusion.pair_counts_complete0
#print axioms Paper6FiveExclusion.pairSuffix1Depth0
#print axioms Paper6FiveExclusion.pairWeight1
#print axioms Paper6FiveExclusion.pairBounds1
#print axioms Paper6FiveExclusion.checkPairs1
#print axioms Paper6FiveExclusion.pair_counts_complete1
#print axioms Paper6FiveExclusion.pairSuffix2Depth0
#print axioms Paper6FiveExclusion.pairSuffix2Depth1
#print axioms Paper6FiveExclusion.pairWeight2
#print axioms Paper6FiveExclusion.pairBounds2
#print axioms Paper6FiveExclusion.checkPairs2
#print axioms Paper6FiveExclusion.pair_counts_complete2
#print axioms Paper6FiveExclusion.pairSuffix3Depth0
#print axioms Paper6FiveExclusion.pairSuffix3Depth1
#print axioms Paper6FiveExclusion.pairSuffix3Depth2
#print axioms Paper6FiveExclusion.pairSuffix3Depth3
#print axioms Paper6FiveExclusion.pairSuffix3Depth4
#print axioms Paper6FiveExclusion.pairSuffix3Depth5
#print axioms Paper6FiveExclusion.pairSuffix3Depth6
#print axioms Paper6FiveExclusion.pairSuffix3Depth7
#print axioms Paper6FiveExclusion.pairSuffix3Depth8
#print axioms Paper6FiveExclusion.pairSuffix3Depth9
#print axioms Paper6FiveExclusion.pairWeight3
#print axioms Paper6FiveExclusion.pairBounds3
#print axioms Paper6FiveExclusion.checkPairs3
#print axioms Paper6FiveExclusion.pair_counts_complete3
