/-!
# Small graphs: bit-mask checkers (core Lean only, no Mathlib)

Checkers on `Nat` for graphs with at most twelve vertices, written with `Nat.rec` loops over
kernel-accelerated `Nat` operations so that `decide +kernel` evaluates them quickly; their meaning
is proved in `Research.Backfill.Paper3.Proof.Small.Bridge`. A graph on `{0, …, n-1}` is an edge mask `c`: the pair `{i, j}`
with `i < j` is bit `j (j - 1) / 2 + i` of `c`. A vertex set is a vertex mask `a < 2^n`.
The table `certs6` (generated outside Lean by `gen/gen_certs6.py`) lists, for each cubic edge
mask on six vertices, a permutation mapping it onto `K_{3,3}` or onto the prism; it is only
checked here.
-/

set_option autoImplicit false

noncomputable section

namespace P3Small

/-- `nall n p = p (n-1) && … && p 0`. -/
def nall (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => p k && acc) n

/-- The number of `k < n` with `p k`. -/
def countB (n : Nat) (p : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => cond (p k) (Nat.add acc 1) acc) n

/-- `∑_{k < n} g k`. -/
def sumB (n : Nat) (g : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.add (g k) acc) n

/-- Bit `i` of `m`. -/
def bit (m i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

/-- The index of the pair `{i, j}` in an edge mask. -/
def pidx (i j : Nat) : Nat :=
  cond (Nat.blt i j) (Nat.add (Nat.div (Nat.mul j (Nat.sub j 1)) 2) i)
    (Nat.add (Nat.div (Nat.mul i (Nat.sub i 1)) 2) j)

/-- Adjacency in the graph with edge mask `c`. -/
def adjB (c i j : Nat) : Bool := cond (Nat.beq i j) false (bit c (pidx i j))

/-- The degree of `i` in the graph with edge mask `c` on `{0, …, n-1}`. -/
def degB (n c i : Nat) : Nat := countB n (adjB c i)

/-- The graph with edge mask `c` on `{0, …, n-1}` is `d`-regular. -/
def regB (n c d : Nat) : Bool := nall n (fun i => Nat.beq (degB n c i) d)

/-- The number of edges of the graph with edge mask `c` inside the vertex mask `a`. -/
def pairsIn (n c a : Nat) : Nat :=
  sumB n (fun j => cond (bit a j) (sumB j (fun i => cond (bit a i && bit c (pidx i j)) 1 0)) 0)

/-- `N_{≤t}` of the graph with edge mask `c` on `{0, …, n-1}`. -/
def nleB (n c t : Nat) : Nat := countB (Nat.pow 2 n) (fun a => Nat.ble (pairsIn n c a) t)

/-! ### Six vertices: permutations and isomorphism certificates -/

/-- The image of `i` under the permutation with code `π` (three bits per vertex). -/
def pimg (π i : Nat) : Nat := Nat.land (Nat.shiftRight π (Nat.mul 3 i)) 7

/-- `π` codes a permutation of `{0, …, 5}`. -/
def permOK (π : Nat) : Bool :=
  nall 6 (fun i => Nat.blt (pimg π i) 6) &&
    nall 6 (fun i => nall 6 (fun j => Nat.beq i j || !Nat.beq (pimg π i) (pimg π j)))

/-- Equality of booleans. -/
def beqB (a b : Bool) : Bool := cond a b (!b)

/-- `π` maps the graph with edge mask `c` onto the graph with edge mask `c'` (six vertices). -/
def isoOK (c c' π : Nat) : Bool :=
  nall 6 (fun i => nall 6 (fun j => beqB (adjB c i j) (adjB c' (pimg π i) (pimg π j))))

/-- `K_{3,3}` with sides `{0, 1, 2}` and `{3, 4, 5}`. -/
def k33Mask : Nat := 7672

/-- The prism `K_3 □ K_2` with `(a, b) ↦ 2a + b`. -/
def prismMask : Nat := 26995

/-- For each cubic edge mask on six vertices: a permutation code and whether the target is the
prism (`true`) or `K_{3,3}` (`false`). -/
def certs6 : List (Nat × Nat × Bool) :=
    [(7672, 181896, false), (7916, 43352, true), (7922, 72472, true), (8028, 50520, true),
    (8049, 137040, true), (8090, 86808, true), (8105, 144208, true), (11756, 72024, true),
    (11762, 43800, true), (12006, 181448, false), (12118, 51864, true), (12133, 137936, true),
    (12174, 88152, true), (12195, 146000, true), (13788, 136536, true), (13809, 51024, true),
    (14038, 137880, true), (14053, 51920, true), (14165, 181336, false), (14221, 88264, true),
    (14227, 146056, true), (14810, 172824, true), (14825, 115536, true), (15054, 174168, true),
    (15075, 117328, true), (15181, 174280, true), (15187, 117384, true), (15243, 72472, false),
    (19836, 82776, true), (19898, 54552, true), (20086, 84568, true), (20142, 55448, true),
    (20254, 174280, false), (20269, 152272, true), (20275, 153168, true), (21756, 140120, true),
    (21945, 47440, true), (22133, 84680, true), (22174, 152216, true), (22189, 174168, false),
    (22195, 153224, true), (22301, 55504, true), (22778, 169240, true), (22905, 104784, true),
    (23134, 181336, true), (23149, 181448, true), (23155, 86808, false), (23211, 120968, true),
    (23323, 120912, true), (25846, 141912, true), (25973, 142024, true), (26014, 152664, true),
    (26029, 152776, true), (26035, 172824, false), (26279, 47888, true), (26391, 55056, true),
    (26862, 170136, true), (26974, 180888, true), (26989, 88152, false), (26995, 181896, true),
    (27051, 178312, true), (27239, 105232, true), (27407, 119568, true), (28894, 88264, false),
    (28909, 180944, true), (28915, 181840, true), (29021, 170192, true), (29083, 178256, true),
    (29271, 169744, true), (29327, 176912, true)]

/-- The certificate of `c` in a table (default `(0, false)`). -/
def findCert (c : Nat) (l : List (Nat × Nat × Bool)) : Nat × Bool :=
  List.rec (motive := fun _ => Nat × Bool) (0, false)
    (fun e _ acc => cond (Nat.beq c e.1) e.2 acc) l

/-- The certificate of `c` in `certs6` is valid. -/
def certOK (c : Nat) : Bool :=
  permOK (findCert c certs6).1 &&
    isoOK c (cond (findCert c certs6).2 prismMask k33Mask) (findCert c certs6).1

/-- Every cubic edge mask on six vertices has a valid certificate. -/
def allCert : Bool := nall 32768 (fun c => !regB 6 c 3 || certOK c)

/-! ### Edge masks of the graphs of Table 4 -/

/-- `H_3 = Hd 3 0 0 0 0` with `(k, inl i) ↦ 6k + i`, `(k, inr j) ↦ 6k + 3 + j`. -/
def maskH3 : Nat := 16156690120190467568

/-- `2 K_{3,3}` with the same labelling. -/
def maskK23 : Nat := 16156694449517239800

/-- `3 K_4` with `(k, i) ↦ 4k + i`. -/
def maskK34 : Nat := 64590643448170168383

/-- `2 K_{2,2}` with `(k, inl i) ↦ 4k + i`, `(k, inr j) ↦ 4k + 2 + j`. -/
def maskK22 : Nat := 102236190

/-- `C_8` (`i ~ i ± 1 mod 8`). -/
def maskC8 : Nat := 137380389

end P3Small

end
