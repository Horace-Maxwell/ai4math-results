import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/- A polygonal upper profile is given by its genuine supporting lines; the lower
   surface uses the negative of another such profile. All lengths are real. -/
namespace DurerDV

structure Profile where
  count : ℕ
  length : ℝ
  knot : ℕ → ℝ
  value : ℝ → ℝ
  slope : ℕ → ℝ
  count_pos : 0 < count
  length_pos : 0 < length
  first : knot 0 = 0
  last : knot count = length
  increasing : ∀ i j, i < j → j ≤ count → knot i < knot j
  covers : ∀ t, 0 ≤ t → t ≤ length →
    ∃ i, i < count ∧ knot i ≤ t ∧ t ≤ knot (i+1)
  support : ∀ i, i < count → ∀ t, 0 ≤ t → t ≤ length →
    value t ≤ value (knot i) + slope i * (t - knot i)
  exposed : ∀ i, i < count → ∀ t, 0 ≤ t → t ≤ length →
    (value t = value (knot i) + slope i * (t - knot i) ↔
      knot i ≤ t ∧ t ≤ knot (i+1))

structure Solid where
  upper : Profile
  lower : Profile
  c : ℝ
  c_min : -1 < c
  c_max : c ≤ 0
  gap : ∀ x y, 0 ≤ x → x ≤ upper.length → 0 ≤ y → y ≤ lower.length →
    -lower.value y < upper.value x

structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

inductive Chart | roof | a | b | c | d | floor
  deriving DecidableEq

def rank : Chart → ℕ
  | .roof => 0 | .a => 1 | .b => 2 | .c => 3 | .d => 4 | .floor => 5

def body (s : Solid) (p : V3) : Prop :=
  0 ≤ p.x ∧ p.x ≤ s.upper.length ∧ 0 ≤ p.y ∧ p.y ≤ s.lower.length ∧
  -s.lower.value p.y ≤ p.z ∧ p.z ≤ s.upper.value p.x

def onChart (s : Solid) (k : Chart) (p : V3) : Prop :=
  body s p ∧ match k with
    | .roof => p.z = s.upper.value p.x
    | .a => p.x = 0
    | .b => p.y = s.lower.length
    | .c => p.x = s.upper.length
    | .d => p.y = 0
    | .floor => p.z = -s.lower.value p.y

def piece (f : Profile) (i : ℕ) (x : ℝ) : Prop :=
  i < f.count ∧ f.knot i ≤ x ∧ x ≤ f.knot (i+1)

def commonFacet (s : Solid) (k : Chart) (p q : V3) : Prop :=
  match k with
  | .roof => ∃ i, piece s.upper i p.x ∧ piece s.upper i q.x
  | .floor => ∃ i, piece s.lower i p.y ∧ piece s.lower i q.y
  | _ => True

/- Physical Cartesian coordinates are (x + c*y, sqrt(1-c²)*y, z);
   the horizontal generating directions have length one and scalar product c. -/
noncomputable def embed (s : Solid) (p : V3) : V3 :=
  ⟨p.x + s.c*p.y, Real.sqrt (1-s.c^2)*p.y, p.z⟩

def sq3 (p q : V3) : ℝ :=
  (p.x-q.x)^2 + (p.y-q.y)^2 + (p.z-q.z)^2

def sq2 (p q : ℝ × ℝ) : ℝ := (p.1-q.1)^2 + (p.2-q.2)^2

def perim (s : Solid) : ℝ := 2*(s.upper.length + s.lower.length)

noncomputable def flat (s : Solid) (u v : ℝ → ℝ) (k : Chart) (p : V3) : ℝ × ℝ :=
  match k with
  | .roof => (p.y + s.c*p.x, s.upper.value 0 + u p.x)
  | .a => (p.y, p.z)
  | .b => (s.lower.length+p.x, p.z)
  | .c => (2*s.lower.length+s.upper.length-p.y, p.z)
  | .d => (perim s-p.x, p.z)
  | .floor => (perim s-p.x-s.c*p.y, -s.lower.value 0-v p.y)

/- The four walls form the central face chain. Within each roof retain all
   transverse true ridges, giving one chart with the indicated subdivision.
   On closed points two charts are welded exactly along consecutive common
   edges, including an endpoint via intervening charts. This definition has
   no reference to planar coordinates. -/
def welded (s : Solid) (i j : Chart) (p q : V3) : Prop :=
  p = q ∧ ∀ k : Chart, min (rank i) (rank j) ≤ rank k →
    rank k ≤ max (rank i) (rank j) → onChart s k p

def arcValid (s : Solid) (f : Profile) (u : ℝ → ℝ) : Prop :=
  u 0 = 0 ∧ StrictMonoOn u (Set.Icc 0 f.length) ∧
    ∀ i x y, piece f i x → piece f i y →
      u x - u y = Real.sqrt (1+f.slope i^2-s.c^2)*(x-y)

/- Metric and exact equivalence on CLOSED facets of the specified cut surface.
   The conclusion quantifies over actual three-dimensional points and all
   panels, with no isometry or overlap condition on the input. -/
def StrictRoofNet : Prop :=
  ∀ s : Solid, ∃ u v : ℝ → ℝ, arcValid s s.upper u ∧ arcValid s s.lower v ∧
    (∀ k p q, onChart s k p → onChart s k q → commonFacet s k p q →
      sq2 (flat s u v k p) (flat s u v k q) = sq3 (embed s p) (embed s q)) ∧
    (∀ i j p q, onChart s i p → onChart s j q →
      (flat s u v i p = flat s u v j q ↔ welded s i j p q))

/- A nonrectangular example with a genuine bend on both surfaces. -/
def ObliqueExample : Prop :=
  ∃ s : Solid, s.c = -(1/2 : ℝ) ∧ s.upper.length = 2 ∧ s.lower.length = 2 ∧
    s.upper.count = 2 ∧ s.lower.count = 2 ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 2, s.upper.value t = min 3 (3+(1-t)/10)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 2, -s.lower.value t = max 0 ((t-1)/10))

end DurerDV
