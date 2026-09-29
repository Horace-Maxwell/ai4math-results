import Research.Backfill.Paper4.Proof.HKOFig2Remark

/-! Explicit connected induced paths that are not isometric in the ambient graph.
The full frozen MathOverflow target also keeps its adjacency iff and ambient distance.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4
namespace NonDHExamples

local instance : DecidableRel Challenge.MOGraph.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ Challenge.moEdges ∨
    (j.val, i.val) ∈ Challenge.moEdges))
local instance : DecidableRel Challenge.G1.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ Challenge.g1Edges ∨
    (j.val, i.val) ∈ Challenge.g1Edges))
local instance : DecidableRel Challenge.HKOFig2.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ Challenge.hkoFig2Edges ∨
    (j.val, i.val) ∈ Challenge.hkoFig2Edges))

def lineDist (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

/-! The MathOverflow induced path is `6–5–0–8–7`. -/
def MOSet : Set (Fin 11) := {x | x = 0 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8}
local instance : DecidablePred (· ∈ MOSet) := fun x =>
  inferInstanceAs (Decidable (x = 0 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8))
local instance : Nonempty MOSet := ⟨⟨0, by decide⟩⟩
local instance : DecidableRel (Challenge.MOGraph.induce MOSet).Adj := fun x y =>
  inferInstanceAs (Decidable (Challenge.MOGraph.Adj x.val y.val))

def MOPosition : Fin 11 → ℕ := ![2, 0, 0, 0, 0, 1, 0, 4, 3, 0, 0]
def DMO (u v : MOSet) : ℕ := lineDist (MOPosition u.val) (MOPosition v.val)

theorem MO_induced_dist : ∀ u v, (Challenge.MOGraph.induce MOSet).dist u v = DMO u v :=
  HKOTriameter.dist_eq_of_certificate (Challenge.MOGraph.induce MOSet) DMO
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem MO_induced_connected : (Challenge.MOGraph.induce MOSet).Connected :=
  HKOTriameter.connected_of_dist _ fun x y hxy => by
    rw [MO_induced_dist]
    revert x y
    decide

theorem MO_path_edges : ∀ i j : Fin 5,
    Challenge.MOGraph.Adj (![6, 5, 0, 8, 7] i) (![6, 5, 0, 8, 7] j) ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  decide +kernel

theorem MO_dist_6_7 : Challenge.MOGraph.dist 6 7 = 2 := by
  let p : Challenge.MOGraph.Walk 6 7 :=
    .cons (by decide : Challenge.MOGraph.Adj 6 4)
      (.cons (by decide : Challenge.MOGraph.Adj 4 7) .nil)
  have hup := SimpleGraph.dist_le p
  have hlo := p.reachable.one_lt_dist_of_ne_of_not_adj (by decide) (by decide)
  have hp : p.length = 2 := rfl
  rw [hp] at hup
  omega

theorem MO_not_distanceHereditary : ¬ Challenge.IsDistanceHereditary Challenge.MOGraph := by
  rintro ⟨_, h⟩
  have heq := h MOSet MO_induced_connected ⟨6, by decide⟩ ⟨7, by decide⟩
  rw [MO_induced_dist, MO_dist_6_7] at heq
  revert heq
  decide

/-! The G1 induced path is `3–1–0–4–5`. -/
def G1Set : Set (Fin 8) := {x | x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 4 ∨ x = 5}
local instance : DecidablePred (· ∈ G1Set) := fun x =>
  inferInstanceAs (Decidable (x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 4 ∨ x = 5))
local instance : Nonempty G1Set := ⟨⟨0, by decide⟩⟩
local instance : DecidableRel (Challenge.G1.induce G1Set).Adj := fun x y =>
  inferInstanceAs (Decidable (Challenge.G1.Adj x.val y.val))

def G1Position : Fin 8 → ℕ := ![2, 1, 0, 0, 3, 4, 0, 0]
def DG1 (u v : G1Set) : ℕ := lineDist (G1Position u.val) (G1Position v.val)

theorem G1_induced_dist : ∀ u v, (Challenge.G1.induce G1Set).dist u v = DG1 u v :=
  HKOTriameter.dist_eq_of_certificate (Challenge.G1.induce G1Set) DG1
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem G1_induced_connected : (Challenge.G1.induce G1Set).Connected :=
  HKOTriameter.connected_of_dist _ fun x y hxy => by
    rw [G1_induced_dist]
    revert x y
    decide

theorem G1_not_distanceHereditary : ¬ Challenge.IsDistanceHereditary Challenge.G1 := by
  rintro ⟨_, h⟩
  have heq := h G1Set G1_induced_connected ⟨3, by decide⟩ ⟨5, by decide⟩
  rw [G1_induced_dist] at heq
  change (4 : ℕ) = Challenge.G1.dist 3 5 at heq
  have hd : Challenge.G1.dist 3 5 = HKOTriameter.D1 3 5 := HKOTriameter.G1_dist 3 5
  rw [hd] at heq
  revert heq
  decide

/-! The HKO Figure 2 induced path is `4–3–2–1–0–6`. -/
def Fig2Set : Set (Fin 12) := {x | x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 6}
local instance : DecidablePred (· ∈ Fig2Set) := fun x =>
  inferInstanceAs (Decidable (x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 6))
local instance : Nonempty Fig2Set := ⟨⟨0, by decide⟩⟩
local instance : DecidableRel (Challenge.HKOFig2.induce Fig2Set).Adj := fun x y =>
  inferInstanceAs (Decidable (Challenge.HKOFig2.Adj x.val y.val))

def Fig2Position : Fin 12 → ℕ := ![4, 3, 2, 1, 0, 0, 5, 0, 0, 0, 0, 0]
def DFig2 (u v : Fig2Set) : ℕ := lineDist (Fig2Position u.val) (Fig2Position v.val)

theorem Fig2_induced_dist :
    ∀ u v, (Challenge.HKOFig2.induce Fig2Set).dist u v = DFig2 u v :=
  HKOTriameter.dist_eq_of_certificate (Challenge.HKOFig2.induce Fig2Set) DFig2
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem Fig2_induced_connected : (Challenge.HKOFig2.induce Fig2Set).Connected :=
  HKOTriameter.connected_of_dist _ fun x y hxy => by
    rw [Fig2_induced_dist]
    revert x y
    decide

theorem HKOFig2_not_distanceHereditary :
    ¬ Challenge.IsDistanceHereditary Challenge.HKOFig2 := by
  rintro ⟨_, h⟩
  have heq := h Fig2Set Fig2_induced_connected ⟨4, by decide⟩ ⟨6, by decide⟩
  rw [Fig2_induced_dist, HKOFig2Proof.dist] at heq
  revert heq
  decide

end NonDHExamples

theorem check_Sec3_MO_notDH : Challenge.Sec3_MO_notDH :=
  ⟨NonDHExamples.MO_path_edges, NonDHExamples.MO_dist_6_7,
    NonDHExamples.MO_not_distanceHereditary⟩

#print axioms NonDHExamples.G1_not_distanceHereditary
#print axioms NonDHExamples.HKOFig2_not_distanceHereditary
#print axioms check_Sec3_MO_notDH

end CodexPaper4
