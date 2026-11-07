import Research.Backfill.Paper2.Challenge

/-! A coefficientwise contraction theorem for scalar or indexed integer series.
Finite jets stabilize; no topology, native execution, or existence premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.XadicFixedPoint
open PowerSeries
variable {I : Type*} {R : Type*} [CommRing R]

def Jet (n : ℕ) (A B : I → PowerSeries R) : Prop :=
  ∀ i j, j < n → coeff j (A i) = coeff j (B i)

private theorem jet_refl (n : ℕ) (A : I → PowerSeries R) : Jet n A A := by
  intro i j hj
  rfl

private theorem jet_symm {n : ℕ} {A B : I → PowerSeries R} (h : Jet n A B) : Jet n B A := by
  intro i j hj
  exact (h i j hj).symm

private theorem jet_trans {n : ℕ} {A B C : I → PowerSeries R}
    (h : Jet n A B) (g : Jet n B C) : Jet n A C := by
  intro i j hj
  exact (h i j hj).trans (g i j hj)

private theorem jet_mono {m n : ℕ} {A B : I → PowerSeries R}
    (hmn : m ≤ n) (h : Jet n A B) : Jet m A B := by
  intro i j hj
  exact h i j (lt_of_lt_of_le hj hmn)

def step (Φ : (I → PowerSeries R) → I → PowerSeries R) (seed : I → PowerSeries R) :
    ℕ → I → PowerSeries R
  | 0 => seed
  | n + 1 => Φ (step Φ seed n)

theorem existsUnique_fixed_seed (N : ℕ) (seed : I → PowerSeries R)
    (Φ : (I → PowerSeries R) → I → PowerSeries R)
    (hpres : ∀ A, Jet N A seed → Jet N (Φ A) seed)
    (hcontract : ∀ n, N ≤ n → ∀ A B, Jet N A seed → Jet N B seed →
      Jet n A B → Jet (n + 1) (Φ A) (Φ B)) :
    ∃! F : I → PowerSeries R, Jet N F seed ∧ Φ F = F := by
  let S := step Φ seed
  have hs : ∀ n, Jet N (S n) seed := by
    intro n
    induction n with
    | zero => exact jet_refl N seed
    | succ n ih => exact hpres (S n) ih
  have hadj : ∀ n, Jet (N + n) (S n) (S (n + 1)) := by
    intro n
    induction n with
    | zero => simpa only [S, step, Nat.add_zero] using jet_symm (hs 1)
    | succ n ih =>
      have h := hcontract (N + n) (by omega) (S n) (S (n + 1)) (hs n) (hs (n + 1)) ih
      simpa only [S, step, Nat.add_succ] using h
  have hstable : ∀ n k, n ≤ k → Jet (N + n) (S n) (S k) := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => exact jet_refl _ _
    | succ k hnk ih =>
      exact jet_trans ih (jet_mono (by omega) (hadj k))
  let F : I → PowerSeries R := fun i => PowerSeries.mk fun j => coeff j (S (j + 1) i)
  have hF : ∀ n, Jet (N + n) F (S n) := by
    intro n i j hj
    dsimp only [F]
    rw [coeff_mk]
    rcases le_total (j + 1) n with hle | hle
    · exact hstable (j + 1) n hle i j (by omega)
    · exact (hstable n (j + 1) hle i j hj).symm
  have hfseed : Jet N F seed := by simpa only [S, step, Nat.add_zero] using hF 0
  have hfix : Φ F = F := by
    funext i
    apply PowerSeries.ext
    intro j
    have h := hcontract (N + (j + 1)) (by omega) F (S (j + 1)) hfseed (hs (j + 1))
      (hF (j + 1))
    have hp := h i j (by omega)
    have hq := hF (j + 2) i j (by omega)
    change coeff j (Φ F i) = coeff j (S (j + 2) i) at hp
    exact hp.trans hq.symm
  refine ⟨F, ⟨hfseed, hfix⟩, ?_⟩
  rintro G ⟨hgseed, hgfix⟩
  have hfg : ∀ n, Jet (N + n) G F := by
    intro n
    induction n with
    | zero => exact jet_trans hgseed (jet_symm hfseed)
    | succ n ih =>
      have h := hcontract (N + n) (by omega) G F hgseed hfseed ih
      rw [hgfix, hfix] at h
      simpa only [Nat.add_succ] using h
  funext i
  apply PowerSeries.ext
  intro j
  exact hfg (j + 1) i j (by omega)

end BackfillPaper2.XadicFixedPoint
#print axioms BackfillPaper2.XadicFixedPoint.existsUnique_fixed_seed
