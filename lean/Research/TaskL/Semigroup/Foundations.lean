import Research.TaskL.Semigroup.FBase

namespace TaskL.Semigroup
open Challenge

variable {S : AddSubmonoid ℕ} {D E : Finset (AddSubmonoid ℕ)}

theorem Represents.cover (h : Represents S D) : Cover S D := by
  intro g hg
  by_contra! hn
  exact hg.1 ((h g).2 hn)

theorem represents_of_cover (hS : Numerical S) (hD : ∀ Q ∈ D, S ≤ Q)
    (hc : Cover S D) : Represents S D := by
  classical
  intro n
  refine ⟨fun hn Q hQ ↦ hD Q hQ hn, ?_⟩
  intro hn
  by_contra hnot
  let B := (gaps S).filter (fun x ↦ ∀ Q ∈ D, x ∈ Q)
  have hB : B.Nonempty := ⟨n, Finset.mem_filter.mpr ⟨(mem_gaps hS).2 hnot, hn⟩⟩
  let g := B.max' hB
  have hgB : g ∈ B := B.max'_mem hB
  obtain ⟨hgGap, hgAll⟩ := Finset.mem_filter.mp hgB
  have hg : g ∉ S := (mem_gaps hS).1 hgGap
  have hp : 0 < g := Nat.pos_of_ne_zero (fun e ↦ hg (e ▸ S.zero_mem))
  have larger : ∀ x, g < x → (∀ Q ∈ D, x ∈ Q) → x ∈ S := by
    intro x hx hxD
    by_contra hxS
    have hxB : x ∈ B := Finset.mem_filter.mpr ⟨(mem_gaps hS).2 hxS, hxD⟩
    exact hx.not_ge (Finset.le_max' _ _ hxB)
  have hspecial : Special S g := by
    refine ⟨hg, larger _ (by omega) (fun Q hQ ↦ Q.add_mem (hgAll Q hQ) (hgAll Q hQ)), ?_⟩
    intro s hs hpos
    exact larger _ (by omega) (fun Q hQ ↦ Q.add_mem (hgAll Q hQ) (hD Q hQ hs))
  obtain ⟨Q, hQD, hnil⟩ := hc g hspecial
  exact hnil (hgAll Q hQD)

theorem decomp_iff (hS : Numerical S) :
    Decomposition S D ↔ Eligible S D ∧ Cover S D ∧ ∀ E ⊂ D, ¬ Cover S E := by
  constructor
  · rintro ⟨hir, hrep, hmin⟩
    have hover : ∀ Q ∈ D, S ≤ Q := fun Q hQ _ hn ↦ (hrep _).1 hn Q hQ
    refine ⟨fun Q hQ ↦ ⟨hir Q hQ, hover Q hQ⟩, Represents.cover hrep, ?_⟩
    intro E he hcov
    exact hmin E he (represents_of_cover hS (fun Q hQ ↦ hover Q (he.le hQ)) hcov)
  · rintro ⟨hel, hcov, hmin⟩
    refine ⟨fun Q hQ ↦ (hel Q hQ).1, represents_of_cover hS (fun Q hQ ↦ (hel Q hQ).2) hcov, ?_⟩
    intro E he hrep
    exact hmin E he (Represents.cover hrep)

theorem exists_minimal_subcover (hS : Numerical S) (hel : Eligible S D) (hc : Cover S D) :
    ∃ E ⊆ D, Decomposition S E := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ E ⊆ D, Cover S E ∧ E.card = n
  have hP : ∃ n, P n := ⟨D.card, D, fun _ h ↦ h, hc, rfl⟩
  obtain ⟨E, he, hcov, hcard⟩ := Nat.find_spec hP
  refine ⟨E, he, (decomp_iff hS).2 ⟨fun Q hQ ↦ hel Q (he hQ), hcov, ?_⟩⟩
  intro F hfe hcf
  have hP' : P F.card := ⟨F, hfe.le.trans he, hcf, rfl⟩
  have hlt : F.card < E.card := Finset.card_lt_card hfe
  exact (Nat.find_min' hP hP').not_gt (hcard ▸ hlt)

end TaskL.Semigroup
