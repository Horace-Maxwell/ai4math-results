import Mathlib
import Research.Backfill.Paper8.Proof.Region.Defs

/-!
# Region search: the enumeration (agent `region`)

`enum` is the list of all trees of all supports. This module characterizes membership in
`treesAux`, `supports` and `enum`, proves that `enum` has no duplicates, and splits `enum` into
the chunks `chunk lo len` that are evaluated by the kernel in `Research.Backfill.Paper8.Proof.Region.Chunk1`–`Chunk10`.
-/

set_option autoImplicit false

namespace P8Region

theorem mem_treesAux (Bl : List ℕ) : ∀ (rest : List ℕ) (T : List (ℕ × ℕ)),
    T ∈ treesAux Bl rest ↔ T.map Prod.fst = rest ∧ ∀ p ∈ T, p.2 ∈ choices Bl p.1
  | [], T => by
    cases T with
    | nil => simp [treesAux]
    | cons p T => simp [treesAux]
  | b :: rest, T => by
    rw [treesAux, List.mem_flatMap]
    constructor
    · rintro ⟨k, hk, hT⟩
      rw [List.mem_map] at hT
      obtain ⟨T', hT', rfl⟩ := hT
      obtain ⟨h1, h2⟩ := (mem_treesAux Bl rest T').1 hT'
      refine ⟨by simp [h1], ?_⟩
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hk
      · exact h2 p hp
    · rintro ⟨h1, h2⟩
      cases T with
      | nil => simp at h1
      | cons p T' =>
        simp only [List.map_cons, List.cons.injEq] at h1
        have hp := h2 p List.mem_cons_self
        rw [h1.1] at hp
        refine ⟨p.2, hp, ?_⟩
        rw [List.mem_map]
        refine ⟨T', (mem_treesAux Bl rest T').2
          ⟨h1.2, fun q hq => h2 q (List.mem_cons_of_mem _ hq)⟩, ?_⟩
        rw [← h1.1]

theorem nodup_choices (Bl : List ℕ) (b : ℕ) : (choices Bl b).Nodup := by
  unfold choices
  split_ifs
  · exact List.nodup_range' ..
  · exact (List.nodup_range' ..).filter _

theorem nodup_treesAux (Bl : List ℕ) : ∀ rest, (treesAux Bl rest).Nodup
  | [] => by simp [treesAux]
  | b :: rest => by
    rw [treesAux, List.nodup_flatMap]
    refine ⟨fun k _ => (nodup_treesAux Bl rest).map (fun T₁ T₂ h => by simpa using h), ?_⟩
    refine (nodup_choices Bl b).imp ?_
    intro k₁ k₂ hne
    rw [Function.onFun, List.disjoint_left]
    intro T h1 h2
    rw [List.mem_map] at h1 h2
    obtain ⟨T₁, -, rfl⟩ := h1
    obtain ⟨T₂, -, h⟩ := h2
    simp only [List.cons.injEq, Prod.mk.injEq, true_and] at h
    exact hne h.1.symm

theorem mem_supports (Bl : List ℕ) : Bl ∈ supports ↔ Bl.Sublist (List.range 13) ∧ 2 ≤ bsOf Bl := by
  simp [supports, List.mem_filter, List.mem_sublists]

theorem nodup_supports : supports.Nodup :=
  (List.nodup_sublists.2 List.nodup_range).filter _

/-- All trees of the region (before the identification with multisets). -/
def enum : List (List (ℕ × ℕ)) := supports.flatMap treesOf

theorem mem_enum (T : List (ℕ × ℕ)) : T ∈ enum ↔
    (T.map Prod.fst).Sublist (List.range 13) ∧ 2 ≤ bsOf (T.map Prod.fst) ∧
      ∀ p ∈ T, p.2 ∈ choices (T.map Prod.fst) p.1 := by
  rw [enum, List.mem_flatMap]
  constructor
  · rintro ⟨Bl, hBl, hT⟩
    rw [treesOf, mem_treesAux] at hT
    obtain ⟨h1, h2⟩ := hT
    rw [mem_supports] at hBl
    subst h1
    exact ⟨hBl.1, hBl.2, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨T.map Prod.fst, (mem_supports _).2 ⟨h1, h2⟩, (mem_treesAux _ _ _).2 ⟨rfl, h3⟩⟩

theorem nodup_enum : enum.Nodup := by
  rw [enum, List.nodup_flatMap]
  refine ⟨fun Bl _ => nodup_treesAux Bl Bl, nodup_supports.imp ?_⟩
  intro Bl₁ Bl₂ hne
  rw [Function.onFun, List.disjoint_left]
  intro T h1 h2
  rw [treesOf, mem_treesAux] at h1 h2
  exact hne (h1.1.symm.trans h2.1)

theorem chunk_split (lo a b : ℕ) : chunk lo (a + b) = chunk lo a ++ chunk (lo + a) b := by
  rw [chunk, chunk, chunk, List.take_add, List.flatMap_append, List.drop_drop]

theorem enum_eq_chunk : enum = chunk 0 10000 := by
  have h1 : supports.length ≤ (List.range 13).sublists.length := List.length_filter_le _ _
  rw [List.length_sublists, List.length_range] at h1
  rw [enum, chunk, List.drop_zero, List.take_of_length_le (by omega)]

theorem stats_append {l₁ l₂ : List (List (ℕ × ℕ))} {n₁ n₂ : ℕ}
    (h₁ : stats l₁ = (n₁, true)) (h₂ : stats l₂ = (n₂, true)) :
    stats (l₁ ++ l₂) = (n₁ + n₂, true) := by
  simp only [stats, Prod.mk.injEq] at h₁ h₂ ⊢
  rw [List.length_append, List.all_append, h₁.1, h₂.1, h₁.2, h₂.2]
  simp

theorem stats_split {lo a b lo' ab n₁ n₂ n : ℕ} (hlo : lo + a = lo') (hab : a + b = ab)
    (hn : n₁ + n₂ = n) (h₁ : stats (chunk lo a) = (n₁, true))
    (h₂ : stats (chunk lo' b) = (n₂, true)) : stats (chunk lo ab) = (n, true) := by
  subst hlo hab hn
  rw [chunk_split]
  exact stats_append h₁ h₂

end P8Region
