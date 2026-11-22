import Research.TaskP.PrimeMedialRacks.Challenge

namespace TaskP.PrimeMedialRacks

open Challenge

variable {α β γ : Type*} {op : Operation α} {op' : Operation β} {op'' : Operation γ}

theorem iso_symm (h : Isomorphic op op') : Isomorphic op' op := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, fun x y => e.injective (by simp [he])⟩

theorem iso_trans (h : Isomorphic op op') (h' : Isomorphic op' op'') :
    Isomorphic op op'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := h'
  exact ⟨e.trans f, fun x y => by simp [he, hf]⟩

theorem iso_rack (h : Isomorphic op op') (hr : IsRack op) : IsRack op' := by
  obtain ⟨e, he⟩ := h
  constructor
  · intro a
    obtain ⟨x, rfl⟩ := e.surjective a
    constructor
    · intro b c hb
      obtain ⟨y, rfl⟩ := e.surjective b
      obtain ⟨z, rfl⟩ := e.surjective c
      rw [← he, ← he] at hb
      exact congrArg e ((hr.1 x).1 (e.injective hb))
    · intro b
      obtain ⟨z, rfl⟩ := e.surjective b
      obtain ⟨y, hy⟩ := (hr.1 x).2 z
      exact ⟨e y, (he x y).symm.trans (congrArg e hy)⟩
  · intro a b c
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    obtain ⟨z, rfl⟩ := e.surjective c
    simpa only [he] using congrArg e (hr.2 x y z)

theorem iso_idempotent (h : Isomorphic op op') (hp : Idempotent op) : Idempotent op' := by
  obtain ⟨e, he⟩ := h
  intro a
  obtain ⟨x, rfl⟩ := e.surjective a
  simpa only [he] using congrArg e (hp x)

theorem iso_medial (h : Isomorphic op op') (hp : Medial op) : Medial op' := by
  obtain ⟨e, he⟩ := h
  intro a b c d
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨u, rfl⟩ := e.surjective b
  obtain ⟨v, rfl⟩ := e.surjective c
  obtain ⟨y, rfl⟩ := e.surjective d
  simpa only [he] using congrArg e (hp x u v y)

theorem iso_reductive (h : Isomorphic op op') (hp : TwoReductive op) : TwoReductive op' := by
  obtain ⟨e, he⟩ := h
  intro a b c d
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  obtain ⟨u, rfl⟩ := e.surjective c
  obtain ⟨v, rfl⟩ := e.surjective d
  simpa only [he] using congrArg e (hp x y u v)

theorem reductive_medial (hr : IsRack op) (hd : TwoReductive op) : Medial op := by
  have row (x u v : α) : op (op x u) v = op u v := by
    rw [hd x u u v]
    obtain ⟨w, rfl⟩ := (hr.1 u).2 v
    exact (hr.2 u u w).symm
  intro x u v y
  rw [row, row, hr.2 u v y, row]

end TaskP.PrimeMedialRacks
