import Research.TaskN.Parking.Challenge

namespace TaskN.Parking
open Challenge

def pairs (x : ℕ) (s : List ℕ) : List ℕ := s.flatMap fun y => [x,y]

def stretch (x : ℕ) (s : List ℕ) : List ℕ := pairs x s ++ [x]

def ruler : List ℕ → List ℕ
  | [] => []
  | x :: xs => stretch x (ruler xs)

def lead (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | y :: ys => if y=x then 1+lead x ys else 0

def pal (s : List ℕ) : Prop := s.reverse = s

@[simp] theorem pairs_nil (x : ℕ) : pairs x [] = [] := rfl
@[simp] theorem pairs_cons (x y : ℕ) (s : List ℕ) :
    pairs x (y::s) = x::y::pairs x s := rfl
@[simp] theorem pairs_append (x : ℕ) (s t : List ℕ) :
    pairs x (s++t) = pairs x s ++ pairs x t := by simp [pairs]
@[simp] theorem length_pairs (x : ℕ) (s : List ℕ) : (pairs x s).length = 2*s.length := by
  induction s with
  | nil => simp
  | cons y ys ih => simp only [pairs_cons,List.length_cons,ih]; omega

@[simp] theorem stretch_nil (x : ℕ) : stretch x [] = [x] := rfl
@[simp] theorem stretch_cons (x y : ℕ) (s : List ℕ) :
    stretch x (y::s) = x::y::stretch x s := rfl
@[simp] theorem stretch_append_one (x y : ℕ) (s : List ℕ) :
    stretch x (s++[y]) = stretch x s ++ [y,x] := by simp [stretch,List.append_assoc]
@[simp] theorem length_stretch (x : ℕ) (s : List ℕ) :
    (stretch x s).length = 2*s.length+1 := by simp [stretch]

theorem ruler_append_one (h : List ℕ) (u : ℕ) :
    ruler (h++[u]) = ruler h ++ [u] ++ ruler h := by
  induction h with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,ruler,ih]
    simp [stretch,List.append_assoc]

theorem reverse_stretch (x : ℕ) (s : List ℕ) :
    (stretch x s).reverse = stretch x s.reverse := by
  induction s with
  | nil => simp
  | cons y ys ih => simp [ih,List.append_assoc]

theorem stretch_injective (x : ℕ) : Function.Injective (stretch x) := by
  intro s
  induction s with
  | nil => intro q h; cases q <;> simp_all
  | cons y ys ih =>
    intro q h
    cases q with
    | nil => simp at h
    | cons v vs =>
      simp only [stretch_cons,List.cons.injEq,true_and] at h
      obtain ⟨rfl,h⟩ := h
      rw [ih h]

theorem pal_stretch (x : ℕ) (s : List ℕ) : pal (stretch x s) ↔ pal s := by
  change (stretch x s).reverse = _ ↔ _
  rw [reverse_stretch]
  exact ⟨fun h => stretch_injective x h,fun h => congrArg (stretch x) h⟩

theorem reverse_pairs (x : ℕ) (s : List ℕ) :
    (pairs x s).reverse = s.reverse.flatMap (fun y => [y,x]) := by
  induction s with
  | nil => simp
  | cons y ys ih => simp [ih,List.append_assoc]

theorem dual_pairs_eq (x : ℕ) (s t : List ℕ) (h : pairs x s = t.flatMap (fun y => [y,x])) :
    ∀ y ∈ s, y=x := by
  induction s generalizing t with
  | nil => simp
  | cons z zs ih =>
    cases t with
    | nil => simp at h
    | cons y ys =>
      simp only [pairs_cons,List.flatMap_cons,List.cons_append,List.nil_append,List.cons.injEq] at h
      rcases h with ⟨_,hz,hl⟩
      simpa only [List.forall_mem_cons] using And.intro hz (ih ys hl)

theorem pal_pairs (x : ℕ) (s : List ℕ) : pal (pairs x s) ↔ ∀ y ∈ s, y=x := by
  constructor
  · intro h
    apply dual_pairs_eq x s s.reverse
    exact (reverse_pairs x s) ▸ h.symm
  · intro h
    have heq : s = List.replicate s.length x := by
      induction s with
      | nil => rfl
      | cons y ys ih =>
        simp only [List.forall_mem_cons] at h
        rw [List.length_cons,List.replicate_succ,← ih h.2,h.1]
    have hh : ∀ i : ℕ, pairs x (List.replicate i x) = List.replicate (2*i) x := by
      intro i; induction i with
      | zero => rfl
      | succ k ih =>
        rw [List.replicate_succ,pairs_cons,ih,show 2*(k+1)=2*k+1+1 by omega]
        simp [List.replicate_succ]
    rw [heq,hh]
    simp [pal]

theorem take_stretch_even (x : ℕ) (s : List ℕ) (i : ℕ) (hi : i ≤ s.length) :
    (stretch x s).take (2*i) = pairs x (s.take i) := by
  induction i generalizing s with
  | zero => simp
  | succ i ih =>
    cases s with
    | nil => simp at hi
    | cons y ys =>
      rw [show 2*(i+1)=2*i+1+1 by omega,stretch_cons]
      simp only [List.take_succ_cons,pairs_cons,List.cons.injEq,true_and]
      exact ih ys (by simpa using hi)

theorem take_stretch_odd (x : ℕ) (s : List ℕ) (i : ℕ) (hi : i ≤ s.length) :
    (stretch x s).take (2*i+1) = stretch x (s.take i) := by
  induction i generalizing s with
  | zero => cases s <;> simp
  | succ i ih =>
    cases s with
    | nil => simp at hi
    | cons y ys =>
      rw [show 2*(i+1)+1=(2*i+1)+1+1 by omega,stretch_cons]
      simp only [List.take_succ_cons,stretch_cons,List.cons.injEq,true_and]
      exact ih ys (by simpa using hi)

theorem lead_le_length (x : ℕ) (s : List ℕ) : lead x s ≤ s.length := by
  induction s with
  | nil => simp [lead]
  | cons y ys ih => simp only [lead,List.length_cons]; split <;> omega

theorem all_take_iff (x : ℕ) (s : List ℕ) (i : ℕ) (hi : i ≤ s.length) :
    (∀ y ∈ s.take i, y=x) ↔ i ≤ lead x s := by
  induction i generalizing s with
  | zero => simp
  | succ i ih =>
    cases s with
    | nil => simp at hi
    | cons y ys =>
      simp only [List.take_succ_cons,List.forall_mem_cons,lead]
      by_cases he : y=x
      · simp only [he,ite_true,true_and,ih ys (by simpa using hi)]; omega
      · simp [he]
end TaskN.Parking
