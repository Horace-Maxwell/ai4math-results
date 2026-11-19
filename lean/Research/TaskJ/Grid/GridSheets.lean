import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Chain

/-! A Hamiltonian cycle on three copies of a given cyclic order. -/

namespace Grid.Sheets

inductive Sheet
  | lo | mid | hi
  deriving DecidableEq

open Sheet

def sheets : List Sheet := [lo, mid, hi]

/-- False exchanges the exterior sheets, true rotates the three sheets. -/
def step : Bool → Sheet → Sheet
  | false, lo => hi
  | false, mid => mid
  | false, hi => lo
  | true, lo => mid
  | true, mid => hi
  | true, hi => lo

def Cross (s t : Sheet) : Prop := ¬ (s = lo ∧ t = lo) ∧ ¬ (s = hi ∧ t = hi)

theorem cross_step (b : Bool) (s : Sheet) : Cross s (step b s) := by
  cases b <;> cases s <;> simp [Cross, step]

theorem step_perm (b : Bool) : (sheets.map (step b)).Perm sheets := by
  cases b <;> decide

@[simp] theorem flip_flip (s : Sheet) : step false (step false s) = s := by
  cases s <;> rfl

variable {α : Type*}

/-- Each vertex carries the change of sheet on its outgoing edge. -/
def wire : List α → List (α × Bool)
  | [] => []
  | [a] => [(a, false)]
  | [a,b] => [(a,false),(b,false)]
  | [a,b,c] => [(a,true),(b,false),(c,false)]
  | [a,b,c,d] => [(a,true),(b,true),(c,false),(d,false)]
  | a :: b :: c :: d :: e :: l => (a,false) :: (b,false) :: wire (c :: d :: e :: l)

theorem wire_points : ∀ l : List α, (wire l).map Prod.fst = l
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] => rfl
  | a :: b :: c :: d :: e :: l => by simp [wire, wire_points (c::d::e::l)]

def walk := fun (l : List (α × Bool)) (s : Sheet) =>
  let rec go (l : List (α × Bool)) (s : Sheet) : List (α × Sheet) :=
    match l with
    | [] => []
    | x :: xs => (x.1, s) :: go xs (step x.2 s)
  go l s

def finish : List (α × Bool) → Sheet → Sheet
  | [], s => s
  | x :: xs, s => finish xs (step x.2 s)

@[simp] theorem walk_nil (s : Sheet) : walk ([] : List (α × Bool)) s = [] := rfl

@[simp] theorem walk_cons (x : α × Bool) (xs) (s) :
    walk (x :: xs) s = (x.1,s) :: walk xs (step x.2 s) := rfl

theorem wire_monodromy : ∀ (l : List α), 3 ≤ l.length →
    ((∀ s, finish (wire l) s = step true s) ∨
     (∀ s, finish (wire l) s = step true (step true s)))
  | [], h | [_], h | [_,_], h => by simp_all
  | [a,b,c], _ => Or.inl (by intro s; cases s <;> rfl)
  | [a,b,c,d], _ => Or.inr (by intro s; cases s <;> rfl)
  | a::b::c::d::e::l, _ => by
      simpa [wire, finish] using wire_monodromy (c::d::e::l) (by simp)

theorem walk_cover (l : List (α × Bool)) :
    (sheets.flatMap (walk l)).Perm (l.flatMap (fun w => sheets.map ((w.1, ·)))) := by
  induction l with
  | nil => simp [sheets]
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    refine (List.map_append_flatMap_perm sheets (fun s => (x.1,s))
      (fun s => walk xs (step x.2 s))).symm.trans ?_
    apply List.Perm.append_left
    refine List.Perm.trans ?_ ih
    simpa [List.flatMap_map] using (step_perm x.2).flatMap_right (walk xs)

def orbit (l : List (α × Bool)) : List Sheet := [mid, finish l mid, finish l (finish l mid)]

theorem orbit_perm (l : List α) (h : 3 ≤ l.length) : (orbit (wire l)).Perm sheets := by
  rcases wire_monodromy l h with hh | hh
  · simp only [orbit, hh]
    decide
  · simp only [orbit, hh]
    decide

theorem orbit_closes (l : List α) (h : 3 ≤ l.length) :
    finish (wire l) (finish (wire l) (finish (wire l) mid)) = mid := by
  rcases wire_monodromy l h with hh | hh <;> simp only [hh] <;> rfl

def liftCycle (l : List α) : List (α × Sheet) :=
  (orbit (wire l)).flatMap (walk (wire l))

theorem liftCycle_perm (l : List α) (h : 3 ≤ l.length) :
    (liftCycle l).Perm (l.flatMap fun x => sheets.map ((x, ·))) := by
  apply ((orbit_perm l h).flatMap_right (walk (wire l))).trans
  have eq := congrArg (fun ll : List α => ll.flatMap (fun x => sheets.map ((x, ·)))) (wire_points l)
  exact (walk_cover (wire l)).trans (List.Perm.of_eq (by simpa [List.flatMap_map] using eq))

theorem walk_chain {R : α → α → Prop} (l : List (α × Bool)) (s : Sheet) (v : α)
    (h : (l.map Prod.fst ++ [v]).IsChain R) :
    (walk l s ++ [(v,finish l s)]).IsChain (fun x y => R x.1 y.1 ∧ Cross x.2 y.2) := by
  induction l generalizing s with
  | nil => simp [finish]
  | cons x xs ih =>
    cases xs with
    | nil =>
      simpa [finish] using And.intro (by simpa using h : R x.1 v) (cross_step x.2 s)
    | cons y ys =>
      simp only [List.map_cons, List.cons_append, List.isChain_cons_cons] at h
      simp only [walk_cons, finish, List.cons_append, List.isChain_cons_cons]
      refine ⟨⟨h.1,cross_step x.2 s⟩, ?_⟩
      simpa only [walk_cons, finish, List.cons_append] using ih (step x.2 s) h.2

theorem walk_append (a b : List (α × Bool)) (s : Sheet) :
    walk (a ++ b) s = walk a s ++ walk b (finish a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons x xs ih => simp [finish, ih]

theorem finish_append (a b : List (α × Bool)) (s : Sheet) :
    finish (a ++ b) s = finish b (finish a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons x xs ih => simp [finish, ih]

theorem wire_first (a : α) (as : List α) :
    ∃ b rest, wire (a :: as) = (a,b) :: rest := by
  have h := wire_points (a :: as)
  cases he : wire (a :: as) with
  | nil => simp [he] at h
  | cons x xs =>
    rw [he] at h
    obtain ⟨rfl, _⟩ := List.cons.inj h
    exact ⟨x.2, xs, rfl⟩

theorem wire_last : ∀ (l : List α), 3 ≤ l.length →
    ∃ v pre, l.getLast? = some v ∧ wire l = pre ++ [(v,false)]
  | [], h | [_], h | [_,_], h => by simp_all
  | [a,b,c], _ => ⟨c, [(a,true),(b,false)], rfl,rfl⟩
  | [a,b,c,d], _ => ⟨d, [(a,true),(b,true),(c,false)], rfl,rfl⟩
  | a::b::c::d::e::l, _ => by
      obtain ⟨z, pre, hz, hp⟩ := wire_last (c::d::e::l) (by simp)
      exact ⟨z, (a,false)::(b,false)::pre, by simpa using hz, by simp [wire,hp]⟩

theorem liftCycle_first (a : α) (as : List α) :
    (liftCycle (a :: as)).head? = some (a,mid) := by
  obtain ⟨b, xs, eq⟩ := wire_first a as
  simp [liftCycle, orbit, eq]

theorem liftCycle_last (l : List α) (h : 3 ≤ l.length) :
    (liftCycle l).getLast? = l.getLast?.map (fun x => (x,mid)) := by
  obtain ⟨v, pre, hz, hp⟩ := wire_last l h
  have hc := orbit_closes l h
  set s := finish (wire l) (finish (wire l) mid) with hs
  change finish (wire l) s = mid at hc
  rw [hp, finish_append] at hc
  change step false (finish pre s) = mid at hc
  have hp' := congrArg (step false) hc
  simp only [flip_flip] at hp'
  change finish pre s = mid at hp'
  rw [hz]
  change ((walk (wire l) mid ++ (walk (wire l) (finish (wire l) mid) ++
    (walk (wire l) s ++ [])))).getLast? = _
  rw [show walk (wire l) s = walk pre s ++ [(v, mid)] by rw [hp,walk_append,hp']; rfl]
  simp

private theorem join_chains {β : Type*} {R : β → β → Prop} {left right : List β} {a : β}
    (hl : (left ++ [a]).IsChain R) (hr : right.IsChain R) (hh : right.head? = some a) :
    (left ++ right).IsChain R := by
  apply hl.left_of_append.append hr
  intro x hx y hy
  rw [hh] at hy
  have eq : y = a := by simpa [eq_comm] using hy
  subst y
  exact (List.isChain_append.mp hl).2.2 x hx a (by simp)

theorem liftCycle_chain {R : α → α → Prop} (a : α) (as : List α)
    (hh : 3 ≤ (a::as).length) (h : ((a::as) ++ [a]).IsChain R) :
    (liftCycle (a::as) ++ [(a,mid)]).IsChain
      (fun x y => R x.1 y.1 ∧ Cross x.2 y.2) := by
  let w := wire (a::as)
  have hbase : (w.map Prod.fst ++ [a]).IsChain R := by simpa [w,wire_points] using h
  let s := finish w mid
  let t := finish w s
  have h₁ := walk_chain w mid a hbase
  have h₂ := walk_chain w s a hbase
  have h₃ := walk_chain w t a hbase
  change (walk w t ++ [(a,finish w t)]).IsChain _ at h₃
  rw [show finish w t = mid from orbit_closes _ hh] at h₃
  obtain ⟨b, xs, eq⟩ := wire_first a as
  have starts (z : Sheet) (rest : List (α × Sheet)) :
      (walk w z ++ rest).head? = some (a,z) := by simp [w,eq]
  have j₂ := join_chains h₂ h₃ (starts t _)
  have j₁ := join_chains h₁ j₂ (starts s _)
  simpa only [liftCycle, orbit, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc] using j₁

end Grid.Sheets
