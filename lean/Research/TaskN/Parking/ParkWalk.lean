import Research.TaskN.Parking.ParkSums
import Research.TaskN.Parking.SpacingWord

namespace TaskN.Parking
open Challenge

/-- Positions visited by a walk with the given nonnegative increments. -/
def points : List ℕ → Finset ℕ
  | [] => {0}
  | v :: vs => insert 0 ((points vs).image (fun t => v+t))

@[simp] theorem point_cons (x : ℕ) (s : List ℕ) (v : ℕ) :
    v ∈ points (x::s) ↔ v=0 ∨ ∃ w ∈ points s, x+w=v := by simp [points]

@[simp] theorem zero_point (s : List ℕ) : 0 ∈ points s := by
  cases s <;> simp [points]

theorem end_point (s : List ℕ) : s.sum ∈ points s := by
  induction s with
  | nil => simp [points]
  | cons x s ih => exact (point_cons ..).2 (Or.inr ⟨_,ih,rfl⟩)

theorem point_bound {s : List ℕ} {v : ℕ} (hv : v ∈ points s) : v ≤ s.sum := by
  induction s generalizing v with
  | nil => simpa [points] using hv
  | cons x s ih =>
    rcases (point_cons ..).1 hv with he | ⟨u,hu,rfl⟩
    · omega
    · exact Nat.add_le_add_left (ih hu) x

theorem point_append (s q : List ℕ) (v : ℕ) : v ∈ points (s++q) ↔
    v ∈ points s ∨ ∃ w ∈ points q, s.sum+w=v := by
  induction s generalizing v with
  | nil => simp [points]; aesop
  | cons x s ih =>
    simp only [List.cons_append, List.sum_cons, point_cons]
    constructor
    · rintro (rfl | ⟨u,hu,rfl⟩)
      · exact Or.inl (Or.inl rfl)
      · rcases (ih _).1 hu with h | ⟨w,hw,rfl⟩
        · exact Or.inl (Or.inr ⟨_,h,rfl⟩)
        · exact Or.inr ⟨_,hw,by omega⟩
    · rintro ((rfl | ⟨u,hu,rfl⟩) | ⟨w,hw,rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨_,(ih u).2 (Or.inl hu),rfl⟩
      · exact Or.inr ⟨_,(ih _).2 (Or.inr ⟨_,hw,rfl⟩),by omega⟩

theorem walk_of_dominant (xs : List ℕ) (hd : dominant xs) :
    (ruler (jumps xs)).sum = xs.sum ∧
    positive (ruler (jumps xs)) ∧ points (ruler (jumps xs)) = subsetSums xs := by
  induction xs with
  | nil => simp [ruler,jumps,positive,points,subsetSums]
  | cons x xs ih =>
    change xs.sum < x ∧ dominant xs at hd
    obtain ⟨hl,hp,he⟩ := ih hd.2
    rw [jumps,ruler_append_one,List.append_assoc]
    simp only [List.singleton_append]
    constructor
    · simp only [List.sum_append,List.sum_cons,hl]; omega
    constructor
    · intro v hv
      simp only [List.mem_append,List.mem_cons] at hv
      rcases hv with h | rfl | h
      · exact hp _ h
      · omega
      · exact hp _ h
    · ext v
      rw [point_append,he,hl,subset_cons]
      constructor
      · rintro (h | ⟨w,hw,rfl⟩)
        · exact Or.inl h
        · rcases (point_cons ..).1 hw with rfl | ⟨u,hu,rfl⟩
          · exact Or.inl (by simpa using sum_mem_subsets xs)
          · rw [he] at hu
            exact Or.inr ⟨_,hu,by omega⟩
      · rintro (h | ⟨u,hu,rfl⟩)
        · exact Or.inl h
        · rw [←he] at hu
          exact Or.inr ⟨_,(point_cons ..).2 (Or.inr ⟨_,hu,rfl⟩),by omega⟩

theorem positive_tail {x : ℕ} {s : List ℕ} (h : positive (x::s)) : positive s :=
  fun v hv => h v (List.mem_cons_of_mem _ hv)

theorem points_injective (s q : List ℕ) (hs : positive s) (hq : positive q)
    (he : points s = points q) : s=q := by
  induction s generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons y q =>
      have hm : y ∈ points (y::q) := (point_cons ..).2 (Or.inr ⟨0,zero_point _,by simp⟩)
      rw [←he] at hm
      have hy : 0<y := hq _ (by simp)
      simp [points] at hm
      omega
  | cons x s ih =>
    have hx : 0<x := hs _ (by simp)
    have hm : x ∈ points (x::s) := (point_cons ..).2 (Or.inr ⟨0,zero_point _,by simp⟩)
    cases q with
    | nil =>
      rw [he] at hm
      simp [points] at hm
      omega
    | cons y q =>
      have hy : 0<y := hq _ (by simp)
      have hym : y ∈ points (y::q) := (point_cons ..).2 (Or.inr ⟨0,zero_point _,by simp⟩)
      rw [he] at hm
      rw [←he] at hym
      obtain ⟨u,_,hu⟩ := ((point_cons ..).1 hm).resolve_left (by omega)
      obtain ⟨w,_,hw⟩ := ((point_cons ..).1 hym).resolve_left (by omega)
      have hxy : x=y := by omega
      cases hxy
      congr 1
      apply ih q (positive_tail hs) (positive_tail hq)
      ext v
      have hiff : x+v ∈ points (x::s) ↔ x+v ∈ points (x::q) := by rw [he]
      simpa [point_cons,show x ≠ 0 by omega] using hiff

theorem mirror_point (s : List ℕ) {v : ℕ} (hv : v ∈ points s) :
    s.sum-v ∈ points s.reverse := by
  induction s generalizing v with
  | nil => simp [points]
  | cons x s ih =>
    rw [List.reverse_cons,point_append,List.sum_cons]
    rcases (point_cons ..).1 hv with rfl | ⟨w,hw,rfl⟩
    · exact Or.inr ⟨x,by simp [points],by simp; omega⟩
    · exact Or.inl (by rw [show x+s.sum-(x+w) = s.sum-w by omega]; exact ih hw)

theorem symmetric_iff_pal {s : List ℕ} (hs : positive s) :
    (∀ v ∈ points s, s.sum-v ∈ points s) ↔ pal s := by
  constructor
  · intro h
    apply points_injective _ _ (fun v hv => hs v (List.mem_reverse.mp hv)) hs
    ext v
    constructor
    · intro hv
      have hx := mirror_point s.reverse hv
      have hlim := point_bound hv
      simp only [List.sum_reverse,List.reverse_reverse] at hx hlim
      simpa [Nat.sub_sub_self hlim] using h _ hx
    · intro hv
      have hx := mirror_point s (h v hv)
      simpa [Nat.sub_sub_self (point_bound hv)] using hx
  · intro h v hv
    have hm := mirror_point s hv
    change s.reverse=s at h
    rwa [h] at hm

end TaskN.Parking
