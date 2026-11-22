import Research.TaskN.Parking.Challenge

namespace TaskN.Parking
open Challenge

def residual : List ℕ → ℕ → ℕ
  | [], r => r
  | x :: xs, r => residual xs (if x ≤ r then r-x else r)

@[simp] theorem residual_zero (xs : List ℕ) : residual xs 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [residual] using ih

private def gapState (lo gap used : ℕ) : Street :=
  (if gap = 0 then [] else [(lo,lo+gap)], used+gap)

private theorem parkOrdinary (len lo gap used : ℕ) :
    park 0 len (gapState lo gap used).1 (gapState lo gap used).2 =
      gapState (if len ≤ gap then lo+len else lo)
        (if len ≤ gap then gap-len else gap) (used+len) := by
  by_cases hz : gap = 0
  · subst gap
    simp [gapState,park]
  · by_cases hl : len ≤ gap
    · have hfit : lo + len ≤ lo + gap := by omega
      by_cases he : len = gap
      · subst len
        simp [gapState,park,hz,add_comm]
      · have hlt : lo + len < lo + gap := by omega
        have hpos : gap-len ≠ 0 := by omega
        simp [gapState,park,hz,hl,hfit,hlt,hpos]
    · have hnf : ¬ lo + len ≤ lo + gap := by omega
      simp [gapState,park,hz,hl,hnf]
      omega

private theorem ordinaryEnd (xs : List ℕ) (lo gap used : ℕ) :
    (drive (gapState lo gap used) (ordinary xs)).2 = used + xs.sum + residual xs gap := by
  induction xs generalizing lo gap used with
  | nil => simp [ordinary,drive,gapState,residual]
  | cons x xs ih =>
    change (drive (park 0 x (gapState lo gap used).1 (gapState lo gap used).2)
      (ordinary xs)).2 = _
    rw [parkOrdinary,ih]
    simp only [List.sum_cons, residual]
    omega

private theorem ordinaryPacked (xs : List ℕ) (used : ℕ) :
    drive ([],used) (ordinary xs) = ([],used+xs.sum) := by
  induction xs generalizing used with
  | nil => simp [drive,ordinary]
  | cons x xs ih =>
    change drive (park 0 x [] used) (ordinary xs) = _
    simp [park,ih,Nat.add_assoc]

private theorem specialOnPacked (t len used : ℕ) :
    park t len [] used = gapState used (t-used) (used+len) := by
  by_cases h : t ≤ used
  · simp [park,h,gapState,Nat.sub_eq_zero_of_le h]
  · have hp : t-used ≠ 0 := by omega
    simp [park,h,gapState,hp]
    omega

theorem allPositions_iff (ys : List ℕ) (t : ℕ) :
    allPositions ys t ↔
      ∀ (pre : List ℕ) (x : ℕ) (suf : List ℕ), ys = pre ++ x :: suf →
        residual suf (t-pre.sum) = 0 := by
  have h (pre : List ℕ) (x : ℕ) (suf : List ℕ) :
      (drive ([],0) (ordinary pre ++ (x,t) :: ordinary suf)).2 =
        (pre.sum + x) + suf.sum + residual suf (t-pre.sum) := by
    simp only [drive,List.foldl_append]
    change (drive (drive ([],0) (ordinary pre)) ((x,t) :: ordinary suf)).2 = _
    rw [ordinaryPacked]
    simp only [Nat.zero_add]
    change (drive (park t x [] pre.sum) (ordinary suf)).2 = _
    rw [specialOnPacked,ordinaryEnd]
  constructor <;> intro hp pre x suf he
  · specialize hp pre x suf he
    rw [h,he,List.sum_append,List.sum_cons] at hp
    omega
  · specialize hp pre x suf he
    rw [h,hp,he,List.sum_append,List.sum_cons]
    omega

end TaskN.Parking
