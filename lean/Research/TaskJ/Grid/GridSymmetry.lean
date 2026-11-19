import Research.TaskJ.Grid.GridPathEdges

namespace Grid.Pad

open Challenge

def axisAntipode (d x : ℕ) : ℕ := d - 1 - x

def antipode (ds x : List ℕ) : Point := List.zipWith axisAntipode ds x

@[simp] theorem antipode_cons (d a : ℕ) (ds x : List ℕ) :
    antipode (d::ds) (a::x) = axisAntipode d a :: antipode ds x := rfl

@[simp] theorem axisAntipode_twice {d x : ℕ} (h : x < d) :
    axisAntipode d (axisAntipode d x) = x := by unfold axisAntipode; omega

theorem vertex_cons {d a : ℕ} {ds x : List ℕ} :
    a::x ∈ vertices (d::ds) ↔ a < d ∧ x ∈ vertices ds := by simp [vertices]

theorem vertex_cases {d : ℕ} {ds p : List ℕ} (h : p ∈ vertices (d::ds)) :
    ∃ a x, p = a::x ∧ a < d ∧ x ∈ vertices ds := by
  simp only [vertices, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨a,ha,x,hx,rfl⟩ := h
  exact ⟨a,x,rfl,ha,hx⟩

theorem antipode_mem {ds x : List ℕ} (hx : x ∈ vertices ds) : antipode ds x ∈ vertices ds := by
  induction ds generalizing x with
  | nil => simp [antipode,vertices]
  | cons n ns ih =>
    obtain ⟨a,x,rfl,ha,hx⟩ := vertex_cases hx
    apply vertex_cons.mpr
    exact ⟨by unfold axisAntipode; omega, ih hx⟩

theorem antipode_involutive {ds x : List ℕ} (hx : x ∈ vertices ds) :
    antipode ds (antipode ds x) = x := by
  induction ds generalizing x with
  | nil => simp [vertices] at hx; subst x; rfl
  | cons d ds ih =>
    obtain ⟨a,x,rfl,ha,hx⟩ := vertex_cases hx
    simp [ha,ih hx]

theorem axis_radius_antipode {d a : ℕ} (h : a < d) :
    axisRadius d (axisAntipode d a) = axisRadius d a := by
  unfold axisRadius axisAntipode
  simp only [abs_eq_max_neg]
  omega

theorem radius_antipode {ds x : List ℕ} (hx : x ∈ vertices ds) :
    radius ds (antipode ds x) = radius ds x := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨a,x,rfl,ha,hx⟩ := vertex_cases hx
    simp [axis_radius_antipode ha,ih hx]

theorem dist_antipode {ds x y : List ℕ} (hx : x ∈ vertices ds) (hy : y ∈ vertices ds) :
    manhattan (antipode ds x) (antipode ds y) = manhattan x y := by
  induction ds generalizing x y with
  | nil => simp [vertices] at hx hy; subst_vars; rfl
  | cons d ds ih =>
    obtain ⟨a,x,rfl,ha,hx⟩ := vertex_cases hx
    obtain ⟨b,y,rfl,hb,hy⟩ := vertex_cases hy
    simp only [antipode_cons,manhattan_cons,ih hx hy]
    unfold axisAntipode Nat.dist
    omega

theorem defect_antipode {ds x y : List ℕ} (hx : x ∈ vertices ds) (hy : y ∈ vertices ds) :
    defect ds (antipode ds x) (antipode ds y) = defect ds x y := by
  simp [defect,radius_antipode hx,radius_antipode hy,dist_antipode hx hy]

theorem defect_to_antipode {ds x : List ℕ} (hx : x ∈ vertices ds) :
    defect ds x (antipode ds x) = 0 := by
  induction ds generalizing x with
  | nil => simp [vertices] at hx; subst x; rfl
  | cons d ds ih =>
    obtain ⟨a,x,rfl,ha,hx⟩ := vertex_cases hx
    simp only [antipode_cons,defect_cons,ih hx,add_zero,axis_radius_antipode ha]
    unfold axisRadius axisAntipode Nat.dist
    simp only [abs_eq_max_neg, Nat.cast_add]
    omega

theorem defect_comm (ds x y : List ℕ) : defect ds x y = defect ds y x := by
  suffices manhattan x y = manhattan y x by simp [defect,this,add_comm]
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a x ih => cases y with
    | nil => rfl
    | cons b y => simp [ih y, Nat.dist_comm]

/-- Coordinates are classified by their signs relative to the midpoint. -/
def axisSign (d x : ℕ) : ℤ := if 2*x+1 < d then -1 else if d < 2*x+1 then 1 else 0

def signature (ds x : List ℕ) : List ℤ := List.zipWith axisSign ds x

theorem axis_transfer (d a b c : ℕ) (hs : axisSign d a = axisSign d b)
    (h : axisRadius d a + axisRadius d c - 2 * (Nat.dist a c : ℤ) = 0) :
    axisRadius d b + axisRadius d c - 2 * (Nat.dist b c : ℤ) = 0 := by
  unfold axisSign at hs
  unfold axisRadius Nat.dist at *
  simp only [abs_eq_max_neg, Nat.cast_add] at *
  split_ifs at hs <;> omega

theorem defect_transfer {ds x y z : List ℕ} (hx : x ∈ vertices ds) (hy : y ∈ vertices ds)
    (hz : z ∈ vertices ds) (hs : signature ds x = signature ds y) (hd : defect ds x z = 0) :
    defect ds y z = 0 := by
  induction ds generalizing x y z with
  | nil => simp [vertices] at hx hy hz; subst_vars; rfl
  | cons d ds ih =>
    obtain ⟨a,x,rfl,_,hx⟩ := vertex_cases hx
    obtain ⟨b,y,rfl,_,hy⟩ := vertex_cases hy
    obtain ⟨c,z,rfl,_,hz⟩ := vertex_cases hz
    obtain ⟨hs₁,hs₂⟩ := List.cons.inj hs
    rw [defect_cons] at hd ⊢
    have hb := Grid.axis_dist_le d a c
    have ht := Grid.defect_nonneg (length_of_mem_vertices hx) (length_of_mem_vertices hz)
    rw [ih hx hy hz hs₂ (by omega), axis_transfer d a b c hs₁ (by omega)]
    simp

end Grid.Pad
