import Research.Backfill.Paper1.Prop31WholeChain

/-! Static C1 and C2 branches, including k=0 and the singleton y=1. -/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace Prop31

lemma chain_surplus_term {a b k : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hab : Even (a + b)) {p q : ℝ} (hreg : Challenge.Regions p q)
    {Y : ℕ → ℕ → ℝ} (hY : Challenge.IsSignMat a b Y)
    {g : ℕ → ℝ} (hg : Challenge.IsSignVec a g) (hk : k ≤ b)
    (hlast : ∀ i ≤ a, Y i b = g i) (hchain : TailChain a b k Y g)
    {l : ℕ} (hl1 : 1 ≤ l) (hlk : l ≤ k) :
    Challenge.psiCol a b p q Y (b - l) =
      (q - 1) * (1 + nu q (b - l)) * Challenge.DeltaC a p g := by
  have hh := ((check_Lemma23 a b ha hb hab p q hreg Y hY).1 g hg k hk hlast hchain).2 l hl1 hlk
  have he : (b : ℤ) - l - 1 = ((b - l : ℕ) : ℤ) - 1 := by omega
  rwa [he, Additional.mu_pred_eq_nu] at hh

lemma tail_eta_sum (q Δ : ℝ) {b k : ℕ} (hk : k < b) :
    (∑ l ∈ Finset.Icc 1 k, (q - 1) * (1 + nu q (b - l)) * Δ) =
      ∑ n ∈ Finset.Icc 1 k,
        (q - 1) * (1 + Challenge.etaMap q n (nu q (b - (k + 1)))) * Δ := by
  apply Finset.sum_bij (fun l _ => k + 1 - l)
  · intro l hl
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hl
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro l hl m hm he
    obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    omega
  · intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    refine ⟨k + 1 - n, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro l hl
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hl
    rw [eta_nu, show b - (k + 1) + (k + 1 - l) = b - l by omega]

lemma C1_strict {a b k : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hab : Even (a + b)) (hpar : b % 2 = a % 2)
    {p q Pm : ℝ} (hreg : Challenge.Regions p q) (hPm : Pm ≤ q - 1)
    (hS : Challenge.CondS a p Pm) {Y : ℕ → ℕ → ℝ}
    (hY : Challenge.IsSignMat a b Y) {g : ℕ → ℝ}
    (hg : Challenge.IsSignVec a g) (hk : k < b) (hk4 : k ≤ 4)
    (hlast : ∀ i ≤ a, Y i b = g i) (hchain : TailChain a b k Y g)
    (hbreak : ¬ ∀ i ≤ a, Y i (b - 1 - k) = (-1) ^ (k + 1) * g i)
    (hC1 : ∀ k ≤ 4, ∀ y : ℝ, Challenge.Ik a k q y →
      ∀ c : ℕ → ℝ, Challenge.IsSignVec a c →
        ¬ (∀ i ≤ a, c i = (-1) ^ (k + 1) * g i) →
        (∑ n ∈ Finset.Icc 1 k,
          (q - 1) * (1 + Challenge.etaMap q n y) * Challenge.DeltaC a p g) +
          Challenge.psi a p q y c (fun i => (-1) ^ k * Challenge.mu q ((k : ℤ) - 1) * g i) >
        q * Challenge.etaMap q (k + 1) y * (2 * Challenge.deltaK a p - Challenge.DeltaC a p g)) :
    Challenge.Gval a b p q Y < Challenge.Theta a b p q := by
  have hq : 2 < q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  let y := Challenge.mu q ((b : ℤ) - 2 - k)
  let j := b - 1 - k
  have hj : j < b := by dsimp [j]; omega
  have hy : y = nu q (b - (k + 1)) := mu_tail_eq_nu q hk
  have hη : Challenge.etaMap q (k + 1) y = Challenge.mu q ((b : ℤ) - 1) := by
    rw [hy, eta_nu, show b - (k + 1) + (k + 1) = b by omega,
      Additional.mu_pred_eq_nu]
  have hstate := ((check_Lemma23 a b ha hb hab p q hreg Y hY).1 g hg k hk.le hlast hchain).1 k le_rfl
  have hψ : Challenge.psiCol a b p q Y j = Challenge.psi a p q y (Challenge.col Y j)
      (fun i => (-1) ^ k * Challenge.mu q ((k : ℤ) - 1) * g i) := by
    unfold Challenge.psiCol
    have he1 : (j : ℤ) - 1 = (b : ℤ) - 2 - k := by dsimp [j]; omega
    rw [he1]
    apply psi_congr a p q y (by intros; rfl)
    intro i hi
    have he2 : (b : ℤ) - 1 - k = (j : ℤ) := by dsimp [j]; omega
    rw [he2] at hstate
    exact hstate i hi
  have hsum : (∑ l ∈ Finset.Icc 1 k, Challenge.psiCol a b p q Y (b - l)) =
      ∑ n ∈ Finset.Icc 1 k,
        (q - 1) * (1 + Challenge.etaMap q n y) * Challenge.DeltaC a p g := by
    calc
      _ = ∑ l ∈ Finset.Icc 1 k,
          (q - 1) * (1 + nu q (b - l)) * Challenge.DeltaC a p g := by
        apply Finset.sum_congr rfl
        intro l hl
        exact chain_surplus_term ha hb hab hreg hY hg hk.le hlast hchain
          (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2
      _ = _ := by rw [hy]; exact tail_eta_sum q (Challenge.DeltaC a p g) hk
  have hcert := hC1 k hk4 y (Ik_actual hq hpar hk) (Challenge.col Y j)
    (fun i hi => hY i hi j hj.le) hbreak
  rw [hη, ← hψ, ← hsum] at hcert
  have hle := tail_break_sum_le_total (Challenge.psiCol a b p q Y) hk
    (fun l hl => (psiCol_nonneg ha hreg hPm hS hY hl).1)
  apply strict_of_surplus hq a b p Y
  have hdelta : Challenge.DeltaC a p (Challenge.col Y b) = Challenge.DeltaC a p g :=
    DeltaC_congr a p hlast
  rw [hdelta]
  exact hcert.trans_le hle

lemma five_eta_sum (q Δ : ℝ) {b : ℕ} (hb : 6 ≤ b) :
    (∑ l ∈ Finset.Icc 1 5, (q - 1) * (1 + nu q (b - l)) * Δ) =
      ∑ n ∈ range 5, (q - 1) * (1 + Challenge.etaMap q n (nu q (b - 5))) * Δ := by
  apply Finset.sum_bij (fun l _ => 5 - l)
  · intro l hl
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hl
    exact Finset.mem_range.mpr (by omega)
  · intro l hl m hm he
    obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    omega
  · intro n hn
    have hn5 := Finset.mem_range.mp hn
    refine ⟨5 - n, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro l hl
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hl
    rw [eta_nu, show b - 5 + (5 - l) = b - l by omega]

lemma C2_strict {a b k : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hab : Even (a + b)) (hpar : b % 2 = a % 2)
    {p q Pm : ℝ} (hreg : Challenge.Regions p q) (hPm : Pm ≤ q - 1)
    (hS : Challenge.CondS a p Pm) {Y : ℕ → ℕ → ℝ}
    (hY : Challenge.IsSignMat a b Y) {g : ℕ → ℝ}
    (hg : Challenge.IsSignVec a g) (hk : k < b) (hk5 : 5 ≤ k)
    (hlast : ∀ i ≤ a, Y i b = g i) (hchain : TailChain a b k Y g)
    (hC2 : ∀ y : ℝ,
      (if Even a then Challenge.mu q 0 ≤ y ∧ y ≤ Challenge.muInf q
        else Challenge.muInf q ≤ y ∧ y ≤ Challenge.mu q 1) →
      (∑ n ∈ range 5, (q - 1) * (1 + Challenge.etaMap q n y) * Challenge.DeltaC a p g) >
        q * Challenge.etaMap q 5 y * (2 * Challenge.deltaK a p - Challenge.DeltaC a p g)) :
    Challenge.Gval a b p q Y < Challenge.Theta a b p q := by
  have hq : 2 < q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  have hb6 : 6 ≤ b := by omega
  let y := Challenge.mu q ((b : ℤ) - 6)
  have hy : y = nu q (b - 5) := by
    dsimp [y]
    rw [show (b : ℤ) - 6 = ((b - 5 : ℕ) : ℤ) - 1 by omega, Additional.mu_pred_eq_nu]
  have hη : Challenge.etaMap q 5 y = Challenge.mu q ((b : ℤ) - 1) := by
    rw [hy, eta_nu, show b - 5 + 5 = b by omega, Additional.mu_pred_eq_nu]
  have hsum : (∑ l ∈ Finset.Icc 1 5, Challenge.psiCol a b p q Y (b - l)) =
      ∑ n ∈ range 5, (q - 1) * (1 + Challenge.etaMap q n y) * Challenge.DeltaC a p g := by
    calc
      _ = ∑ l ∈ Finset.Icc 1 5, (q - 1) * (1 + nu q (b - l)) * Challenge.DeltaC a p g := by
        apply Finset.sum_congr rfl
        intro l hl
        exact chain_surplus_term ha hb hab hreg hY hg hk.le hlast hchain
          (Finset.mem_Icc.mp hl).1 (by have := (Finset.mem_Icc.mp hl).2; omega)
      _ = _ := by rw [hy]; exact five_eta_sum q (Challenge.DeltaC a p g) hb6
  have hcert := hC2 y (C2_interval_actual hq hpar hb6)
  rw [hη, ← hsum] at hcert
  have hle := tail_sum_le_total (Challenge.psiCol a b p q Y) (show 5 ≤ b by omega)
    (fun l hl => (psiCol_nonneg ha hreg hPm hS hY hl).1)
  apply strict_of_surplus hq a b p Y
  have hdelta : Challenge.DeltaC a p (Challenge.col Y b) = Challenge.DeltaC a p g :=
    DeltaC_congr a p hlast
  rw [hdelta]
  exact hcert.trans_le hle

end Prop31
end CodexPaper1
