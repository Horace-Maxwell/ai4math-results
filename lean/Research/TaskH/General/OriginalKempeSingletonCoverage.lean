import Research.TaskH.Seven.SevenTwoColorSwapFibers
import Research.TaskH.General.SingletonFiberBoundaryOriginal

/-! An actual Kempe exchange in the ENTIRE deleted graph. Original first-step
coverage is applied to this genuinely proper recoloring. Only the OLD row
fibers and one old cross-edge exclusion are used; a new pure split is not
assumed. These are local transport lemmas, not a strengthened Main statement. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open scoped Classical
open SimpleGraph _root_.TaskH.Challenge
variable {k : ℕ} {V : Type u} {G : SimpleGraph V}

theorem originalKempe_fixed_color_iff {W : Type*} {K : SimpleGraph W}
    (c : K.Coloring (Fin k)) (α γ δ : Fin k) (a z : W)
    (hδα : δ ≠ α) (hδγ : δ ≠ γ) :
    _root_.TaskH.Seven.twoColorSwap c α γ a z = δ ↔ c z = δ := by
  rw [_root_.TaskH.Seven.twoColorSwap_apply]
  split_ifs
  · rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hδα hδγ]
  · rfl

theorem equality_original_unlocked_row_meets_same_side [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (a b P Q T U : {z : V // z ≠ v})
    (hvb : G.Adj v b.val) (hvP : G.Adj v P.val)
    (haP : G.Adj a.val P.val)
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c a → z = a.val)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z → c ⟨z, hzv⟩ = c b → z = b.val)
    (hab : c a ≠ c b) (hPb : c P ≠ c b)
    (hTa : c T ≠ c a) (hTb : c T ≠ c b) (hTP : c T ≠ c P)
    (hpairP : ∀ z : {z : V // z ≠ v}, G.Adj v z.val →
      (c z = c P ↔ z = P ∨ z = Q))
    (hpairT : ∀ z : {z : V // z ≠ v}, G.Adj v z.val →
      (c z = c T ↔ z = T ∨ z = U))
    (hcross : ¬G.Adj P.val U.val)
    (hout : Q ∉ _root_.TaskH.Seven.twoColorComponent c (c a) (c P) a) :
    G.Adj P.val T.val := by
  classical
  let N : Set {z : V // z ≠ v} := {z | G.Adj v z.val}
  have hsingle : ∀ z ∈ N, c z = c a ↔ z = a := by
    intro z hz
    constructor
    · intro hc
      exact Subtype.ext (haunique z.val z.property hz hc)
    · intro he
      exact congrArg c he
  have hswap := _root_.TaskH.Seven.twoColorSwap_singleton_pair_fibers c (c a) (c P)
    a P Q N rfl rfl haP hsingle hpairP hout
  let d := _root_.TaskH.Seven.twoColorSwap c (c a) (c P) a
  have hPnew : d P = c a := (hswap.1 P hvP).mpr rfl
  have hbnew : d b = c b :=
    _root_.TaskH.Seven.twoColorSwap_other_color c (c a) (c P) a b hab.symm hPb.symm
  have hPunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      d ⟨z, hzv⟩ = d P → z = P.val := by
    intro z hzv hvz hc
    have he := (hswap.1 ⟨z, hzv⟩ hvz).mp (hc.trans hPnew)
    exact congrArg Subtype.val he
  have hbunique' : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      d ⟨z, hzv⟩ = d b → z = b.val := by
    intro z hzv hvz hc
    have he : c ⟨z, hzv⟩ = c b :=
      (originalKempe_fixed_color_iff c (c a) (c P) (c b) a ⟨z, hzv⟩ hab.symm hPb.symm).mp
        (hc.trans hbnew)
    exact hbunique z hzv hvz he
  have hnewcolors : d b ≠ d P := by rw [hbnew, hPnew]; exact hab.symm
  obtain ⟨z, hzv, hvz, hzc, hzP⟩ := equality_original_singleton_color_fiber_touches
    hk hcrit hcount hvb hvP d hbunique' hPunique hnewcolors (c T)
    (by change c T ≠ d b; rw [hbnew]; exact hTb)
    (by change c T ≠ d P; rw [hPnew]; exact hTa)
  have hzold : c ⟨z, hzv⟩ = c T :=
    (originalKempe_fixed_color_iff c (c a) (c P) (c T) a ⟨z, hzv⟩ hTa hTP).mp hzc
  rcases (hpairT ⟨z, hzv⟩ hvz).mp hzold with he | he
  · have hzT : z = T.val := congrArg Subtype.val he
    simpa only [hzT] using hzP.symm
  · have hzU : z = U.val := congrArg Subtype.val he
    exact False.elim (hcross (by simpa only [hzU] using hzP.symm))

end TaskH.General
#print axioms TaskH.General.originalKempe_fixed_color_iff
#print axioms TaskH.General.equality_original_unlocked_row_meets_same_side
