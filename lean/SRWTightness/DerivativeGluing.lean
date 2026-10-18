import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

open Set Filter
open scoped Topology

namespace SRWTightness

/-- Matching values and derivatives allow two scalar functions to be glued at a threshold. -/
theorem hasDerivAt_threshold_glue (f g : ℝ → ℝ) (c d : ℝ)
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (he : f c = g c) :
    HasDerivAt (fun x ↦ if x ≤ c then f x else g x) d c := by
  have hl : HasDerivWithinAt (fun x ↦ if x ≤ c then f x else g x) d (Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro x hx; simp only [mem_Iic] at hx; simp [hx]
    · simp
  have hr : HasDerivWithinAt (fun x ↦ if x ≤ c then f x else g x) d (Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro x hx
      by_cases hxc : x ≤ c
      · have hx' : x = c := le_antisymm hxc hx
        subst x
        simp [he]
      · simp [hxc]
    · simp [he]
  have hh := hl.union hr
  rw [Iic_union_Ici] at hh
  exact hasDerivWithinAt_univ.mp hh

/-- A piecewise derivative formula is valid globally when the two pieces match to first order. -/
theorem hasDerivAt_piecewise_threshold (f g f' g' : ℝ → ℝ) (c : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : f c = g c) (hd : f' c = g' c) (x : ℝ) :
    HasDerivAt (fun y ↦ if y ≤ c then f y else g y)
      (if x ≤ c then f' x else g' x) x := by
  rcases lt_trichotomy x c with h | rfl | h
  · rw [if_pos h.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds h] with y hy
    simp [hy.le]
  · rw [if_pos le_rfl]
    exact hasDerivAt_threshold_glue f g x (f' x) (hf x) (hd ▸ hg x) he
  · rw [if_neg (not_le.mpr h)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds h] with y hy
    simp [not_le.mpr hy]

end SRWTightness
