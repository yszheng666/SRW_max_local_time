import SRWTightness.QuadraticCutoff
import SRWTightness.DerivativeGluing
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum

namespace SRWTightness

/-- The quadratic profile has the claimed derivative even at all three junctions. -/
theorem quadraticCutoff_hasDerivAt (x : ℝ) :
    HasDerivAt quadraticCutoff (quadraticCutoffSlope x) x := by
  have hp (y : ℝ) : HasDerivAt (fun z : ℝ ↦ 2 * (1 - z) ^ 2) (-4 * (1 - y)) y := by
    apply ((((hasDerivAt_id y).const_sub 1).pow 2).const_mul 2).congr_deriv
    dsimp
    ring
  have hq (y : ℝ) : HasDerivAt (fun z : ℝ ↦ 1 - 2 * z ^ 2) (-4 * y) y := by
    apply ((((hasDerivAt_id y).pow 2).const_mul 2).const_sub 1).congr_deriv
    dsimp
    ring
  have hr (y : ℝ) := hasDerivAt_piecewise_threshold
    (fun z ↦ 2 * (1 - z) ^ 2) (fun _ ↦ 0)
    (fun z ↦ -4 * (1 - z)) (fun _ ↦ 0) 1 hp (fun z ↦ hasDerivAt_const z 0)
    (by norm_num) (by norm_num) y
  have hm (y : ℝ) := hasDerivAt_piecewise_threshold
    (fun z ↦ 1 - 2 * z ^ 2) (fun z ↦ if z ≤ 1 then 2 * (1 - z) ^ 2 else 0)
    (fun z ↦ -4 * z) (fun z ↦ if z ≤ 1 then -4 * (1 - z) else 0) (1 / 2)
    hq hr (by norm_num) (by norm_num) y
  exact hasDerivAt_piecewise_threshold (fun _ ↦ 1)
    (fun z ↦ if z ≤ 1 / 2 then 1 - 2 * z ^ 2 else if z ≤ 1 then 2 * (1 - z) ^ 2 else 0)
    (fun _ ↦ 0)
    (fun z ↦ if z ≤ 1 / 2 then -4 * z else if z ≤ 1 then -4 * (1 - z) else 0) 0
    (fun z ↦ hasDerivAt_const z 1) hm (by norm_num) (by norm_num) x

/-- The actual derivative agrees with the explicit triangular slope. -/
theorem quadraticCutoff_deriv (x : ℝ) : deriv quadraticCutoff x = quadraticCutoffSlope x :=
  (quadraticCutoff_hasDerivAt x).deriv

/-- The profile derivative is globally 4-Lipschitz. -/
theorem quadraticCutoff_deriv_lipschitz : LipschitzWith 4 (deriv quadraticCutoff) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [quadraticCutoff_deriv, Real.dist_eq, NNReal.coe_ofNat] using quadraticCutoffSlope_dist x y

/-- The profile itself is globally 2-Lipschitz. -/
theorem quadraticCutoff_lipschitz : LipschitzWith 2 quadraticCutoff := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (quadraticCutoff_hasDerivAt x).differentiableAt)
  intro x
  rw [quadraticCutoff_deriv]
  change |quadraticCutoffSlope x| ≤ (2 : ℝ)
  have hh := quadraticCutoffSlope_bounds x
  exact abs_le.mpr ⟨hh.1, hh.2.trans (by norm_num)⟩

/-- Both the smoothing profile and its derivative are continuous. -/
theorem quadraticCutoff_continuous_deriv :
    Continuous quadraticCutoff ∧ Continuous (deriv quadraticCutoff) :=
  ⟨quadraticCutoff_lipschitz.continuous, quadraticCutoff_deriv_lipschitz.continuous⟩

end SRWTightness
