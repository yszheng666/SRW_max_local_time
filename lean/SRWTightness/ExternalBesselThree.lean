import SRWTightness.ActualIntervalBridge
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Three independent Brownian coordinates, radially projected after translation by x e₁.
The Brownian time range is [0,T]; no assertion is made outside this range. -/
noncomputable def actualBesselThree (T x t : ℝ)
    (ω : Fin 3 → GaussianCoefficientSpace) : ℝ :=
  Real.sqrt (∑ i : Fin 3,
    ((if i = 0 then x else 0) + Real.sqrt T * gaussianDyadicPath (ω i) (t / T)) ^ 2)

/-- Finite-horizon lower-level hitting bound for the explicitly defined radial process. -/
def BesselThreeHittingInput : Prop :=
  ∀ T x b : ℝ, 0 < T → 0 < x → 0 < b →
    (independentBridgeLaw (Fin 3)).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, actualBesselThree T x t ω ≤ b} ≤ min 1 (b / x)

/-- The standard Markov/hitting consequence at a deterministic positive time. -/
def BesselThreeDelayedHittingInput : Prop :=
  ∀ T x b s : ℝ, 0 < T → 0 < x → 0 < b → 0 < s → s ≤ T →
    (independentBridgeLaw (Fin 3)).real
      {ω | ∃ t ∈ Set.Icc s T, actualBesselThree T x t ω ≤ b} ≤
        b * ∫ ω, (actualBesselThree T x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)

/-- A uniform inverse moment bound; the same constant works for all starting points and times. -/
def BesselThreeInverseMomentInput (C : ℝ) : Prop :=
  0 < C ∧ ∀ T x s : ℝ, 0 < T → 0 < x → 0 < s → s ≤ T →
    Integrable (fun ω ↦ (actualBesselThree T x s ω)⁻¹) (independentBridgeLaw (Fin 3)) ∧
      (∫ ω, (actualBesselThree T x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)) ≤ C / Real.sqrt s

/-- Radial Brownian increments have the dimension-three second moment bound. -/
def BesselThreeIncrementInput : Prop :=
  ∀ T x r s : ℝ, 0 < T → 0 < x → 0 ≤ r → r ≤ s → s ≤ T →
    Integrable (fun ω ↦ (actualBesselThree T x s ω - actualBesselThree T x r ω) ^ 2)
      (independentBridgeLaw (Fin 3)) ∧
    (∫ ω, (actualBesselThree T x s ω - actualBesselThree T x r ω) ^ 2
      ∂independentBridgeLaw (Fin 3)) ≤ 3 * (s - r)

/-- The delayed crossing estimate used on each dyadic interval in the manuscript. -/
theorem besselThree_delayed_crossing_bound (hHit : BesselThreeDelayedHittingInput)
    (C : ℝ) (hMoment : BesselThreeInverseMomentInput C)
    (T x b s : ℝ) (hT : 0 < T) (hx : 0 < x) (hb : 0 < b)
    (hs : 0 < s) (hsT : s ≤ T) :
    (independentBridgeLaw (Fin 3)).real
      {ω | ∃ t ∈ Set.Icc s T, actualBesselThree T x t ω ≤ b} ≤ b * (C / Real.sqrt s) := by
  exact (hHit T x b s hT hx hb hs hsT).trans
    (mul_le_mul_of_nonneg_left (hMoment.2 T x s hT hx hs hsT).2 hb.le)

end SRWTightness
