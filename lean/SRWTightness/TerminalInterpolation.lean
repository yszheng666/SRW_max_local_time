import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- The absent endpoint denotes the fixed zero value at initial time. -/
def interpolationEndpoint {ι : Type*} (j : Option ι) (x : ι → ℝ) : ℝ := j.elim 0 x

noncomputable def interpolationWeights {ι : Type*} (left right : Option ι) (θ : ℝ)
    (i : ι) : ℝ := by
  classical
  exact (if left = some i then 1 - θ else 0) + (if right = some i then θ else 0)

def linearObservationInterpolation {ι : Type*} (left right : Option ι) (θ : ℝ)
    (x : ι → ℝ) : ℝ :=
  (1 - θ) * interpolationEndpoint left x + θ * interpolationEndpoint right x

/-- Actual two-endpoint interpolation is a linear form in the observation coordinates. -/
theorem interpolationWeights_sum {ι : Type*} [Fintype ι]
    (left right : Option ι) (θ : ℝ) (x : ι → ℝ) :
    (∑ i, interpolationWeights left right θ i * x i) =
      linearObservationInterpolation left right θ x := by
  classical
  cases left <;> cases right <;>
    simp [interpolationWeights, linearObservationInterpolation, interpolationEndpoint,
      add_mul, Finset.sum_add_distrib]

/-- Subtracting deterministic observation means subtracts their interpolated linear form. -/
theorem centered_interpolation_identity {ι : Type*} [Fintype ι]
    (left right : Option ι) (θ : ℝ) (x mean : ι → ℝ) :
    linearObservationInterpolation left right θ (x - mean) =
      (∑ i, interpolationWeights left right θ i * x i) -
        ∑ i, interpolationWeights left right θ i * mean i := by
  rw [← interpolationWeights_sum]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

end SRWTightness
