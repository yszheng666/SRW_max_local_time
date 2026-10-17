import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Proportional singleton masses against a probability law determine the total finite mass. -/
theorem countable_proportional_atom_mass {R : Type*} [MeasurableSpace R]
    [MeasurableSingletonClass R] [Countable R] (μ ν : Measure R)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ r, μ.real {r} = A * ν.real {r}) : μ.real Set.univ = A := by
  have he : μ = ENNReal.ofReal A • ν := by
    apply Measure.ext_of_singleton
    intro r
    rw [Measure.smul_apply, smul_eq_mul,
      ← ENNReal.ofReal_toReal (measure_ne_top μ {r}),
      ← ENNReal.ofReal_toReal (measure_ne_top ν {r}), ← ENNReal.ofReal_mul hA]
    exact congrArg ENNReal.ofReal (h r)
  rw [he, Measure.real, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one,
    ENNReal.toReal_ofReal hA]

end SRWTightness
