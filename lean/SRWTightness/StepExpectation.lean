import SRWTightness.Law
import SRWTightness.Geometry
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.NormNum

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Exact SRW transition drift, integrated against its actual one-step probability law. -/
theorem integral_normSq_step (x : Site) :
    ∫ d, normSq (x + step d) ∂directionLaw = normSq x + 1 := by
  rw [directionLaw, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply]
  have hc : Fintype.card Direction = 4 := rfl
  rw [hc]
  simp only [ENNReal.toReal_inv, smul_eq_mul]
  rw [← Finset.mul_sum, sum_normSq_step]
  norm_num
  <;> ring

end SRWTightness
