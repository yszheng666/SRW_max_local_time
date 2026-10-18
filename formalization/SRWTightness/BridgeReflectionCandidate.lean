import SRWTightness.BridgeReflectionIntegrated
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Every nonempty finite interval has positive mass under the nondegenerate
endpoint Gaussian law. -/
theorem gaussian_endpoint_interval_pos (T a b : ℝ) (hT : 0 < T) (hab : a < b) :
    0 < gaussianReal 0 T.toNNReal (Set.Ioc a b) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hv := gaussianReal_absolutelyContinuous' 0 (ne_of_gt (Real.toNNReal_pos.mpr hT)) hz
  have hp : 0 < volume (Set.Ioc a b) := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact (ne_of_gt hp) hv

/-- The explicit reflection factor is integrable below any endpoint strictly below the barrier. -/
theorem bridge_reflection_candidate_integrable (T q b : ℝ) (hT : 0 < T)
    (hq : 0 < q) (hb : b < q) :
    IntegrableOn (fun a ↦ 1 - Real.exp (-(2 * q * (q - a) / T)))
      (Set.Iic b) (gaussianReal 0 T.toNNReal) := by
  have hc : Continuous (fun a : ℝ ↦ 1 - Real.exp (-(2 * q * (q - a) / T))) := by fun_prop
  apply (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Iic] with a ha
  have hqa : 0 < q - a := by linarith [show a ≤ b from ha]
  have hp : 0 ≤ 2 * q * (q - a) / T := by positivity
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤
    1 - Real.exp (-(2 * q * (q - a) / T)))]
  linarith [Real.exp_pos (-(2 * q * (q - a) / T))]

end SRWTightness
