import SRWTightness.GaussianBridgeMiddleDensity
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The bridge middle law is a Brownian endpoint law weighted by the remaining heat kernel. -/
theorem gaussian_bridge_middle_density_law (T r b : ℝ) (hr : 0 < r) (hrT : r < T) :
    gaussianReal (r / T * b) (r * (T - r) / T).toNNReal =
      (gaussianReal 0 r.toNNReal).withDensity
        (fun z ↦ ENNReal.ofReal (gaussianPDFReal z (T - r).toNNReal b /
          gaussianPDFReal 0 T.toNNReal b)) := by
  have hT : 0 < T := hr.trans hrT
  have hv : 0 < r * (T - r) / T := by positivity
  have hm : Measurable (fun z ↦ ENNReal.ofReal (gaussianPDFReal z (T - r).toNNReal b /
      gaussianPDFReal 0 T.toNNReal b)) := by fun_prop
  rw [gaussianReal_of_var_ne_zero _ (ne_of_gt (Real.toNNReal_pos.mpr hv)),
    gaussianReal_of_var_ne_zero _ (ne_of_gt (Real.toNNReal_pos.mpr hr)),
    ← withDensity_mul _ (measurable_gaussianPDF _ _) hm]
  apply withDensity_congr_ae
  filter_upwards [] with z
  rw [gaussianPDF, gaussian_bridge_middle_density T r b z hr hrT]
  change ENNReal.ofReal (_ * _ / _) = ENNReal.ofReal _ * ENNReal.ofReal _
  rw [mul_div_assoc, ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]

end SRWTightness
