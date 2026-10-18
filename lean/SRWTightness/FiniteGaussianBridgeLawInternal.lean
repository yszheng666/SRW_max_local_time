import SRWTightness.MeasurableBrownianReconstruction
import SRWTightness.FiniteGaussianPrefixMeasurable
import SRWTightness.FiniteGaussianPathReconstruction

open MeasureTheory ProbabilityTheory

namespace SRWTightness

set_option maxHeartbeats 800000 in
/-- The actual finite retained mesh has the exact endpoint/bridge law for arbitrary strict gaps. -/
theorem finiteGaussian_endpoint_bridge_law_internal
    (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hT : T 0 = 0)
    (hgap : ∀ j < n, T j < T (j + 1)) :
    ((gaussianCoordinateLaw (brownianTimeMatrix T n)).prod (independentBridgeLaw ℕ)).map
      (fun p ↦ (finiteGaussianBridgedPath T n n p.1 p.2 (T n),
        fun v : Set.Icc (0 : ℝ) (T n) ↦ finiteGaussianBridgedPath T n n p.1 p.2 v)) =
      ((gaussianReal 0 (T n).toNNReal).prod gaussianCoefficientLaw).map
        (fun p ↦ (p.1, fun v : Set.Icc (0 : ℝ) (T n) ↦
          endpointBrownianBridge (T n) p.1 v p.2)) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure (brownianTimeMatrix T n)
  have hg := hgap
  have hpos : 0 < T n := by
    have h01 := hgap 0 (by omega)
    have h1n := timeGridTime_mono T n hgap (by omega : 1 ≤ n) le_rfl
    simp only [hT, zero_add] at h01
    linarith
  apply measurable_brownian_endpoint_bridge_law
    ((gaussianCoordinateLaw (brownianTimeMatrix T n)).prod (independentBridgeLaw ℕ))
    (fun v p ↦ finiteGaussianBridgedPath T n n p.1 p.2 v) (T n) hpos
    ((finiteGaussianBridgedPath_gaussian T n hg).comp_right Subtype.val)
  · intro v
    exact finiteGaussianBridgedPath_measurable T n n v
  · intro v
    exact finiteGaussianBridgedPath_mean T n hn hg v
      (by simpa only [hT] using v.property.1) v.property.2
  · intro s t
    exact finiteGaussianBridgedPath_covariance T n hn hT hgap s t
      s.property.1 s.property.2 t.property.1 t.property.2

end SRWTightness
