import SRWTightness.MeasurableBrownianReconstruction
import SRWTightness.GaussianGridPath

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual interpolated observation grid has its exact endpoint/bridge joint law. -/
theorem gaussianGrid_endpoint_bridge_law_internal
    (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) :
    ((gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)).map
      (fun p ↦ (gaussianGridPath T n p (T n),
        fun v : Set.Icc (0 : ℝ) (T n) ↦ gaussianGridPath T n p v)) =
      ((gaussianReal 0 (T n).toNNReal).prod gaussianCoefficientLaw).map
        (fun p ↦ (p.1, fun v : Set.Icc (0 : ℝ) (T n) ↦
          endpointBrownianBridge (T n) p.1 v p.2)) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure (brownianTimeMatrix T (n + 1))
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  have hpos : 0 < T n := by
    have h01 := hgap 0 (by omega)
    have h1n := timeGridTime_mono T (n + 1)
      (fun j hj ↦ by linarith [hgap j hj]) (by omega : 1 ≤ n) (by omega)
    simp only [hT, zero_add] at h01
    linarith
  apply measurable_brownian_endpoint_bridge_law _
    (fun v p ↦ gaussianGridPath T n p v) (T n) hpos
    ((gaussianGridPath_gaussian T n hg).comp_right Subtype.val)
  · intro v
    exact ((timeGridInterpolation_measurable_nodes T
      (fun j x ↦ observationMeshValue x j) n
      (fun j _ ↦ observationMeshValue_measurable n j) v).comp measurable_fst).add
      ((timeGridBridge_measurable T n v).comp measurable_snd)
  · intro v
    exact gaussianGridPath_mean T n hn hg v
      (by simpa only [hT] using v.property.1) v.property.2
  · intro s t
    exact gaussianGridPath_covariance T n hn hT hgap s t
      s.property.1 s.property.2 t.property.1 t.property.2

end SRWTightness
