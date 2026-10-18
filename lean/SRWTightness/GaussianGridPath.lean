import SRWTightness.BrownianObservationNodes
import SRWTightness.BridgedGridBrownianCovariance
import SRWTightness.BridgedGridMoments

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

noncomputable def gaussianGridPath (T : ℕ → ℝ) (n : ℕ)
    (p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) (v : ℝ) : ℝ :=
  bridgedGridPath T (fun j x ↦ observationMeshValue x j) n p v

theorem gaussianGridPath_gaussian (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) :
    IsGaussianProcess (fun v p ↦ gaussianGridPath T n p v)
      ((gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)) := by
  let K := brownianTimeMatrix T (n + 1)
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  exact bridgedGridPath_gaussian (gaussianCoordinateLaw K) T _ n hgap
    (observationMeshValue_gaussian n K) (fun j _ ↦ observationMeshValue_measurable n j)

theorem gaussianGridPath_covariance (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) (s t : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ T n) (ht : 0 ≤ t) (ht' : t ≤ T n) :
    cov[fun p ↦ gaussianGridPath T n p s, fun p ↦ gaussianGridPath T n p t;
      (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)] = min s t := by
  let K := brownianTimeMatrix T (n + 1)
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  exact bridgedGridPath_covariance (gaussianCoordinateLaw K) T _ n hn
    (fun j hj ↦ by linarith [hgap j (by omega)]) s t (by simpa only [hT] using hs) hs'
    (by simpa only [hT] using ht) ht'
    (fun j _ ↦ observationMeshValue_memLp n j K)
    (fun i hi j hj ↦ observationMeshValue_brownian_covariance T n hT hgap i j hi hj)

theorem gaussianGridPath_mean (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hgap : ∀ j < n, T j < T (j + 1)) (v : ℝ) (hl : T 0 ≤ v) (hu : v ≤ T n) :
    (∫ p, gaussianGridPath T n p v
      ∂(gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)) = 0 := by
  let K := brownianTimeMatrix T (n + 1)
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  exact bridgedGridPath_mean_zero (gaussianCoordinateLaw K) T _ n hn hgap v hl hu
    (fun j _ ↦ observationMeshValue_memLp n j K) (fun j _ ↦ observationMeshValue_mean n j K)

theorem gaussianGridPath_ae_continuous (T : ℕ → ℝ) (n : ℕ) :
    ∀ᵐ p ∂(gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ),
      Continuous (gaussianGridPath T n p) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure (brownianTimeMatrix T (n + 1))
  exact bridgedGridPath_ae_continuous (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1)))
    T (fun j (x : Fin (n + 1) → ℝ) ↦ observationMeshValue x j) n

end SRWTightness
