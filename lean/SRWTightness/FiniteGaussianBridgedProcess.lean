import SRWTightness.FiniteGaussianMeshCovariance
import SRWTightness.BridgedGridBrownianCovariance
import SRWTightness.BridgedGridMoments

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

theorem finiteGaussianBridgedPath_gaussian (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) :
    IsGaussianProcess (fun v p ↦ finiteGaussianBridgedPath T n n p.1 p.2 v)
      ((gaussianCoordinateLaw (brownianTimeMatrix T n)).prod (independentBridgeLaw ℕ)) := by
  let K := brownianTimeMatrix T n
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  exact bridgedGridPath_gaussian (gaussianCoordinateLaw K) T _ n hgap
    (finiteGaussianMesh_gaussian n n K) (fun j _ ↦ finiteGaussianMesh_measurable n j)

theorem finiteGaussianBridgedPath_covariance (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hT : T 0 = 0)
    (hgap : ∀ j < n, T j < T (j + 1)) (s t : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ T n) (ht : 0 ≤ t) (ht' : t ≤ T n) :
    cov[fun p ↦ finiteGaussianBridgedPath T n n p.1 p.2 s,
      fun p ↦ finiteGaussianBridgedPath T n n p.1 p.2 t;
      (gaussianCoordinateLaw (brownianTimeMatrix T n)).prod (independentBridgeLaw ℕ)] =
        min s t := by
  let K := brownianTimeMatrix T n
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  exact bridgedGridPath_covariance (gaussianCoordinateLaw K) T _ n hn
    hgap s t (by simpa only [hT] using hs) hs'
    (by simpa only [hT] using ht) ht'
    (fun j _ ↦ finiteGaussianMesh_memLp n j K)
    (fun i hi j hj ↦ finiteGaussianMesh_brownian_covariance T n hT hgap i j hi hj)

theorem finiteGaussianBridgedPath_mean (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hgap : ∀ j < n, T j < T (j + 1)) (v : ℝ) (hl : T 0 ≤ v) (hu : v ≤ T n) :
    (∫ p, finiteGaussianBridgedPath T n n p.1 p.2 v
      ∂(gaussianCoordinateLaw (brownianTimeMatrix T n)).prod (independentBridgeLaw ℕ)) = 0 := by
  let K := brownianTimeMatrix T n
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  exact bridgedGridPath_mean_zero (gaussianCoordinateLaw K) T _ n hn hgap v hl hu
    (fun j _ ↦ finiteGaussianMesh_memLp n j K) (fun j _ ↦ finiteGaussianMesh_mean n j K)

theorem finiteGaussianBridgedPath_ae_continuous (T : ℕ → ℝ) (n : ℕ) :
    ∀ᵐ p ∂(gaussianCoordinateLaw (brownianTimeMatrix T n)).prod (independentBridgeLaw ℕ),
      Continuous (finiteGaussianBridgedPath T n n p.1 p.2) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure (brownianTimeMatrix T n)
  exact bridgedGridPath_ae_continuous (gaussianCoordinateLaw (brownianTimeMatrix T n))
    T (fun j (x : Fin n → ℝ) ↦ finiteGaussianMesh n x j) n

end SRWTightness
