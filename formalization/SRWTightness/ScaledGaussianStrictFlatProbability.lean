import SRWTightness.ScaledGaussianFlatProbability
import SRWTightness.StrictBarrierDistribution
import SRWTightness.GaussianSymmetricInterval
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual Brownian strict flat-barrier probability equals its closed-barrier probability. -/
theorem scaled_gaussian_strict_flat_probability (hReflection : BridgeReflectionInput)
    (T q : ℝ) (hT : 0 < T) (hq : 0 < q) :
    gaussianCoefficientLaw.real
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T,
        Real.sqrt T * gaussianDyadicPath ω (t / T) < q} =
      (gaussianReal 0 T.toNNReal).real (Set.Icc (-q) q) := by
  let F : ℝ → ℝ := fun p ↦ 2 * (Real.sqrt (2 * Real.pi * T))⁻¹ *
    ∫ t in (0 : ℝ)..p, Real.exp (-(t ^ 2) / (2 * T))
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-(t ^ 2) / (2 * T))) := by fun_prop
  have hF : Continuous F := continuous_const.mul
    (intervalIntegral.continuous_primitive (fun a b ↦ hc.intervalIntegrable a b) 0)
  have hclosed (p : ℝ) (hp : 0 < p) :
      gaussianCoefficientLaw.real {ω | ∀ t : Set.Icc (0 : ℝ) T,
        Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ p} = F p := by
    have hh := scaled_gaussian_flat_probability hReflection T p hT hp
    rw [gaussian_symmetric_interval T p hT hp.le] at hh
    simpa only [Subtype.forall] using hh
  have he := strict_barrier_of_continuous_distribution gaussianCoefficientLaw
    (fun t : Set.Icc (0 : ℝ) T ↦ fun ω ↦
      Real.sqrt T * gaussianDyadicPath ω (t / T)) F q hq hF.continuousAt hclosed
  rw [gaussian_symmetric_interval T q hT hq.le]
  simpa only [Subtype.forall] using he

end SRWTightness
