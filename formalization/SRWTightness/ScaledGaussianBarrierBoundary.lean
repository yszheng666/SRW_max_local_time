import SRWTightness.ScaledGaussianStrictFlatProbability
import SRWTightness.StrictBarrierAlmostEverywhere

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- For the actual Brownian path, strict and closed flat-barrier events agree almost surely. -/
theorem scaled_gaussian_barrier_boundary (hReflection : BridgeReflectionInput)
    (T q : ℝ) (hT : 0 < T) (hq : 0 < q) :
    ∀ᵐ ω ∂gaussianCoefficientLaw,
      (∀ t ∈ Set.Icc (0 : ℝ) T, Real.sqrt T * gaussianDyadicPath ω (t / T) < q) ↔
      ∀ t ∈ Set.Icc (0 : ℝ) T, Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ q := by
  let F : ℝ → ℝ := fun p ↦ 2 * (Real.sqrt (2 * Real.pi * T))⁻¹ *
    ∫ t in (0 : ℝ)..p, Real.exp (-(t ^ 2) / (2 * T))
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-(t ^ 2) / (2 * T))) := by fun_prop
  have hF : Continuous F := continuous_const.mul
    (intervalIntegral.continuous_primitive (fun a b ↦ hc.intervalIntegrable a b) 0)
  have hm (p : ℝ) (hp : 0 < p) : NullMeasurableSet
      {ω | ∀ t : Set.Icc (0 : ℝ) T,
        Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ p} gaussianCoefficientLaw := by
    have hmeas (t : ℝ) : Measurable
        (fun ω ↦ -(Real.sqrt T * gaussianDyadicPath ω (t / T))) :=
      (measurable_const.mul (gaussianDyadicPath_measurable _)).neg
    have hcont : ∀ᵐ ω ∂gaussianCoefficientLaw,
        Continuous (fun t ↦ -(Real.sqrt T * gaussianDyadicPath ω (t / T))) := by
      filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
      exact (continuous_const.mul (hω.comp (continuous_id.div_const T))).neg
    simpa only [Subtype.forall, neg_le_neg_iff] using
      continuousPath_survival_nullMeasurable gaussianCoefficientLaw _ hmeas hcont T
        (fun _ ↦ -p) continuous_const
  have hclosed (p : ℝ) (hp : 0 < p) :
      gaussianCoefficientLaw.real {ω | ∀ t : Set.Icc (0 : ℝ) T,
        Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ p} = F p := by
    have hh := scaled_gaussian_flat_probability hReflection T p hT hp
    rw [gaussian_symmetric_interval T p hT hp.le] at hh
    simpa only [Subtype.forall] using hh
  have he := strict_barrier_ae_closed gaussianCoefficientLaw
    (fun t : Set.Icc (0 : ℝ) T ↦ fun ω ↦
      Real.sqrt T * gaussianDyadicPath ω (t / T)) F q hq hF.continuousAt hm hclosed
  simpa only [Subtype.forall] using he

end SRWTightness
