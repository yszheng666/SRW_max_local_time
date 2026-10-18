import SRWTightness.ScaledGaussianBarrierBoundary
import SRWTightness.DyadicFlatPathEvent

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Strict positive Brownian survival is null measurable under the original reflection input. -/
theorem scaled_gaussian_strict_survival_nullMeasurable (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    NullMeasurableSet {ω | ∀ t ∈ Set.Icc (0 : ℝ) T,
      0 < x - Real.sqrt T * gaussianDyadicPath ω (t / T)} gaussianCoefficientLaw := by
  let W := fun ω (t : Set.Icc (0 : ℝ) T) ↦
    Real.sqrt T * gaussianDyadicPath ω (t / T)
  have hW : Measurable W := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  have hD := (dyadicFlatPathEvent_measurable T x).preimage hW
  apply hD.nullMeasurableSet.congr
  filter_upwards [gaussianDyadicPath_ae_continuous,
    scaled_gaussian_barrier_boundary hReflection T x hT hx] with ω hc hb
  have hd := continuous_flat_iff_dyadic
    (fun t ↦ Real.sqrt T * gaussianDyadicPath ω (t / T))
    (continuous_const.mul (hc.comp (continuous_id.div_const T))) T x
  apply propext
  change W ω ∈ dyadicFlatPathEvent T x ↔
    ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < x - Real.sqrt T * gaussianDyadicPath ω (t / T)
  simpa only [sub_pos] using hd.symm.trans hb.symm

end SRWTightness
