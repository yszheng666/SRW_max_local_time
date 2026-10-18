import SRWTightness.IndependentSymmetricReflection
import SRWTightness.ScaledGaussianFutureIndependence
import SRWTightness.BesselIncrementLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

set_option maxHeartbeats 800000 in
/-- Reflecting the terminal Brownian increment preserves its joint law with the entire past. -/
theorem scaled_gaussian_deterministic_reflection (T r t : ℝ) (hT : 0 < T)
    (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T) :
    gaussianCoefficientLaw.map (fun ω ↦
      ((fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)),
        Real.sqrt T * gaussianDyadicPath ω (t / T))) =
    gaussianCoefficientLaw.map (fun ω ↦
      ((fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)),
        2 * (Real.sqrt T * gaussianDyadicPath ω (r / T)) -
          Real.sqrt T * gaussianDyadicPath ω (t / T))) := by
  let X : GaussianCoefficientSpace → Set.Icc (0 : ℝ) r → ℝ :=
    fun ω u ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  let Z : GaussianCoefficientSpace → ℝ := fun ω ↦
    Real.sqrt T * gaussianDyadicPath ω (t / T) -
      Real.sqrt T * gaussianDyadicPath ω (r / T)
  let g : (Set.Icc (0 : ℝ) r → ℝ) → ℝ := fun p ↦ p ⟨r, hr, le_rfl⟩
  have hX : Measurable X := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  have hZ : Measurable Z := (measurable_const.mul (gaussianDyadicPath_measurable _)).sub
    (measurable_const.mul (gaussianDyadicPath_measurable _))
  have hg : Measurable g := measurable_pi_apply _
  have hev : Measurable (fun p : Set.Icc r t → ℝ ↦ p ⟨t, hrt, le_rfl⟩) :=
    measurable_pi_apply _
  have hind : IndepFun X Z gaussianCoefficientLaw := by
    simpa only [Function.comp_def, id_eq, X, Z] using
      (scaled_gaussian_future_indep_past T r t hT hr hrt ht).comp measurable_id hev
  have hl : HasLaw Z (gaussianReal 0 (t - r).toNNReal) gaussianCoefficientLaw := by
    simpa only [Z, mul_sub] using bessel_scaled_increment_law T r t hT hr hrt ht
  have hn : HasLaw (fun ω ↦ -Z ω) (gaussianReal 0 (t - r).toNNReal)
      gaussianCoefficientLaw := by
    simpa only [neg_zero, Pi.neg_def] using gaussianReal_neg hl
  have hs : gaussianCoefficientLaw.map Z = gaussianCoefficientLaw.map (fun ω ↦ -Z ω) :=
    hl.map_eq.trans hn.map_eq.symm
  have he := independent_symmetric_reflection gaussianCoefficientLaw X Z g hX hZ hg hind hs
  have hplus (ω : GaussianCoefficientSpace) :
      g (X ω) + Z ω = Real.sqrt T * gaussianDyadicPath ω (t / T) := by
    dsimp [g, X, Z]
    ring
  have hminus (ω : GaussianCoefficientSpace) : g (X ω) - Z ω =
      2 * (Real.sqrt T * gaussianDyadicPath ω (r / T)) -
        Real.sqrt T * gaussianDyadicPath ω (t / T) := by
    dsimp [g, X, Z]
    ring
  simpa only [hplus, hminus, X] using he

end SRWTightness
