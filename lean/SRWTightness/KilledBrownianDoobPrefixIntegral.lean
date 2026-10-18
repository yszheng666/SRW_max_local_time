import SRWTightness.KilledBrownianDoobPrefixDensityLaw
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Every measurable Doob-prefix functional is a current-distance weighted Brownian integral. -/
theorem killed_brownian_doob_prefix_integral (hReflection : BridgeReflectionInput)
    (T x r : ℝ) (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrT : r < T)
    (f : (Set.Icc (0 : ℝ) r → ℝ) → ℝ) (hf : Measurable f) :
    (∫ ω, f (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T))
      ∂killedBrownianDoobCoefficientLaw T x) =
    ∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈
        dyadicFlatPathEvent r x ∧ Real.sqrt T * gaussianDyadicPath ω (r / T) < x},
      ((x - Real.sqrt T * gaussianDyadicPath ω (r / T)) / x) *
        f (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T))
          ∂gaussianCoefficientLaw := by
  let P := fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  let e : Set.Icc (0 : ℝ) r := ⟨r, hr.le, le_rfl⟩
  let A : Set (Set.Icc (0 : ℝ) r → ℝ) :=
    {p | p ∈ dyadicFlatPathEvent r x ∧ p e < x}
  let w := fun p : Set.Icc (0 : ℝ) r → ℝ ↦ (x - p e) / x
  have hP : Measurable P := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  have hA : MeasurableSet A := (dyadicFlatPathEvent_measurable r x).inter
    (measurableSet_lt (measurable_pi_apply e) measurable_const)
  have hw : Measurable w := by dsimp [w]; fun_prop
  change (∫ ω, f (P ω) ∂killedBrownianDoobCoefficientLaw T x) =
    ∫ ω in P ⁻¹' A, w (P ω) * f (P ω) ∂gaussianCoefficientLaw
  rw [← integral_map hP.aemeasurable hf.aestronglyMeasurable]
  rw [killed_brownian_doob_prefix_density_law hReflection T x r hT hx hr hrT]
  rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ p in A, w p * f p ∂gaussianCoefficientLaw.map P := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hA] with p hp
      rw [ENNReal.toReal_ofReal (div_nonneg (sub_pos.mpr hp.2).le hx.le), smul_eq_mul]
    _ = _ := setIntegral_map hA (hw.mul hf).aestronglyMeasurable hP.aemeasurable

end SRWTightness
