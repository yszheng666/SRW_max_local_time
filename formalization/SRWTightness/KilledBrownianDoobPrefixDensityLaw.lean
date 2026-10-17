import SRWTightness.KilledBrownianDoobPrefixWeight
import SRWTightness.DensityMapPullback

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SRWTightness

/-- The Doob prefix law has its current-distance density on surviving Brownian paths. -/
theorem killed_brownian_doob_prefix_density_law (hReflection : BridgeReflectionInput)
    (T x r : ℝ) (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrT : r < T) :
    (killedBrownianDoobCoefficientLaw T x).map
      (fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) =
    ((gaussianCoefficientLaw.map
      (fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T))).restrict
        {p | p ∈ dyadicFlatPathEvent r x ∧ p ⟨r, hr.le, le_rfl⟩ < x}).withDensity
          (fun p ↦ ENNReal.ofReal ((x - p ⟨r, hr.le, le_rfl⟩) / x)) := by
  let P := fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  let e : Set.Icc (0 : ℝ) r := ⟨r, hr.le, le_rfl⟩
  let A : Set (Set.Icc (0 : ℝ) r → ℝ) :=
    {p | p ∈ dyadicFlatPathEvent r x ∧ p e < x}
  let w := fun p : Set.Icc (0 : ℝ) r → ℝ ↦ (x - p e) / x
  let Γ := (gaussianCoefficientLaw.restrict (P ⁻¹' A)).withDensity
    (fun ω ↦ ENNReal.ofReal (w (P ω)))
  have hP : Measurable P := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  have hA : MeasurableSet A := (dyadicFlatPathEvent_measurable r x).inter
    (measurableSet_lt (measurable_pi_apply e) measurable_const)
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hwP : Measurable (fun ω ↦ w (P ω)) := hw.comp hP
  have hn (ω) (hω : ω ∈ P ⁻¹' A) : 0 ≤ w (P ω) :=
    div_nonneg (sub_pos.mpr hω.2).le hx.le
  have hg := ((scaled_gaussian_path_process T hT).hasGaussianLaw_eval
    ⟨r, hr.le, hrT.le⟩).integrable
  have hi : Integrable (fun ω ↦ w (P ω)) gaussianCoefficientLaw :=
    ((integrable_const x).sub hg).div_const x
  letI : IsFiniteMeasure Γ := by
    constructor
    change ((gaussianCoefficientLaw.restrict (P ⁻¹' A)).withDensity
      (fun ω ↦ ENNReal.ofReal (w (P ω)))) Set.univ < ∞
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    have hnon : ∀ᵐ ω ∂gaussianCoefficientLaw.restrict (P ⁻¹' A), 0 ≤ w (P ω) := by
      filter_upwards [ae_restrict_mem (hA.preimage hP)] with ω hω
      exact hn ω hω
    rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn hnon]
    exact ENNReal.ofReal_lt_top
  letI := killed_brownian_doob_probability hReflection T x hT hx
  have he : (killedBrownianDoobCoefficientLaw T x).map P = Γ.map P := by
    apply Measure.ext
    intro B hB
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change ((killedBrownianDoobCoefficientLaw T x).map P).real B = (Γ.map P).real B
    rw [map_measureReal_apply hP hB, map_measureReal_apply hP hB]
    have hΓ : Γ.real (P ⁻¹' B) =
        ∫ ω in {ω | P ω ∈ B ∧ P ω ∈ dyadicFlatPathEvent r x ∧ P ω e < x},
          w (P ω) ∂gaussianCoefficientLaw := by
      change ((gaussianCoefficientLaw.restrict (P ⁻¹' A)).withDensity
        (fun ω ↦ ENNReal.ofReal (w (P ω)))).real (P ⁻¹' B) = _
      rw [restricted_density_event_real gaussianCoefficientLaw (P ⁻¹' A)
        (hA.preimage hP).nullMeasurableSet _ hwP hn (P ⁻¹' B) (hB.preimage hP)]
      apply setIntegral_congr_set
      exact ae_of_all _ (fun ω ↦ by
        apply propext
        change ((P ω ∈ dyadicFlatPathEvent r x ∧ P ω e < x) ∧ P ω ∈ B) ↔
          (P ω ∈ B ∧ P ω ∈ dyadicFlatPathEvent r x ∧ P ω e < x)
        tauto)
    rw [hΓ]
    exact killed_brownian_doob_prefix_weight hReflection T x r hT hx hr hrT B hB
  change (killedBrownianDoobCoefficientLaw T x).map P =
    ((gaussianCoefficientLaw.map P).restrict A).withDensity (fun p ↦ ENNReal.ofReal (w p))
  rw [he]
  change ((gaussianCoefficientLaw.restrict (P ⁻¹' A)).withDensity
    (fun ω ↦ ENNReal.ofReal (w (P ω)))).map P = _
  rw [density_map_pullback _ P hP _ hw.ennreal_ofReal, ← Measure.restrict_map hP hA]

end SRWTightness
