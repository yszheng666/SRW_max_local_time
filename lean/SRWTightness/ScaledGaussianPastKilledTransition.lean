import SRWTightness.ScaledGaussianFutureLaw
import SRWTightness.KilledFuturePathEvent
import SRWTightness.IndependentPastEventProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- On any earlier scaled Brownian path event, surviving later endpoints have the killed kernel. -/
theorem scaled_gaussian_past_killed_transition (hReflection : BridgeReflectionInput)
    (T r t x : ℝ) (hT : 0 < T) (hr : 0 ≤ r) (hrt : r < t) (ht : t ≤ T)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (hpos : ∀ p ∈ A, p ⟨r, hr, le_rfl⟩ < x) (B : Set ℝ) (hB : MeasurableSet B) :
    gaussianCoefficientLaw.real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A ∧
      x - Real.sqrt T * gaussianDyadicPath ω (t / T) ∈ B ∧
      ∀ u ∈ Set.Icc (0 : ℝ) (t - r),
        Real.sqrt T * gaussianDyadicPath ω ((r + u) / T) ≤ x} =
    ∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A},
      (killedBrownianDensityLaw (t - r)
        (x - Real.sqrt T * gaussianDyadicPath ω (r / T))).real B ∂gaussianCoefficientLaw := by
  let μ := gaussianCoefficientLaw
  let W := fun ω u ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  let P := fun ω (u : Set.Icc (0 : ℝ) r) ↦ W ω u
  let Y := fun ω (u : Set.Icc (0 : ℝ) (t - r)) ↦ W ω (r + u) - W ω r
  let Z := fun ω (u : Set.Icc (0 : ℝ) (t - r)) ↦
    Real.sqrt (t - r) * gaussianDyadicPath ω (u / (t - r))
  let ν := μ.map Z
  have hD : 0 < t - r := sub_pos.mpr hrt
  have hW (u : ℝ) : Measurable (fun ω ↦ W ω u) :=
    measurable_const.mul (gaussianDyadicPath_measurable _)
  have hP : Measurable P := measurable_pi_lambda _ (fun u ↦ hW u)
  have hY : Measurable Y := measurable_pi_lambda _ (fun u ↦ (hW _).sub (hW _))
  have hZ : Measurable Z := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hZ.aemeasurable
  let E : Set ((Set.Icc (0 : ℝ) r → ℝ) × (Set.Icc (0 : ℝ) (t - r) → ℝ)) :=
    (fun p ↦ (x - p.1 ⟨r, hr, le_rfl⟩, p.2)) ⁻¹' killedFuturePathEvent (t - r) hD.le B
  have hE : MeasurableSet E :=
    (killedFuturePathEvent_measurable (t - r) hD.le B hB).preimage
      ((measurable_const.sub ((measurable_pi_apply _).comp measurable_fst)).prodMk measurable_snd)
  have hl : HasLaw Y ν μ := ⟨hY.aemeasurable,
    scaled_gaussian_future_path_law T r t hT hr hrt ht⟩
  have he := independent_past_event_probability μ ν P Y hP hY hl
    (scaled_gaussian_elapsed_future_indep_past T r t hT hr hrt.le ht) A hA E hE
  have hright : (∫ ω in P ⁻¹' A, ν.real (Prod.mk (P ω) ⁻¹' E) ∂μ) =
      ∫ ω in P ⁻¹' A, (killedBrownianDensityLaw (t - r) (x - W ω r)).real B ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (hA.preimage hP)] with ω hω
    exact killed_future_path_section hReflection (t - r) (x - W ω r)
      hD (sub_pos.mpr (hpos (P ω) hω)) B hB
  change μ.real _ = ∫ ω in P ⁻¹' A, (killedBrownianDensityLaw (t - r) (x - W ω r)).real B ∂μ
  rw [← hright, ← he]
  apply measureReal_congr
  filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
  have hcont : Continuous (W ω) := continuous_const.mul (hω.comp (continuous_id.div_const T))
  apply propext
  change (P ω ∈ A ∧ _ ∧ _) ↔ (P ω ∈ A ∧ _)
  apply and_congr_right
  intro hAω
  have hc := continuous_flat_iff_dyadic (fun u ↦ W ω (r + u) - W ω r)
    ((hcont.comp (continuous_const.add continuous_id)).sub continuous_const)
    (t - r) (x - W ω r)
  have hend : x - W ω r - (W ω (r + (t - r)) - W ω r) = x - W ω t := by
    rw [show r + (t - r) = t by ring]
    ring
  change (_ ∧ _) ↔ (x - W ω r - (W ω (r + (t - r)) - W ω r) ∈ B ∧ _)
  rw [hend]
  apply and_congr_right
  intro hBω
  simpa only [sub_le_sub_iff_right, dyadicFlatPathEvent, Set.mem_setOf_eq, Y, P, W] using hc

end SRWTightness
