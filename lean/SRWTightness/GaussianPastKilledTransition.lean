import SRWTightness.GaussianFuturePastProduct
import SRWTightness.KilledFuturePathEvent
import SRWTightness.IndependentPastEventProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- On a positive-distance past event, the future survival endpoint has the killed kernel. -/
theorem gaussian_past_killed_transition (hReflection : BridgeReflectionInput)
    (r x : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (hpos : ∀ p ∈ A, p ⟨r, hr, le_rfl⟩ < x) (B : Set ℝ) (hB : MeasurableSet B) :
    gaussianCoefficientLaw.real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ gaussianDyadicPath ω u) ∈ A ∧
      x - gaussianDyadicPath ω 1 ∈ B ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (1 - r), gaussianDyadicPath ω (r + t) ≤ x} =
    ∫ ω in (fun ω (u : Set.Icc (0 : ℝ) r) ↦ gaussianDyadicPath ω u) ⁻¹' A,
      (killedBrownianDensityLaw (1 - r) (x - gaussianDyadicPath ω r)).real B
        ∂gaussianCoefficientLaw := by
  let μ := gaussianCoefficientLaw
  let P := fun ω (u : Set.Icc (0 : ℝ) r) ↦ gaussianDyadicPath ω u
  let Y := fun ω (t : Set.Icc (0 : ℝ) (1 - r)) ↦
    gaussianDyadicPath ω (r + t) - gaussianDyadicPath ω r
  let Z := fun ω (t : Set.Icc (0 : ℝ) (1 - r)) ↦
    Real.sqrt (1 - r) * gaussianDyadicPath ω (t / (1 - r))
  let ν := μ.map Z
  have hT : 0 < 1 - r := sub_pos.mpr hr1
  have hP : Measurable P := measurable_pi_lambda _ (fun _ ↦ gaussianDyadicPath_measurable _)
  have hY : Measurable Y := measurable_pi_lambda _ (fun _ ↦
    (gaussianDyadicPath_measurable _).sub (gaussianDyadicPath_measurable _))
  have hZ : Measurable Z := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hZ.aemeasurable
  let E : Set ((Set.Icc (0 : ℝ) r → ℝ) × (Set.Icc (0 : ℝ) (1 - r) → ℝ)) :=
    (fun p ↦ (x - p.1 ⟨r, hr, le_rfl⟩, p.2)) ⁻¹'
      killedFuturePathEvent (1 - r) hT.le B
  have hE : MeasurableSet E :=
    (killedFuturePathEvent_measurable (1 - r) hT.le B hB).preimage
      ((measurable_const.sub ((measurable_pi_apply _).comp measurable_fst)).prodMk measurable_snd)
  have hl : HasLaw Y ν μ := ⟨hY.aemeasurable, gaussian_future_path_law r hr hr1⟩
  have he := independent_past_event_probability μ ν P Y hP hY hl
    (gaussian_elapsed_future_indep_past r hr hr1.le) A hA E hE
  have hright : (∫ ω in P ⁻¹' A, ν.real (Prod.mk (P ω) ⁻¹' E) ∂μ) =
      ∫ ω in P ⁻¹' A, (killedBrownianDensityLaw (1 - r)
        (x - gaussianDyadicPath ω r)).real B ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (hA.preimage hP)] with ω hω
    exact killed_future_path_section hReflection (1 - r) (x - gaussianDyadicPath ω r)
      hT (sub_pos.mpr (hpos (P ω) hω)) B hB
  rw [← hright, ← he]
  apply measureReal_congr
  filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
  apply propext
  change (P ω ∈ A ∧ _ ∧ _) ↔ (P ω ∈ A ∧ _)
  apply and_congr_right
  intro hAω
  have hc := continuous_flat_iff_dyadic
    (fun t ↦ gaussianDyadicPath ω (r + t) - gaussianDyadicPath ω r)
    ((hω.comp (continuous_const.add continuous_id)).sub continuous_const)
    (1 - r) (x - gaussianDyadicPath ω r)
  have hend : x - gaussianDyadicPath ω r -
      (gaussianDyadicPath ω (r + (1 - r)) - gaussianDyadicPath ω r) =
      x - gaussianDyadicPath ω 1 := by
    rw [show r + (1 - r) = 1 by ring]
    ring
  change (_ ∧ _) ↔ (x - gaussianDyadicPath ω r -
    (gaussianDyadicPath ω (r + (1 - r)) - gaussianDyadicPath ω r) ∈ B ∧ _)
  rw [hend]
  apply and_congr_right
  intro hBω
  simpa only [sub_le_sub_iff_right, dyadicFlatPathEvent, Set.mem_setOf_eq, Y, P] using hc

end SRWTightness
