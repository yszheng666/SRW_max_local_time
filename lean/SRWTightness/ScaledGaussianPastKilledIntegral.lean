import SRWTightness.ScaledGaussianPastKilledTransition
import SRWTightness.KilledFuturePathLaw
import SRWTightness.IndependentParameterIntegral

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Surviving future endpoint integrals factor through the killed kernel on any whole-past event. -/
theorem scaled_gaussian_past_killed_integral (hReflection : BridgeReflectionInput)
    (T r t x : ℝ) (hT : 0 < T) (hr : 0 ≤ r) (hrt : r < t) (ht : t ≤ T)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (hpos : ∀ p ∈ A, p ⟨r, hr, le_rfl⟩ < x) (f : ℝ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun ω ↦ f (x - Real.sqrt T * gaussianDyadicPath ω (t / T)))
      gaussianCoefficientLaw) :
    (∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A ∧
      ∀ u ∈ Set.Icc (0 : ℝ) (t - r),
        Real.sqrt T * gaussianDyadicPath ω ((r + u) / T) ≤ x},
      f (x - Real.sqrt T * gaussianDyadicPath ω (t / T)) ∂gaussianCoefficientLaw) =
    ∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A},
      ∫ z, f z ∂killedBrownianDensityLaw (t - r)
        (x - Real.sqrt T * gaussianDyadicPath ω (r / T)) ∂gaussianCoefficientLaw := by
  classical
  let μ := gaussianCoefficientLaw
  let W := fun ω u ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  let P := fun ω (u : Set.Icc (0 : ℝ) r) ↦ W ω u
  let Y := fun ω (u : Set.Icc (0 : ℝ) (t - r)) ↦ W ω (r + u) - W ω r
  let Z := fun ω (u : Set.Icc (0 : ℝ) (t - r)) ↦
    Real.sqrt (t - r) * gaussianDyadicPath ω (u / (t - r))
  let ν := μ.map Z
  have hD : 0 < t - r := sub_pos.mpr hrt
  let e : Set.Icc (0 : ℝ) r := ⟨r, hr, le_rfl⟩
  let d : Set.Icc (0 : ℝ) (t - r) := ⟨t - r, hD.le, le_rfl⟩
  let E : Set ((Set.Icc (0 : ℝ) r → ℝ) × (Set.Icc (0 : ℝ) (t - r) → ℝ)) :=
    {p | ∀ n j : ℕ, ∀ h : (j : ℝ) / 2 ^ n ≤ t - r,
      p.2 ⟨(j : ℝ) / 2 ^ n, by positivity, h⟩ ≤ x - p.1 e}
  have hE : MeasurableSet E := by
    simp only [E, Set.setOf_forall]
    exact MeasurableSet.iInter fun n ↦ MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun h ↦ measurableSet_le
        ((measurable_pi_apply _).comp measurable_snd)
        (measurable_const.sub ((measurable_pi_apply e).comp measurable_fst))
  let F := E.indicator (fun p ↦ f (x - p.1 e - p.2 d))
  have hF : Measurable F := (hf.comp (by fun_prop)).indicator hE
  have hW (u : ℝ) : Measurable (fun ω ↦ W ω u) :=
    measurable_const.mul (gaussianDyadicPath_measurable _)
  have hP : Measurable P := measurable_pi_lambda _ (fun u ↦ hW u)
  have hY : Measurable Y := measurable_pi_lambda _ (fun u ↦ (hW _).sub (hW _))
  have hZ : Measurable Z := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hZ.aemeasurable
  let G := (fun ω ↦ (P ω, Y ω)) ⁻¹' E
  have hG : MeasurableSet G := hE.preimage (hP.prodMk hY)
  have hend (ω) : x - P ω e - Y ω d = x - W ω t := by
    dsimp [P, Y, e, d]
    rw [show r + (t - r) = t by ring]
    ring
  have hval (ω) : F (P ω, Y ω) = G.indicator (fun ω ↦ f (x - W ω t)) ω := by
    simp only [F, G, Set.indicator_apply, Set.mem_preimage, hend]
  have hiF : Integrable (fun ω ↦ F (P ω, Y ω)) μ := by
    simpa only [hval] using hi.indicator hG
  have hl : HasLaw Y ν μ := ⟨hY.aemeasurable,
    scaled_gaussian_future_path_law T r t hT hr hrt ht⟩
  have he := independent_parameter_setIntegral μ ν P Y hP hY hl
    (scaled_gaussian_elapsed_future_indep_past T r t hT hr hrt.le ht) F hF hiF A hA
  have hleft : (∫ ω in P ⁻¹' A, F (P ω, Y ω) ∂μ) =
      ∫ ω in {ω | P ω ∈ A ∧ ∀ u ∈ Set.Icc (0 : ℝ) (t - r), W ω (r + u) ≤ x},
        f (x - W ω t) ∂μ := by
    simp_rw [hval]
    rw [setIntegral_indicator hG]
    apply setIntegral_congr_set
    filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
    have hc : Continuous (W ω) := continuous_const.mul (hω.comp (continuous_id.div_const T))
    apply propext
    change (P ω ∈ A ∧ _) ↔ (P ω ∈ A ∧ _)
    apply and_congr_right
    intro hAω
    have hd := continuous_flat_iff_dyadic (fun u ↦ W ω (r + u) - W ω r)
      ((hc.comp (continuous_const.add continuous_id)).sub continuous_const)
      (t - r) (x - W ω r)
    simpa only [E, G, Set.mem_preimage, Set.mem_setOf_eq, P, Y, e,
      dyadicFlatPathEvent, sub_le_sub_iff_right] using hd.symm
  rw [← hleft, he]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (hA.preimage hP)] with ω hω
  have hsection : (fun z ↦ F (P ω, z)) =
      (dyadicFlatPathEvent (t - r) (x - P ω e)).indicator
        (fun z ↦ f (x - P ω e - z d)) := by rfl
  rw [hsection, integral_indicator (dyadicFlatPathEvent_measurable _ _)]
  exact killed_future_path_integral hReflection (t - r) (x - P ω e)
    hD (sub_pos.mpr (hpos (P ω) hω)) f hf

end SRWTightness
