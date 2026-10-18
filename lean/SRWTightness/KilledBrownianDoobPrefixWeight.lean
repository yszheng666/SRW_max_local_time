import SRWTightness.KilledBrownianDoobEventReal
import SRWTightness.ScaledGaussianKilledFirstMomentPast

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A Doob prefix event is weighted by its current distance, independent of the terminal horizon. -/
theorem killed_brownian_doob_prefix_weight (hReflection : BridgeReflectionInput)
    (T x r : ℝ) (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrT : r < T)
    (B : Set (Set.Icc (0 : ℝ) r → ℝ)) (hB : MeasurableSet B) :
    (killedBrownianDoobCoefficientLaw T x).real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ B} =
    ∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ B ∧
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈
        dyadicFlatPathEvent r x ∧ Real.sqrt T * gaussianDyadicPath ω (r / T) < x},
      (x - Real.sqrt T * gaussianDyadicPath ω (r / T)) / x ∂gaussianCoefficientLaw := by
  let W := fun ω u ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  let P := fun ω (u : Set.Icc (0 : ℝ) r) ↦ W ω u
  let A : Set (Set.Icc (0 : ℝ) r → ℝ) :=
    {p | p ∈ B ∧ p ∈ dyadicFlatPathEvent r x ∧ p ⟨r, hr.le, le_rfl⟩ < x}
  have hA : MeasurableSet A := hB.inter ((dyadicFlatPathEvent_measurable r x).inter
    (measurableSet_lt (measurable_pi_apply _) measurable_const))
  have hP : Measurable P := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  have hset : {ω | (∀ u ∈ Set.Icc (0 : ℝ) T, 0 < x - W ω u) ∧ P ω ∈ B} =ᵐ[
      gaussianCoefficientLaw]
      {ω | P ω ∈ A ∧ ∀ u ∈ Set.Icc (0 : ℝ) (T - r), W ω (r + u) ≤ x} := by
    filter_upwards [gaussianDyadicPath_ae_continuous,
      scaled_gaussian_barrier_boundary hReflection T x hT hx] with ω hω hboundary
    have hc : Continuous (W ω) := continuous_const.mul (hω.comp (continuous_id.div_const T))
    have hd := continuous_flat_iff_dyadic (W ω) hc r x
    apply propext
    change ((∀ u ∈ Set.Icc (0 : ℝ) T, 0 < x - W ω u) ∧ P ω ∈ B) ↔
      (P ω ∈ A ∧ ∀ u ∈ Set.Icc (0 : ℝ) (T - r), W ω (r + u) ≤ x)
    constructor
    · rintro ⟨hs, hBω⟩
      have hflat (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) T) : W ω u ≤ x :=
        (sub_pos.mp (hs u hu)).le
      refine ⟨⟨hBω, hd.mp (fun u hu ↦ hflat u ⟨hu.1, hu.2.trans hrT.le⟩),
        sub_pos.mp (hs r ⟨hr.le, hrT.le⟩)⟩, ?_⟩
      intro u hu
      exact hflat (r + u) ⟨add_nonneg hr.le hu.1, by linarith [hu.2]⟩
    · rintro ⟨hAω, hfuture⟩
      have hpast := hd.mpr hAω.2.1
      have hfull : ∀ u ∈ Set.Icc (0 : ℝ) T, W ω u ≤ x := by
        intro u hu
        by_cases hur : u ≤ r
        · exact hpast u ⟨hu.1, hur⟩
        · have hv : u - r ∈ Set.Icc (0 : ℝ) (T - r) :=
            ⟨by linarith, by linarith [hu.2]⟩
          have hh := hfuture (u - r) hv
          rwa [show r + (u - r) = u by ring] at hh
      refine ⟨?_, hAω.1⟩
      intro u hu
      exact sub_pos.mpr (hboundary.mpr hfull u hu)
  have hmoment := scaled_gaussian_killed_first_moment_past hReflection T r T x hT hr.le
    hrT le_rfl A hA (fun p hp ↦ hp.2.2)
  have hPB : MeasurableSet {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ B} :=
    hB.preimage hP
  have hmoment' :
      (∫ ω in {ω | P ω ∈ A ∧ ∀ u ∈ Set.Icc (0 : ℝ) (T - r), W ω (r + u) ≤ x},
        x - W ω T ∂gaussianCoefficientLaw) =
      ∫ ω in P ⁻¹' A, x - W ω r ∂gaussianCoefficientLaw := hmoment
  rw [killed_brownian_doob_event_real hReflection T x hT hx _ hPB]
  change (∫ ω in {ω | (∀ u ∈ Set.Icc (0 : ℝ) T, 0 < x - W ω u) ∧ P ω ∈ B},
    (x - W ω T) / x ∂gaussianCoefficientLaw) =
    ∫ ω in P ⁻¹' A, (x - W ω r) / x ∂gaussianCoefficientLaw
  rw [setIntegral_congr_set hset, integral_div, hmoment', ← integral_div]

end SRWTightness
