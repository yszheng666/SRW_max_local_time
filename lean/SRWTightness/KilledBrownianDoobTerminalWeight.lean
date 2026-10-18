import SRWTightness.KilledBrownianDoobEventReal

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Under its actual Doob law the Brownian distance path survives strictly throughout. -/
theorem killed_brownian_doob_strict_survival (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    ∀ᵐ ω ∂killedBrownianDoobCoefficientLaw T x,
      ∀ u ∈ Set.Icc (0 : ℝ) T, 0 < x - Real.sqrt T * gaussianDyadicPath ω (u / T) := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem₀ (scaled_gaussian_strict_survival_nullMeasurable hReflection T x hT hx))

/-- The whole Doob path law has a measurable survival restriction and its terminal linear weight. -/
theorem killed_brownian_doob_terminal_weight (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x)
    (B : Set (Set.Icc (0 : ℝ) T → ℝ)) (hB : MeasurableSet B) :
    (killedBrownianDoobCoefficientLaw T x).real {ω |
      (fun u : Set.Icc (0 : ℝ) T ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ B} =
    ∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) T ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ B ∧
      (fun u : Set.Icc (0 : ℝ) T ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈
        dyadicFlatPathEvent T x ∧ Real.sqrt T * gaussianDyadicPath ω (T / T) < x},
      (x - Real.sqrt T * gaussianDyadicPath ω (T / T)) / x ∂gaussianCoefficientLaw := by
  have hP : Measurable (fun ω (u : Set.Icc (0 : ℝ) T) ↦
      Real.sqrt T * gaussianDyadicPath ω (u / T)) :=
    measurable_pi_lambda _ (fun _ ↦ measurable_const.mul (gaussianDyadicPath_measurable _))
  have hPB : MeasurableSet {ω |
      (fun u : Set.Icc (0 : ℝ) T ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ B} :=
    hB.preimage hP
  rw [killed_brownian_doob_event_real hReflection T x hT hx _ hPB]
  apply setIntegral_congr_set
  filter_upwards [gaussianDyadicPath_ae_continuous,
    scaled_gaussian_barrier_boundary hReflection T x hT hx] with ω hc hb
  have hd := continuous_flat_iff_dyadic
    (fun u ↦ Real.sqrt T * gaussianDyadicPath ω (u / T))
    (continuous_const.mul (hc.comp (continuous_id.div_const T))) T x
  apply propext
  simp only [Set.mem_setOf_eq, sub_pos]
  constructor
  · rintro ⟨hs, hBω⟩
    exact ⟨hBω, hd.mp (hb.mp hs), hs T ⟨hT.le, le_rfl⟩⟩
  · rintro ⟨hBω, hflat, _⟩
    exact ⟨hb.mpr (hd.mpr hflat), hBω⟩

end SRWTightness
