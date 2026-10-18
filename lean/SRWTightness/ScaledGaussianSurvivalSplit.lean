import SRWTightness.ScaledGaussianStrictSurvivalMeasurable

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Strict survival splits almost surely into a measurable past and closed future survival. -/
theorem scaled_gaussian_survival_split (hReflection : BridgeReflectionInput)
    (T x r : ℝ) (hT : 0 < T) (hx : 0 < x) (hr : 0 ≤ r) (hrT : r < T) :
    ∀ᵐ ω ∂gaussianCoefficientLaw,
      (∀ u ∈ Set.Icc (0 : ℝ) T, 0 < x - Real.sqrt T * gaussianDyadicPath ω (u / T)) ↔
      ((fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈
        dyadicFlatPathEvent r x ∧ Real.sqrt T * gaussianDyadicPath ω (r / T) < x ∧
        ∀ u ∈ Set.Icc (0 : ℝ) (T - r),
          Real.sqrt T * gaussianDyadicPath ω ((r + u) / T) ≤ x) := by
  filter_upwards [gaussianDyadicPath_ae_continuous,
    scaled_gaussian_barrier_boundary hReflection T x hT hx] with ω hc hb
  let W := fun u ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  have hcont : Continuous W := continuous_const.mul (hc.comp (continuous_id.div_const T))
  have hd := continuous_flat_iff_dyadic W hcont r x
  constructor
  · intro hs
    have hflat (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) T) : W u ≤ x :=
      (sub_pos.mp (hs u hu)).le
    refine ⟨hd.mp (fun u hu ↦ hflat u ⟨hu.1, hu.2.trans hrT.le⟩),
      sub_pos.mp (hs r ⟨hr, hrT.le⟩), ?_⟩
    intro u hu
    exact hflat (r + u) ⟨add_nonneg hr hu.1, by linarith [hu.2]⟩
  · rintro ⟨hp, _, hf⟩
    have hpast := hd.mpr hp
    have hfull : ∀ u ∈ Set.Icc (0 : ℝ) T, W u ≤ x := by
      intro u hu
      by_cases hur : u ≤ r
      · exact hpast u ⟨hu.1, hur⟩
      · have hv : u - r ∈ Set.Icc (0 : ℝ) (T - r) :=
          ⟨by linarith, by linarith [hu.2]⟩
        have hh := hf (u - r) hv
        rwa [show r + (u - r) = u by ring] at hh
    intro u hu
    exact sub_pos.mpr (hb.mpr hfull u hu)

end SRWTightness
