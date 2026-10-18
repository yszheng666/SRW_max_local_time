import SRWTightness.DensityEntropyBound
import SRWTightness.DensityEventLower
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace SRWTightness

/-- A normalized density with integrable entropy controls every measurable event. -/
theorem density_entropy_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : Integrable f μ) (hnon : ∀ ω, 0 ≤ f ω) (hmass : ∫ ω, f ω ∂μ = 1)
    (hlog : Integrable (fun ω ↦ f ω * Real.log (f ω)) μ)
    (s : Set Ω) (hs : MeasurableSet s) :
    |(μ.withDensity (fun ω ↦ ENNReal.ofReal (f ω))).real s - μ.real s| ≤
      2 * Real.sqrt (∫ ω, f ω * Real.log (f ω) ∂μ) := by
  rw [withDensity_ofReal_event_real μ f hfm hnon s hs]
  have he : (∫ ω in s, f ω ∂μ) - μ.real s = ∫ ω in s, (f ω - 1) ∂μ := by
    rw [integral_sub hf.integrableOn (integrable_const 1)]
    simp
  rw [he]
  have habs : Integrable (fun ω ↦ |f ω - 1|) μ := (hf.sub (integrable_const 1)).abs
  calc
    _ ≤ ∫ ω in s, |f ω - 1| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, |f ω - 1| ∂μ := setIntegral_le_integral habs
      (Filter.Eventually.of_forall (fun ω ↦ abs_nonneg _))
    _ ≤ _ := (density_entropy_l1_bound μ f hf hnon hmass hlog).2

/-- Adding an independent probability space preserves the entropy event bound. -/
theorem density_entropy_event_bound_aux {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ)
    (hnon : ∀ ω, 0 ≤ f ω) (hmass : ∫ ω, f ω ∂μ = 1)
    (hlog : Integrable (fun ω ↦ f ω * Real.log (f ω)) μ)
    (s : Set (Ω × Ξ)) (hs : MeasurableSet s) :
    |((μ.withDensity (fun ω ↦ ENNReal.ofReal (f ω))).prod ν).real s - (μ.prod ν).real s| ≤
      2 * Real.sqrt (∫ ω, f ω * Real.log (f ω) ∂μ) := by
  rw [prod_withDensity_left hfm.ennreal_ofReal]
  have hm : ∫ x : Ω × Ξ, f x.1 ∂μ.prod ν = 1 := by
    simpa only [integral_fun_fst, measureReal_univ_eq_one, one_smul] using hmass
  have hh := density_entropy_event_bound (μ.prod ν) (fun x ↦ f x.1)
    (hfm.comp measurable_fst) (hf.comp_fst ν) (fun x ↦ hnon x.1) hm (hlog.comp_fst ν) s hs
  have he := integral_fun_fst (μ := μ) (ν := ν) (fun ω ↦ f ω * Real.log (f ω))
  simp only [measureReal_univ_eq_one, one_smul] at he
  rw [he] at hh
  exact hh

end SRWTightness
