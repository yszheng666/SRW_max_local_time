import SRWTightness.PeriodicBoxIntegral

open MeasureTheory Function

namespace SRWTightness

theorem continuous_integrable_fourierBox (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    Integrable F fourierBoxMeasure := by
  unfold fourierBoxMeasure fourierIntervalMeasure
  rw [Measure.prod_restrict]
  exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- The degree-two torus change of variables preserves the unnormalized square average. -/
theorem fourierBox_integral_rotation (F : ℝ × ℝ → ℝ) (hF : Continuous F)
    (h1 : ∀ y, Periodic (fun x ↦ F (x, y)) (2 * Real.pi))
    (h2 : ∀ x, Periodic (fun y ↦ F (x, y)) (2 * Real.pi)) :
    (∫ p, F (p.1 + p.2, p.1 - p.2) ∂fourierBoxMeasure) = ∫ p, F p ∂fourierBoxMeasure := by
  have hI := continuous_integrable_fourierBox (fun p ↦ F (p.1 + p.2, p.1 - p.2)) (by fun_prop)
  have hJ := continuous_integrable_fourierBox (fun p : ℝ × ℝ ↦ F (p.2, 2 * p.1 - p.2)) (by fun_prop)
  have hinner (u : ℝ) : (∫ v, F (u + v, u - v) ∂fourierIntervalMeasure) =
      ∫ t, F (t, 2 * u - t) ∂fourierIntervalMeasure := by
    have hg : Periodic (fun t ↦ F (t, 2 * u - t)) (2 * Real.pi) := by
      intro t
      change F (t + 2 * Real.pi, 2 * u - (t + 2 * Real.pi)) = F (t, 2 * u - t)
      rw [show 2 * u - (t + 2 * Real.pi) = (2 * u - t) - 2 * Real.pi by ring]
      have hh1 := h1 ((2 * u - t) - 2 * Real.pi) t
      change F (t + 2 * Real.pi, (2 * u - t) - 2 * Real.pi) = F (t, (2 * u - t) - 2 * Real.pi) at hh1
      rw [hh1]
      have hh := h2 t ((2 * u - t) - 2 * Real.pi)
      simpa only [sub_add_cancel] using hh.symm
    calc
      _ = ∫ v, F (v + u, 2 * u - (v + u)) ∂fourierIntervalMeasure := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro v
        congr 1 <;> ring
      _ = _ := fourierInterval_integral_translate _ hg u
  change (∫ p, F (p.1 + p.2, p.1 - p.2) ∂fourierIntervalMeasure.prod fourierIntervalMeasure) = _
  rw [integral_prod _ hI]
  calc
    _ = ∫ u, ∫ t, F (t, 2 * u - t) ∂fourierIntervalMeasure ∂fourierIntervalMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hinner
    _ = ∫ t, ∫ u, F (t, 2 * u - t) ∂fourierIntervalMeasure ∂fourierIntervalMeasure :=
      integral_integral_swap (f := fun u t ↦ F (t, 2 * u - t)) hJ
    _ = ∫ t, ∫ v, F (t, v) ∂fourierIntervalMeasure ∂fourierIntervalMeasure := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      simpa only [sub_eq_add_neg] using
        fourierInterval_integral_double_translate (fun v ↦ F (t, v)) (h2 t) (by fun_prop) (-t)
    _ = _ := (integral_prod F (continuous_integrable_fourierBox F hF)).symm

end SRWTightness
