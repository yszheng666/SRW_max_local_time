import SRWTightness.EventExponentialLower
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

theorem withDensity_ofReal_event_real {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x)
    (s : Set α) (hs : MeasurableSet s) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))).real s = ∫ x in s, w x ∂μ := by
  have hh := setIntegral_withDensity_eq_setIntegral_toReal_smul (μ := μ) hw.ennreal_ofReal
    (Filter.Eventually.of_forall (fun x ↦ ENNReal.ofReal_lt_top)) (fun _ ↦ (1 : ℝ)) hs
  simpa only [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    ENNReal.toReal_ofReal (hn _)] using hh

/-- Event lower comparison, including the zero-probability case without a conditional quotient. -/
theorem density_event_lower_of_moment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (w Q : α → ℝ) (C M : ℝ)
    (hw : Measurable w) (hwn : ∀ x, 0 ≤ w x) (hwb : ∀ x, w x ≤ M)
    (hQm : Measurable Q) (hQn : ∀ x, 0 ≤ Q x)
    (hwlower : ∀ x, Real.exp (-Q x / 2) ≤ w x)
    (s : Set α) (hs : MeasurableSet s) (hQ : IntegrableOn Q s μ)
    (hmean : ∫ x in s, Q x ∂μ ≤ C * μ.real s) :
    Real.exp (-C / 2) * μ.real s ≤
      (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))).real s := by
  have hE : IntegrableOn (fun x ↦ Real.exp (-Q x / 2)) s μ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    linarith [hQn x]
  have hW : IntegrableOn w s μ := by
    apply (integrable_const M).mono' hw.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hwn x)]
      exact hwb x)
  rw [withDensity_ofReal_event_real μ w hw hwn s hs]
  exact (event_exp_lower_of_integral_bound μ s Q C hQ hE hmean).trans
    (integral_mono hE hW hwlower)

end SRWTightness
