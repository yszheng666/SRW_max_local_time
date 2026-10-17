import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
namespace SRWTightness

/-- Strict almost-everywhere comparison of integrable functions gives strict integral comparison. -/
theorem integral_strict_of_ae_strict {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hμ : 0 < μ Set.univ) (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ ω ∂μ, f ω < g ω) : (∫ ω, f ω ∂μ) < ∫ ω, g ω ∂μ := by
  have hn : 0 ≤ᵐ[μ] (fun ω ↦ g ω - f ω) := hfg.mono (fun _ h ↦ sub_nonneg.mpr h.le)
  have hs : Function.support (fun ω ↦ g ω - f ω) =ᵐ[μ] Set.univ := by
    filter_upwards [hfg] with ω hω
    apply propext
    exact iff_of_true (ne_of_gt (sub_pos.mpr hω)) trivial
  have hp : 0 < ∫ ω, g ω - f ω ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hn (hg.sub hf)).mpr (by
      rw [measure_congr hs]
      exact hμ)
  rw [integral_sub hg hf] at hp
  exact sub_pos.mp hp

end SRWTightness
