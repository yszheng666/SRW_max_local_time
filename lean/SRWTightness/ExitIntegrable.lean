import SRWTightness.ExitLimit

open MeasureTheory Filter
open scoped Topology ENNReal

namespace SRWTightness

 theorem lintegral_exitSteps_le {R : ℝ} (hR : 0 ≤ R) :
    ∫⁻ ω, ENNReal.ofReal (exitSteps R ω : ℝ) ∂pathLaw ≤ ENNReal.ofReal ((R + 1) ^ 2) := by
  have hm : ∀ N, AEMeasurable
      (fun ω ↦ ENNReal.ofReal (boundedTime R N ω : ℝ)) pathLaw := fun N ↦
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (integrable_boundedTime R N).aestronglyMeasurable.aemeasurable
  have hmono : ∀ᵐ ω ∂pathLaw, Monotone
      (fun N ↦ ENNReal.ofReal (boundedTime R N ω : ℝ)) :=
    Eventually.of_forall (fun ω m n h ↦ ENNReal.ofReal_le_ofReal
      (Nat.cast_le.mpr (boundedTime_mono R ω h)))
  have ht : ∀ᵐ ω ∂pathLaw, Tendsto
      (fun N ↦ ENNReal.ofReal (boundedTime R N ω : ℝ)) atTop
      (𝓝 (ENNReal.ofReal (exitSteps R ω : ℝ))) := by
    filter_upwards [ae_tendsto_boundedTime hR] with ω hω
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hω
  apply le_of_tendsto' (lintegral_tendsto_of_tendsto_of_monotone hm hmono ht)
  intro N
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_boundedTime R N)
    (Eventually.of_forall (fun ω ↦ Nat.cast_nonneg (boundedTime R N ω)))]
  exact ENNReal.ofReal_le_ofReal (integral_boundedTime_le hR N)

/-- Integrability of the true disk exit, obtained from bounded stopping and monotone convergence. -/
theorem integrable_exitSteps {R : ℝ} (hR : 0 ≤ R) :
    Integrable (fun ω ↦ (exitSteps R ω : ℝ)) pathLaw := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun N ↦ (integrable_boundedTime R N).aestronglyMeasurable) (ae_tendsto_boundedTime hR), ?_⟩
  unfold HasFiniteIntegral
  simp_rw [Real.enorm_of_nonneg (Nat.cast_nonneg _)]
  exact lt_of_le_of_lt (lintegral_exitSteps_le hR) ENNReal.ofReal_lt_top

 theorem tendsto_integral_boundedTime {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun N ↦ ∫ ω, (boundedTime R N ω : ℝ) ∂pathLaw) atTop
      (𝓝 (∫ ω, (exitSteps R ω : ℝ) ∂pathLaw)) := by
  apply integral_tendsto_of_tendsto_of_monotone (integrable_boundedTime R)
    (integrable_exitSteps hR) _ (ae_tendsto_boundedTime hR)
  exact Eventually.of_forall (fun ω m n h ↦ Nat.cast_le.mpr (boundedTime_mono R ω h))

 theorem integral_exitSteps_le {R : ℝ} (hR : 0 ≤ R) :
    ∫ ω, (exitSteps R ω : ℝ) ∂pathLaw ≤ (R + 1) ^ 2 :=
  le_of_tendsto' (tendsto_integral_boundedTime hR) (integral_boundedTime_le hR)

end SRWTightness
