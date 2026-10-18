import SRWTightness.ExitIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

 theorem coe_exitSteps (R : ℝ) (ω : Sample) (ht : exitTime R ω ≠ ⊤) :
    (exitSteps R ω : WithTop ℕ) = exitTime R ω := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ht
  simp [exitSteps, ← hk]
  rfl

 theorem normSq_exitSteps_bounds {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ ω ∂pathLaw, R ^ 2 ≤ normSq (position ω (exitSteps R ω)) ∧
      normSq (position ω (exitSteps R ω)) ≤ (R + 1) ^ 2 := by
  filter_upwards [exitTime_ne_top_ae hR] with ω hω
  have ht := (coe_exitSteps R ω hω).symm
  exact ⟨normSq_at_exit_ge R ω (exitSteps R ω) ht,
    normSq_at_exit_le hR ω (exitSteps R ω) ht⟩

 theorem ae_tendsto_normSq_boundedTime {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ ω ∂pathLaw, Tendsto (fun N ↦ normSq (position ω (boundedTime R N ω))) atTop
      (𝓝 (normSq (position ω (exitSteps R ω)))) := by
  filter_upwards [exitTime_ne_top_ae hR] with ω hω
  apply tendsto_const_nhds.congr'
  filter_upwards [boundedTime_eventually_eq R ω hω] with N hN
  simp only [hN]

 theorem integrable_normSq_exitSteps {R : ℝ} (hR : 0 ≤ R) :
    Integrable (fun ω ↦ normSq (position ω (exitSteps R ω))) pathLaw := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun N ↦ (integrable_normSq_boundedTime R N).aestronglyMeasurable)
    (ae_tendsto_normSq_boundedTime hR), HasFiniteIntegral.of_bounded (C := (R + 1) ^ 2) ?_⟩
  filter_upwards [normSq_exitSteps_bounds hR] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (normSq_nonneg _)] using hω.2

/-- Source equation (2.1): the stopped second-moment identity at the genuine finite disk exit. -/
theorem integral_exitSteps_eq_normSq {R : ℝ} (hR : 0 ≤ R) :
    ∫ ω, (exitSteps R ω : ℝ) ∂pathLaw =
      ∫ ω, normSq (position ω (exitSteps R ω)) ∂pathLaw := by
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Sample ↦ (R + 1) ^ 2)
    (fun N ↦ (integrable_normSq_boundedTime R N).aestronglyMeasurable)
    (integrable_const _) (fun N ↦ Eventually.of_forall (fun ω ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (normSq_nonneg _)] using
        normSq_at_boundedTime_le hR N ω)) (ae_tendsto_normSq_boundedTime hR)
  simp_rw [integral_normSq_boundedTime_eq] at ht
  exact tendsto_nhds_unique (tendsto_integral_boundedTime hR) ht

 theorem integral_exitSteps_ge {R : ℝ} (hR : 0 ≤ R) :
    R ^ 2 ≤ ∫ ω, (exitSteps R ω : ℝ) ∂pathLaw := by
  rw [integral_exitSteps_eq_normSq hR]
  calc
    R ^ 2 = ∫ _ : Sample, R ^ 2 ∂pathLaw := by simp
    _ ≤ _ := integral_mono_ae (integrable_const _) (integrable_normSq_exitSteps hR)
      ((normSq_exitSteps_bounds hR).mono (fun _ h ↦ h.1))

end SRWTightness
