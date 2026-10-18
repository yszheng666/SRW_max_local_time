import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

/-- The pinned residual on a Brownian interval of length T. -/
noncomputable def brownianBridgeResidual {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (T s : ℝ≥0) (ω : Ω) : ℝ := B s ω - ((s : ℝ) / (T : ℝ)) * B T ω

theorem brownianBridgeResidual_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    IsGaussianProcess (brownianBridgeResidual B T) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro s
  exact ⟨{s, T},
    { toFun x := x ⟨s, by simp⟩ - ((s : ℝ) / (T : ℝ)) * x ⟨T, by simp⟩
      map_add' x y := by simp; ring
      map_smul' c x := by simp; ring }, by intro ω; simp [brownianBridgeResidual]⟩

theorem brownianBridgeResidual_mean {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P) (T s : ℝ≥0) :
    (∫ ω, brownianBridgeResidual B T s ω ∂P) = 0 := by
  unfold brownianBridgeResidual
  rw [integral_sub (hB.integrable_eval s) ((hB.integrable_eval T).const_mul _),
    integral_const_mul, hB.integral_eval s, hB.integral_eval T, mul_zero, sub_zero]

theorem brownianBridgeResidual_zero {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, brownianBridgeResidual B T 0 ω = 0 := by
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
  simp [brownianBridgeResidual, hω]

theorem brownianBridgeResidual_terminal {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (hT : T ≠ 0) (ω : Ω) : brownianBridgeResidual B T T ω = 0 := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT
  simp [brownianBridgeResidual, hT']

/-- The pinned residual has the Brownian bridge covariance kernel. -/
theorem brownianBridgeResidual_covariance {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (T s t : ℝ≥0) (hT : T ≠ 0) (hs : s ≤ T) (ht : t ≤ T) :
    covariance (brownianBridgeResidual B T s) (brownianBridgeResidual B T t) P =
      min (s : ℝ) (t : ℝ) - (s : ℝ) * (t : ℝ) / (T : ℝ) := by
  letI := hB.isGaussianProcess.isProbabilityMeasure
  have hm (u : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  unfold brownianBridgeResidual
  rw [covariance_fun_sub_fun_sub (hm s) ((hm T).const_mul _) (hm t) ((hm T).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval,
    min_eq_left hs, min_eq_right ht, min_self, NNReal.coe_min]
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT
  field_simp
  <;> ring

/-- Continuous Brownian paths give continuous pinned residuals. -/
theorem brownianBridgeResidual_continuous {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, Continuous (fun s ↦ brownianBridgeResidual B T s ω) := by
  filter_upwards [hB.cont] with ω hω
  exact hω.sub ((continuous_subtype_val.div_const (T : ℝ)).mul continuous_const)

end SRWTightness
