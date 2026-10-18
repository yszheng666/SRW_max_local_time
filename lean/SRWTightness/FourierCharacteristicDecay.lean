import SRWTightness.SRWFourierExpectation
import SRWTightness.PotentialFourierLaw
import Mathlib.Analysis.SpecificLimits.Normed

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

theorem measurable_fourierCharacteristic : Measurable fourierCharacteristic := by
  unfold fourierCharacteristic
  fun_prop

theorem abs_fourierCharacteristic_le_one (θ : ℝ × ℝ) : |fourierCharacteristic θ| ≤ 1 := by
  apply abs_le.mpr
  unfold fourierCharacteristic
  constructor <;> linarith [Real.cos_le_one θ.1, Real.cos_le_one θ.2,
    Real.neg_one_le_cos θ.1, Real.neg_one_le_cos θ.2]

theorem fourierCharacteristic_ae_abs_lt_one : ∀ᵐ θ ∂fourierBoxMeasure,
    |fourierCharacteristic θ| < 1 := by
  have h0 : ∀ᵐ t ∂fourierIntervalMeasure, t ≠ 0 := ae_restrict_of_ae (by rw [ae_iff]; simp)
  have hp : ∀ᵐ t ∂fourierIntervalMeasure, t ≠ Real.pi := ae_restrict_of_ae (by rw [ae_iff]; simp)
  have hn : ∀ᵐ t ∂fourierIntervalMeasure, t ≠ -Real.pi := ae_restrict_of_ae (by rw [ae_iff]; simp)
  have hall : ∀ᵐ t ∂fourierIntervalMeasure, 0 < |t| ∧ |t| < Real.pi := by
    filter_upwards [fourierIntervalMeasure_support, h0, hp, hn] with t ht ht0 htp htn
    refine ⟨abs_pos.mpr ht0, abs_lt.mpr ?_⟩
    have hb := abs_le.mp ht
    exact ⟨lt_of_le_of_ne hb.1 htn.symm, lt_of_le_of_ne hb.2 htp⟩
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := fourierIntervalMeasure)
    (ν := fourierIntervalMeasure)).ae hall
  filter_upwards [h1] with θ hθ
  have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) hθ.2.le hθ.1
  have hl := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ.1) le_rfl hθ.2
  simp only [Real.cos_zero, Real.cos_abs, Real.cos_pi] at hh hl
  apply abs_lt.mpr
  unfold fourierCharacteristic
  constructor <;> linarith [Real.cos_le_one θ.2, Real.neg_one_le_cos θ.2]

theorem fourierCharacteristic_ae_pow_tendsto_zero : ∀ᵐ θ ∂fourierBoxMeasure,
    Tendsto (fun n : ℕ ↦ fourierCharacteristic θ ^ n) atTop (𝓝 0) :=
  fourierCharacteristic_ae_abs_lt_one.mono (fun θ hθ ↦ tendsto_pow_atTop_nhds_zero_of_abs_lt_one hθ)

end SRWTightness
