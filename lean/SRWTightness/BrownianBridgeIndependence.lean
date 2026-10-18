import SRWTightness.BrownianBridgeResidual

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

/-- The pinned residual is uncorrelated with its Brownian endpoint. -/
theorem brownianBridgeResidual_endpoint_covariance {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (T s : ℝ≥0) (hT : T ≠ 0) (hs : s ≤ T) :
    covariance (brownianBridgeResidual B T s) (B T) P = 0 := by
  letI := hB.isGaussianProcess.isProbabilityMeasure
  have hm (u : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  unfold brownianBridgeResidual
  rw [covariance_fun_sub_left (hm s) ((hm T).const_mul _) (hm T),
    covariance_const_mul_left, hB.covariance_eval, hB.covariance_eval,
    min_eq_left hs, min_self]
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT
  field_simp
  <;> ring

/-- The entire residual and endpoint are jointly Gaussian, not merely separately Gaussian. -/
theorem brownianBridgeResidual_endpoint_joint_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    IsGaussianProcess
      (Sum.elim (fun s : Set.Iic T ↦ brownianBridgeResidual B T s)
        (fun _ : Unit ↦ B T)) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  rintro (s | u)
  · exact ⟨{(s : ℝ≥0), T},
      { toFun x := x ⟨s, by simp⟩ - ((s : ℝ≥0) : ℝ) / (T : ℝ) * x ⟨T, by simp⟩
        map_add' x y := by simp; ring
        map_smul' c x := by simp; ring }, by intro ω; simp [brownianBridgeResidual]⟩
  · exact ⟨{T},
      { toFun x := x ⟨T, by simp⟩
        map_add' x y := by simp
        map_smul' c x := by simp }, by intro ω; simp⟩

/-- The whole pinned bridge is independent of the endpoint it was removed from. -/
theorem brownianBridgeResidual_indep_endpoint {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (hT : T ≠ 0) :
    IndepFun (fun ω (s : Set.Iic T) ↦ brownianBridgeResidual B T s ω) (B T) P := by
  have hres := brownianBridgeResidual_gaussian B P hB T
  have hh := IsGaussianProcess.indepFun_of_covariance_eq_zero
    (brownianBridgeResidual_endpoint_joint_gaussian B P hB T)
    (fun s ↦ hres.aemeasurable s) (fun _ ↦ hB.aemeasurable T)
    (fun s _ ↦ brownianBridgeResidual_endpoint_covariance B P hB T s hT s.property)
  exact hh.comp measurable_id (measurable_pi_apply ())

end SRWTightness
