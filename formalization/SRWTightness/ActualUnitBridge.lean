import SRWTightness.GaussianUnitProcess
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

open MeasureTheory ProbabilityTheory

namespace SRWTightness

noncomputable def actualUnitBridge (t : ℝ) (ω : GaussianCoefficientSpace) : ℝ :=
  gaussianDyadicPath ω t - t * gaussianDyadicPath ω 1

theorem actualUnitBridge_zero (ω : GaussianCoefficientSpace) : actualUnitBridge 0 ω = 0 := by
  simp [actualUnitBridge, gaussianDyadicPath_zero]

theorem actualUnitBridge_one (ω : GaussianCoefficientSpace) : actualUnitBridge 1 ω = 0 := by
  simp [actualUnitBridge]

theorem actualUnitBridge_continuous :
    ∀ᵐ ω ∂gaussianCoefficientLaw, Continuous (fun t ↦ actualUnitBridge t ω) := by
  filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
  exact hω.sub (continuous_id.mul continuous_const)

theorem actualUnitBridge_measurable (t : ℝ) : Measurable (actualUnitBridge t) :=
  (gaussianDyadicPath_measurable t).sub
    (measurable_const.mul (gaussianDyadicPath_measurable 1))

theorem actualUnitBridge_mean (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (∫ ω, actualUnitBridge t ω ∂gaussianCoefficientLaw) = 0 := by
  have hmem (s : Set.Icc (0 : ℝ) 1) :=
    (gaussianPath_unit_gaussianProcess.hasGaussianLaw_eval s).integrable
  unfold actualUnitBridge
  rw [integral_sub (hmem ⟨t, ht, ht'⟩) ((hmem ⟨1, by norm_num⟩).const_mul t),
    integral_const_mul, (gaussianPath_eval_hasLaw t ht ht').integral_eq,
    (gaussianPath_eval_hasLaw 1 (by norm_num) le_rfl).integral_eq]
  simp [integral_id_gaussianReal]

theorem actualUnitBridge_covariance (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (ht : 0 ≤ t) (ht' : t ≤ 1) :
    cov[actualUnitBridge s, actualUnitBridge t; gaussianCoefficientLaw] = min s t - s * t := by
  have hm (u : Set.Icc (0 : ℝ) 1) :=
    (gaussianPath_unit_gaussianProcess.hasGaussianLaw_eval u).memLp_two
  unfold actualUnitBridge
  rw [covariance_fun_sub_fun_sub (hm ⟨s, hs, hs'⟩) ((hm ⟨1, by norm_num⟩).const_mul s)
    (hm ⟨t, ht, ht'⟩) ((hm ⟨1, by norm_num⟩).const_mul t)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  rw [gaussianPath_covariance s t hs hs' ht ht',
    gaussianPath_covariance s 1 hs hs' (by norm_num) le_rfl,
    gaussianPath_covariance 1 t (by norm_num) le_rfl ht ht',
    gaussianPath_covariance 1 1 (by norm_num) le_rfl (by norm_num) le_rfl]
  rw [min_eq_left hs', min_eq_right ht', min_self]
  ring

theorem actualUnitBridge_joint_endpoint_gaussian :
    IsGaussianProcess
      (Sum.elim (fun t : Set.Icc (0 : ℝ) 1 ↦ actualUnitBridge t)
        (fun _ : Unit ↦ fun ω ↦ gaussianDyadicPath ω 1)) gaussianCoefficientLaw := by
  classical
  let e : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  apply gaussianPath_unit_gaussianProcess.of_isGaussianProcess
  rintro (t | u)
  · exact ⟨{t, e},
      { toFun x := x ⟨t, by simp⟩ - (t : ℝ) * x ⟨e, by simp⟩
        map_add' x y := by simp; ring
        map_smul' c x := by simp; ring }, by intro ω; rfl⟩
  · exact ⟨{e},
      { toFun x := x ⟨e, by simp⟩
        map_add' x y := by simp
        map_smul' c x := by simp }, by intro ω; rfl⟩

theorem actualUnitBridge_gaussian :
    IsGaussianProcess (fun t : Set.Icc (0 : ℝ) 1 ↦ actualUnitBridge t)
      gaussianCoefficientLaw :=
  actualUnitBridge_joint_endpoint_gaussian.comp_right Sum.inl

theorem actualUnitBridge_endpoint_covariance (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    cov[actualUnitBridge t, fun ω ↦ gaussianDyadicPath ω 1; gaussianCoefficientLaw] = 0 := by
  have hm (u : Set.Icc (0 : ℝ) 1) :=
    (gaussianPath_unit_gaussianProcess.hasGaussianLaw_eval u).memLp_two
  unfold actualUnitBridge
  rw [covariance_fun_sub_left (hm ⟨t, ht, ht'⟩) ((hm ⟨1, by norm_num⟩).const_mul t)
    (hm ⟨1, by norm_num⟩), covariance_const_mul_left,
    gaussianPath_covariance t 1 ht ht' (by norm_num) le_rfl,
    gaussianPath_covariance 1 1 (by norm_num) le_rfl (by norm_num) le_rfl]
  simp [min_eq_left ht']

theorem actualUnitBridge_indep_endpoint :
    IndepFun (fun ω (t : Set.Icc (0 : ℝ) 1) ↦ actualUnitBridge t ω)
      (fun ω ↦ gaussianDyadicPath ω 1) gaussianCoefficientLaw := by
  have h := IsGaussianProcess.indepFun_of_covariance_eq_zero
    actualUnitBridge_joint_endpoint_gaussian
    (fun t ↦ (actualUnitBridge_measurable t).aemeasurable)
    (fun _ ↦ (gaussianDyadicPath_measurable 1).aemeasurable)
    (fun t _ ↦ actualUnitBridge_endpoint_covariance t t.property.1 t.property.2)
  exact h.comp measurable_id (measurable_pi_apply ())

end SRWTightness
