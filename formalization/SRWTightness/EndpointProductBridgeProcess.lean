import SRWTightness.BridgedGridGaussian
import SRWTightness.ExternalBridgeReflection

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The independently sampled Gaussian endpoint and centered bridge give a Gaussian path. -/
theorem endpoint_product_bridge_gaussian (T : ℝ) (hT : 0 < T) :
    IsGaussianProcess
      (fun t : Set.Icc (0 : ℝ) T ↦ fun p : ℝ × GaussianCoefficientSpace ↦
        endpointBrownianBridge T p.1 t p.2)
      ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw) where
  hasGaussianLaw I := by
    let F : ℝ → I → ℝ := fun b t ↦ (t.val : ℝ) / T * b
    let G : GaussianCoefficientSpace → I → ℝ := fun ω t ↦ actualIntervalBridge T t.val ω
    have hF : HasGaussianLaw F (gaussianReal 0 T.toNNReal) := by
      let L : ℝ →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi
        (fun t ↦ ((t.val : ℝ) / T) • ContinuousLinearMap.id ℝ ℝ)
      exact (IsGaussian.hasGaussianLaw_id (μ := gaussianReal 0 T.toNNReal)).map L
    have hG := (actualIntervalBridge_gaussian T hT).hasGaussianLaw I
    have hmF : Measurable F := by fun_prop
    have hmG : Measurable G := measurable_pi_lambda _
      (fun t ↦ actualIntervalBridge_measurable T t.val)
    have hFp := gaussianLaw_measurePreserving (gaussianReal 0 T.toNNReal)
      ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw)
      F Prod.fst hF hmF measurePreserving_fst
    have hGp := gaussianLaw_measurePreserving gaussianCoefficientLaw
      ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw)
      G Prod.snd hG hmG measurePreserving_snd
    have hh := iIndepFun.hasGaussianLaw_fun_add hGp hFp (indepFun_prod hmF hmG).symm
    exact hh

/-- The product endpoint/bridge reconstruction has zero mean at each retained time. -/
theorem endpoint_product_bridge_mean (T t : ℝ) (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) :
    (∫ p : ℝ × GaussianCoefficientSpace, endpointBrownianBridge T p.1 t p.2
      ∂(gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw) = 0 := by
  have hg := ((actualIntervalBridge_gaussian T hT).hasGaussianLaw_eval ⟨t, ht, htT⟩).memLp_two
  have he : MemLp (fun b : ℝ ↦ b) 2 (gaussianReal 0 T.toNNReal) :=
    (IsGaussian.hasGaussianLaw_id (μ := gaussianReal 0 T.toNNReal)).memLp_two
  unfold endpointBrownianBridge
  rw [integral_add ((hg.comp_snd _).integrable (by norm_num))
      (((he.const_mul (t / T)).comp_fst _).integrable (by norm_num)),
    integral_fun_snd, integral_fun_fst, integral_const_mul,
    actualIntervalBridge_mean T t hT ht htT]
  simp [integral_id_gaussianReal]

/-- The product endpoint/bridge reconstruction has the exact Brownian covariance kernel. -/
theorem endpoint_product_bridge_covariance (T s t : ℝ) (hT : 0 < T)
    (hs : 0 ≤ s) (hsT : s ≤ T) (ht : 0 ≤ t) (htT : t ≤ T) :
    cov[fun p : ℝ × GaussianCoefficientSpace ↦ endpointBrownianBridge T p.1 s p.2,
      fun p ↦ endpointBrownianBridge T p.1 t p.2;
      (gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw] = min s t := by
  have hg (v : Set.Icc (0 : ℝ) T) :=
    ((actualIntervalBridge_gaussian T hT).hasGaussianLaw_eval v).memLp_two
  have he : MemLp (fun b : ℝ ↦ b) 2 (gaussianReal 0 T.toNNReal) :=
    (IsGaussian.hasGaussianLaw_id (μ := gaussianReal 0 T.toNNReal)).memLp_two
  simp only [endpointBrownianBridge, add_comm (actualIntervalBridge T _ _)]
  rw [covariance_product_sums _ _ (fun b : ℝ ↦ s / T * b)
    (fun b : ℝ ↦ t / T * b) (actualIntervalBridge T s) (actualIntervalBridge T t)
    (he.const_mul (s / T)) (he.const_mul (t / T))
    (hg ⟨s, hs, hsT⟩) (hg ⟨t, ht, htT⟩)]
  have hv : cov[fun b : ℝ ↦ b, fun b : ℝ ↦ b; gaussianReal 0 T.toNNReal] = T := by
    change cov[id, id; gaussianReal 0 T.toNNReal] = T
    rw [covariance_self measurable_id.aemeasurable, variance_id_gaussianReal,
      Real.coe_toNNReal T hT.le]
  rw [covariance_const_mul_left, covariance_const_mul_right, hv,
    actualIntervalBridge_covariance T s t hT hs hsT ht htT]
  field_simp
  ring

end SRWTightness
