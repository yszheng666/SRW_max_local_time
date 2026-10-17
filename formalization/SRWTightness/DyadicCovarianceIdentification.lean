import SRWTightness.DyadicTentScaling
import SRWTightness.SchauderCovarianceKernel
import SRWTightness.GaussianFiniteCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem dyadicTentKernel_split (m : ℕ) (s t : ℝ) :
    dyadicTentKernel (m + 1) s t = schauderTent s * schauderTent t +
      (if s ≤ 1 / 2 ∧ t ≤ 1 / 2 then dyadicTentKernel m (2 * s) (2 * t) / 2
       else if 1 / 2 ≤ s ∧ 1 / 2 ≤ t then
         dyadicTentKernel m (2 * s - 1) (2 * t - 1) / 2 else 0) := by
  have he (m : ℕ) (s t : ℝ) : dyadicTentKernel m s t =
      ∑ n ∈ Finset.range m, dyadicLayerKernel n s t := rfl
  rw [he, Finset.sum_range_succ', dyadicLayerKernel_zero]
  split_ifs with hl hr
  · simp_rw [dyadicLayerKernel_left _ s t hl.1]
    rw [← Finset.sum_div, ← he]
    ring
  · simp_rw [dyadicLayerKernel_right _ s t hr.1]
    rw [← Finset.sum_div, ← he]
    ring
  · by_cases h : s ≤ 1 / 2
    · simp_rw [dyadicLayerKernel_cross _ s t h (show 1 / 2 ≤ t by grind)]
      simp
    · have ht : t ≤ 1 / 2 := by grind
      simp_rw [dyadicLayerKernel_symm _ s t,
        dyadicLayerKernel_cross _ t s ht (show 1 / 2 ≤ s by linarith)]
      simp

theorem dyadicTentKernel_eq_bridgeKernelApprox (m : ℕ) (s t : ℝ) :
    dyadicTentKernel m s t = bridgeKernelApprox m s t := by
  induction m generalizing s t with
  | zero => simp [dyadicTentKernel, bridgeKernelApprox]
  | succ m ih =>
    rw [dyadicTentKernel_split, bridgeKernelApprox]
    simp_rw [ih]

theorem gaussianFinitePath_covariance_error (m : ℕ) (s t : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    |cov[gaussianFinitePath (m, s), gaussianFinitePath (m, t); gaussianCoefficientLaw] -
      min s t| ≤ (1 / 2 : ℝ) ^ m / 4 := by
  rw [gaussianFinitePath_covariance_explicit, dyadicTentKernel_eq_bridgeKernelApprox,
    abs_sub_comm]
  have h := bridgeKernelApprox_error m s t hs hs' ht ht'
  convert h using 1
  unfold unitBridgeKernel
  congr 1
  ring

end SRWTightness
