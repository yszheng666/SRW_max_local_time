import SRWTightness.IntervalBridgeSuffixResidual

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The future residual has zero covariance with every earlier bridge coordinate. -/
theorem interval_bridge_suffix_past_covariance (T r s u : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrT : r < T)
    (hs : 0 ≤ s) (hsr : s ≤ r) (hu : 0 ≤ u) (huT : u ≤ T - r) :
    cov[actualIntervalBridge T s, intervalBridgeSuffixResidual T r u;
      gaussianCoefficientLaw] = 0 := by
  have hTr : 0 < T - r := sub_pos.mpr hrT
  have hru : r + u ≤ T := by linarith
  have hm (t : Set.Icc (0 : ℝ) T) :=
    ((actualIntervalBridge_gaussian T hT).hasGaussianLaw_eval t).memLp_two
  unfold intervalBridgeSuffixResidual
  rw [covariance_fun_sub_right (hm ⟨s, hs, hsr.trans hrT.le⟩)
      (hm ⟨r + u, add_nonneg hr hu, hru⟩) ((hm ⟨r, hr, hrT.le⟩).const_mul _),
    covariance_const_mul_right,
    actualIntervalBridge_covariance T s (r + u) hT hs (hsr.trans hrT.le)
      (add_nonneg hr hu) hru,
    actualIntervalBridge_covariance T s r hT hs (hsr.trans hrT.le) hr hrT.le,
    min_eq_left (by linarith : s ≤ r + u), min_eq_left hsr]
  field_simp
  <;> ring

/-- The future bridge residual has the covariance of a bridge of the remaining duration. -/
theorem interval_bridge_suffix_covariance (T r u v : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrT : r < T)
    (hu : 0 ≤ u) (huT : u ≤ T - r) (hv : 0 ≤ v) (hvT : v ≤ T - r) :
    cov[intervalBridgeSuffixResidual T r u, intervalBridgeSuffixResidual T r v;
      gaussianCoefficientLaw] = min u v - u * v / (T - r) := by
  have hTr : 0 < T - r := sub_pos.mpr hrT
  have hru : r + u ≤ T := by linarith
  have hrv : r + v ≤ T := by linarith
  have hm (t : Set.Icc (0 : ℝ) T) :=
    ((actualIntervalBridge_gaussian T hT).hasGaussianLaw_eval t).memLp_two
  unfold intervalBridgeSuffixResidual
  rw [covariance_fun_sub_fun_sub
    (hm ⟨r + u, add_nonneg hr hu, hru⟩) ((hm ⟨r, hr, hrT.le⟩).const_mul _)
    (hm ⟨r + v, add_nonneg hr hv, hrv⟩) ((hm ⟨r, hr, hrT.le⟩).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  rw [actualIntervalBridge_covariance T (r + u) (r + v) hT
      (add_nonneg hr hu) hru (add_nonneg hr hv) hrv,
    actualIntervalBridge_covariance T (r + u) r hT (add_nonneg hr hu) hru hr hrT.le,
    actualIntervalBridge_covariance T r (r + v) hT hr hrT.le (add_nonneg hr hv) hrv,
    actualIntervalBridge_covariance T r r hT hr hrT.le hr hrT.le,
    min_eq_right (by linarith : r ≤ r + u), min_eq_left (by linarith : r ≤ r + v), min_self]
  rcases le_total u v with h | h
  · rw [min_eq_left h, min_eq_left (by linarith : r + u ≤ r + v)]
    field_simp
    <;> ring
  · rw [min_eq_right h, min_eq_right (by linarith : r + v ≤ r + u)]
    field_simp
    <;> ring

end SRWTightness
