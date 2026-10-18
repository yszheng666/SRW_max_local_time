import SRWTightness.SourceUpperThresholdExpansion
import SRWTightness.RoundedTerminalThreshold
import SRWTightness.SourceReferenceIntensityError

namespace SRWTightness

/-- The normalized square root of the rounded count has inverse-height error. -/
theorem rounded_gaussian_threshold_error (g y : ℝ) (hg : 0 < g) (hy : 0 < y) :
    |Real.sqrt (2 * (Nat.ceil (g * y ^ 2 / 2) : ℝ) / g) - y| ≤ 2 / (g * y) := by
  let a := Real.sqrt (2 * (Nat.ceil (g * y ^ 2 / 2) : ℝ) / g)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hs : a ^ 2 = 2 * (Nat.ceil (g * y ^ 2 / 2) : ℝ) / g :=
    Real.sq_sqrt (by positivity)
  have hr := terminalThreshold_rounding_bounds g y hg
  have hdiff : a ^ 2 - y ^ 2 =
      (2 * ((Nat.ceil (g * y ^ 2 / 2) : ℝ) - g * y ^ 2 / 2)) / g := by
    rw [hs]
    field_simp
    <;> ring
  have hsq : 0 ≤ a ^ 2 - y ^ 2 ∧ a ^ 2 - y ^ 2 ≤ 2 / g := by
    rw [hdiff]
    exact ⟨div_nonneg (by linarith [hr.1]) hg.le,
      div_le_div_of_nonneg_right (by linarith [hr.2]) hg.le⟩
  have hay : y ≤ a := by nlinarith [hsq.1]
  change |a - y| ≤ 2 / (g * y)
  rw [abs_of_nonneg (sub_nonneg.mpr hay)]
  apply (le_div_iff₀ (mul_pos hg hy)).mpr
  have hprod : (a - y) * y ≤ 2 / g := by nlinarith [sq_nonneg (a - y)]
  have hh := (le_div_iff₀ hg).mp hprod
  nlinarith

/-- The actual reference intensity controls its square-root normalization. -/
theorem source_reference_sqrt_error (m H : ℝ) (hm : 0 < m) (hH : 0 ≤ H)
    (hHm : 5 * H ≤ m) :
    |Real.sqrt (sourceReferenceIntensity m H / (2 / Real.pi)) - 1| ≤ 4 * H / m := by
  let g : ℝ := 2 / Real.pi
  have hg : 0 < g := by dsimp [g]; positivity
  have he := sourceReferenceIntensity_error m H hm hH hHm
  have hr : 1 ≤ sourceReferenceIntensity m H / g := (one_le_div hg).mpr (by
    have hlo : 0 ≤ sourceReferenceIntensity m H - g := he.1
    linarith)
  have hs : 1 ≤ Real.sqrt (sourceReferenceIntensity m H / g) := by
    simpa using Real.sqrt_le_sqrt hr
  have hsq := Real.sq_sqrt (show 0 ≤ sourceReferenceIntensity m H / g by linarith)
  have hd : sourceReferenceIntensity m H / g - 1 ≤ 4 * H / m := by
    calc
      _ = (sourceReferenceIntensity m H - g) / g := by field_simp
      _ ≤ ((4 * g * H) / m) / g := div_le_div_of_nonneg_right he.2 hg.le
      _ = 4 * H / m := by field_simp
  change |Real.sqrt (sourceReferenceIntensity m H / g) - 1| ≤ _
  rw [abs_of_nonneg (by linarith)]
  nlinarith

/-- Actual rounded count and reference intensity give the three source threshold errors. -/
theorem source_upper_rounded_threshold_error (m H u y θ N d x q U S : ℝ)
    (hm : 0 < m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m) (hy0 : 0 < y)
    (hd : 0 ≤ d) (hu : |u| ≤ U) (hθ : |θ - 2| ≤ S)
    (hy : y = θ * (N + d)) (hx : x = θ * N) (hq : q = x - u) :
    ∃ ε : ℝ,
      Real.sqrt (2 * (Nat.ceil ((2 / Real.pi) * y ^ 2 / 2) : ℝ) / (2 / Real.pi)) -
        Real.sqrt (sourceReferenceIntensity m H / (2 / Real.pi)) * u = 2 * d + q + ε ∧
      |ε| ≤ 2 / ((2 / Real.pi) * y) + S * d + (4 * H / m) * U := by
  let a := Real.sqrt
    (2 * (Nat.ceil ((2 / Real.pi) * y ^ 2 / 2) : ℝ) / (2 / Real.pi))
  let b := Real.sqrt (sourceReferenceIntensity m H / (2 / Real.pi))
  refine ⟨a - y + (θ - 2) * d + (1 - b) * u, ?_, ?_⟩
  · exact source_upper_threshold_identity a b u y θ N d x q hy hx hq
  · exact source_upper_threshold_error_bound a b u y θ d
      (2 / ((2 / Real.pi) * y)) S (4 * H / m) U hd
      (rounded_gaussian_threshold_error (2 / Real.pi) y (by positivity) hy0) hθ
      (source_reference_sqrt_error m H hm hH hHm) hu

end SRWTightness
