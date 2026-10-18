import SRWTightness.ExitRootMeanLogBound

open MeasureTheory
namespace SRWTightness

/-- Bounded capacities and logarithmic gaps give a linear future-root mean bound. -/
theorem exit_root_pair_mean_linear_bound (hLast : FiniteLastVisitCountInput)
    (c b w x : Site) (R r a : ℝ) (hR : 1 ≤ R) (ha : 0 ≤ a) (har : a < r)
    (hsep : 0 < Real.sqrt (normSq (w - b)) - (r + 1) - a)
    (hx : x ∈ domainExitBoundary (translateFinset b (diskFinset r)))
    (hxD : x ∈ translateFinset c (diskFinset R))
    (hC₁D : translateFinset b (diskFinset r) ⊆ translateFinset c (diskFinset R))
    (hC₂D : translateFinset w (diskFinset r) ⊆ translateFinset c (diskFinset R))
    (J K M : ℝ) (hJ : 0 ≤ J) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hcap : capacity (diskFinset r) (diskFinset a) ≤ M)
    (hlog₁ : Real.log (2 * R / (r - a)) ≤ 2 * J + K)
    (hlog₂ : Real.log (2 * R /
      (Real.sqrt (normSq (w - b)) - (r + 1) - a)) ≤ 2 * J + K) :
    (∫ Y, ((wordMarkRootCount (translateFinset b (diskFinset a))
      (translateFinset b (diskFinset r)) Y +
      wordMarkRootCount (translateFinset w (diskFinset a))
      (translateFinset w (diskFinset r)) Y : ℕ) : ℝ)
      ∂killedWordMarkLaw (translateFinset c (diskFinset R)) x) ≤
      (2 * M * (2 * (2 / Real.pi) + (2 / Real.pi) * K +
        |diskGreenAdditiveConstant|)) * (J + 1) := by
  let g : ℝ := 2 / Real.pi
  let B := 2 * g + g * K + |diskGreenAdditiveConstant|
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbase := exit_root_pair_mean_log_bound hLast c b w x R r a hR ha har
    hsep hx hxD hC₁D hC₂D
  have hup (q : ℝ) (hq : q ≤ 2 * J + K) :
      g * q + diskGreenAdditiveConstant ≤ B * (J + 1) := by
    have hh := mul_le_mul_of_nonneg_left hq hg
    have hb := le_abs_self diskGreenAdditiveConstant
    have hk := mul_nonneg (add_nonneg (mul_nonneg hg hK)
      (abs_nonneg diskGreenAdditiveConstant)) hJ
    dsimp [B]
    nlinarith
  have hcp := capacity_nonneg (diskFinset r) (diskFinset a)
  have h₁ := mul_le_mul_of_nonneg_right (hup _ hlog₁) hcp
  have h₂ := mul_le_mul_of_nonneg_right (hup _ hlog₂) hcp
  have h₃ := mul_le_mul_of_nonneg_left hcap
    (mul_nonneg hB (by linarith : 0 ≤ J + 1))
  change _ ≤ (2 * M * B) * (J + 1)
  change _ ≤ (g * _ + _) * _ + (g * _ + _) * _ at hbase
  nlinarith

end SRWTightness
