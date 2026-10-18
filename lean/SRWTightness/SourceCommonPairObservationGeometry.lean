import SRWTightness.SourceCommonPairDistance
import SRWTightness.TranslatedDiskGeometry

namespace SRWTightness

/-- A ball of twice the pair distance contains both observed sites. -/
theorem source_common_pair_observation_contains (b w : Site)
    (hρ : 0 < Real.sqrt (normSq (w - b))) :
    ({b, w} : Finset Site) ⊆
      translateFinset b (diskFinset (2 * Real.sqrt (normSq (w - b)))) := by
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv
  · subst v
    rw [mem_translateFinset_iff]
    simpa using zero_mem_diskFinset (2 * Real.sqrt (normSq (w - b))) (by positivity)
  · subst v
    rw [mem_translateFinset_iff, mem_diskFinset]
    change normSq (w - b) < (2 * Real.sqrt (normSq (w - b))) ^ 2
    nlinarith [Real.sq_sqrt (normSq_nonneg (w - b))]

/-- The distance floor discharges radial and logarithmic separation for the doubled ball. -/
theorem source_common_pair_observation_separation (t ρ : ℝ) (hρ : 0 < ρ)
    (houter : ρ ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (j J : ℕ) (hj : j + J = sourceCommonPairDistanceIndex t ρ)
    (hJ : Real.log 4 + 1 ≤ (J : ℝ))
    (henergy : diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 +
      Real.log 2 + 1 ≤ (J : ℝ)) :
    2 * (2 * ρ) ≤ sourceCommonPairInnerRadius t j ∧
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤
        Real.log (sourceCommonPairInnerRadius t j) - Real.log (2 * ρ) := by
  have hs := (source_common_pair_log_separation t ρ hρ houter j J hj).1
  have hm := sourceCommonPairInnerRadius_pos t j
  constructor
  · have hl : Real.log (4 * ρ) ≤ Real.log (sourceCommonPairInnerRadius t j) := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hρ.ne']
      linarith
    have hh := (Real.log_le_log_iff (mul_pos (by norm_num : (0 : ℝ) < 4) hρ) hm).mp hl
    linarith
  · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hρ.ne']
    linarith

end SRWTightness
