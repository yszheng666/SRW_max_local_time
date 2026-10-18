import SRWTightness.SourcePairObservationWeights
import SRWTightness.PairEquilibriumCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Both actual sites have the exact Brownian-time covariance with every retained average. -/
theorem source_pair_average_covariance (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ))
    (j : Fin (I - i + 1)) :
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let F := normalizedMarkSum M k α (2 / Real.pi) u
    let S := normalizedEquilibriumAverage D M (sourcePairAverageFamily b A I i j)
      k α (2 / Real.pi) u
    covariance (F z) S μ = sourceObservationTime t A I (j.val + 1) ∧
      covariance (F y) S μ = sourceObservationTime t A I (j.val + 1) := by
  have hj : j.val ≤ I := by omega
  have hji : i ≤ I - j.val := by omega
  obtain ⟨ha, hma, hMD, hKM, hcap⟩ :=
    source_pair_observation_geometry b t A hA ht I hI (I - j.val) (Nat.sub_le _ _)
  have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hmono : A * diskEnergyGapRatio ^ i ≤ A * diskEnergyGapRatio ^ (I - j.val) :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [diskEnergyGapRatio_gt_four]) hji) (by linarith)
  have ha2 : 2 ≤ A * diskEnergyGapRatio ^ (I - j.val) := by linarith
  have hzi : Real.sqrt (normSq ((z : Site) - b)) <
      A * diskEnergyGapRatio ^ (I - j.val) - 1 := by
    rw [hz, sub_self]
    norm_num [normSq]
    linarith
  have hyi : Real.sqrt (normSq ((y : Site) - b)) <
      A * diskEnergyGapRatio ^ (I - j.val) - 1 := by linarith
  have hm := (sourceScaleThreshold_conditions t A hA4 ((le_max_left _ _).trans ht)).2.2.1
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1
  have htime := source_observation_time_at_radius b t A I (I - j.val) (Nat.sub_le _ _)
  simp only [Nat.sub_sub_self hj] at htime
  dsimp only
  rw [htime]
  constructor
  · exact normalizedEquilibriumAverage_interior_covariance _ _ b _ ha2 hKM hMD z hzi
      _ _ u hα (by positivity) hu hcap k hk
  · exact normalizedEquilibriumAverage_interior_covariance _ _ b _ ha2 hKM hMD y hyi
      _ _ u hα (by positivity) hu hcap k hk

end SRWTightness
