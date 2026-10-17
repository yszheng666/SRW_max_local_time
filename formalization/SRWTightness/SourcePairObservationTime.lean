import SRWTightness.SourceObservationTime

namespace SRWTightness

/-- The radius indexed from small to large occurs at the reversed increasing-time node. -/
theorem source_observation_time_at_radius (b : Site) (t A : ℝ) (I i : ℕ) (hi : i ≤ I) :
    sourceObservationTime t A I (I - i + 1) =
      sourceEquilibriumTime b (sourceLowerRadius t) (A * diskEnergyGapRatio ^ i) 14 := by
  have hle : I - i + 1 ≤ I + 1 := by omega
  have hne : I - i + 1 ≠ 0 := by omega
  have he : I + 1 - (I - i + 1) = i := by omega
  simp only [sourceObservationTime, geometricDiskPointTime, hle, ↓reduceIte,
    geometricDiskEnergyTime, hne, he, sourceEquilibriumTime, equilibriumEnergyTime_translate]

/-- The deficit at that actual node differs from the logarithm of its radius by a uniform constant. -/
theorem source_pair_node_deficit_log_radius (b : Site) (t A : ℝ) (I i : ℕ) (hi : i ≤ I)
    (ha : 1 ≤ A * diskEnergyGapRatio ^ i)
    (hma : 2 * (A * diskEnergyGapRatio ^ i) ≤ sourceLowerRadius t)
    (hm : 70 ≤ sourceLowerRadius t) :
    |(sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)) -
      Real.log (A * diskEnergyGapRatio ^ i)| ≤
        sourceEquilibriumTimeError + sourceLowerTimeError := by
  rw [source_observation_time_at_radius b t A I i hi]
  have hh := sourceEquilibriumTime_lowerTime_bound b (sourceLowerRadius t)
    (A * diskEnergyGapRatio ^ i) 14 ha hma (by norm_num) (by linarith)
  have he : (sourceLowerTime (sourceLowerRadius t) -
      sourceEquilibriumTime b (sourceLowerRadius t) (A * diskEnergyGapRatio ^ i) 14) -
      Real.log (A * diskEnergyGapRatio ^ i) =
    -(sourceEquilibriumTime b (sourceLowerRadius t) (A * diskEnergyGapRatio ^ i) 14 -
      (sourceLowerTime (sourceLowerRadius t) - Real.log (A * diskEnergyGapRatio ^ i))) := by ring
  rw [he, abs_neg]
  exact hh

end SRWTightness
