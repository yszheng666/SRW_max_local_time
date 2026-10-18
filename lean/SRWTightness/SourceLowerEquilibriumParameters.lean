import SRWTightness.SourceObservationTime
import SRWTightness.EquilibriumObservationMatrix

open scoped BigOperators
namespace SRWTightness

/-- The normalized source weights are the actual equilibrium measure divided by capacity. -/
theorem source_equilibrium_weight_formula (b : Site) (t a : ℝ) (x : Site) :
    equilibriumWeight (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
      (translateFinset b (diskFinset a)) x =
    equilibriumMeasure (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
      (translateFinset b (diskFinset a)) x /
    capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
      (translateFinset b (diskFinset a)) := rfl

/-- Every actual ordered source average time is the literal reciprocal-capacity formula. -/
theorem source_observation_capacity_time (b : Site) (t A : ℝ) (I : ℕ) (i : Fin (I + 1)) :
    sourceObservationTime t A I ((I + 1) - i.val) =
      1 / ((2 / Real.pi) *
        capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
          (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ i.val)))) -
        sourceReferenceIntensity (sourceLowerRadius t) 14 / (2 * (2 / Real.pi)) := by
  have hn : (I + 1) - i.val ≠ 0 := by omega
  have hle : (I + 1) - i.val ≤ I + 1 := by omega
  have hsub : (I + 1) - ((I + 1) - i.val) = i.val := by omega
  simp only [sourceObservationTime, geometricDiskPointTime, hle, ↓reduceIte,
    geometricDiskEnergyTime, hn, hsub, equilibriumEnergyTime, capacity_translate]

/-- The discrete diagonal of the actual equilibrium observation is its squared-weight norm. -/
theorem source_observation_discrete_error_formula (b : Site) (t A : ℝ) (I : ℕ)
    (i : Fin (I + 1)) :
    observationDiscreteError
      (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
      (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) (2 / Real.pi) (some i) =
      (∑ x ∈ translateFinset b (diskFinset (A * diskEnergyGapRatio ^ i.val)),
        equilibriumWeight
          (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
          (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ i.val))) x ^ 2) /
        (2 * (2 / Real.pi)) := rfl

end SRWTightness
