import SRWTightness.GaussianGridFinalIncrementLaw
import SRWTightness.SourceGaussianGridPath

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual source site increment is independent of the whole average path and has variance V-v0. -/
theorem sourceGaussian_final_increment (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) :
    let T := sourceObservationTime t A I
    let ν := (gaussianCoordinateLaw (brownianTimeMatrix T ((I + 1) + 1))).prod
      (independentBridgeLaw ℕ)
    1 ≤ sourcePointEnergyTime b (sourceLowerRadius t) 14 -
      sourceEquilibriumTime b (sourceLowerRadius t) A 14 ∧
    IndepFun (fun p (v : Set.Icc (0 : ℝ) (T (I + 1))) ↦ gaussianGridPath T (I + 1) p v)
      (gaussianGridFinalIncrement T (I + 1)) ν ∧
    ν.map (gaussianGridFinalIncrement T (I + 1)) = gaussianReal 0
      (sourcePointEnergyTime b (sourceLowerRadius t) 14 -
        sourceEquilibriumTime b (sourceLowerRadius t) A 14).toNNReal := by
  dsimp only
  have hg := sourceObservationTime_gaps t A hA ht I hI
  have hs := sourceObservationTime_site b t A I
  have ha := sourceObservationTime_last_average b t A I
  refine ⟨?_, gaussianGridFinalIncrement_indep_path _ _ (by omega)
    (sourceObservationTime_zero t A I) hg, ?_⟩
  · simpa only [hs, ha] using hg (I + 1) (by omega)
  · have h := gaussianGridFinalIncrement_law (sourceObservationTime t A I) (I + 1)
      (by omega) (sourceObservationTime_zero t A I) hg
    simpa only [show (I + 1) + 1 = I + 2 by omega, hs, ha] using h

/-- A shifted site window is exactly a unit window for the independent final increment. -/
theorem gaussianGrid_site_window_increment (T : ℕ → ℝ) (n : ℕ) (At V : ℝ)
    (p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :
    (At ≤ 2 * V + p.1 (Fin.last n) ∧ 2 * V + p.1 (Fin.last n) ≤ At + 1) ↔
      gaussianGridFinalIncrement T n p ∈
        Set.Icc (At - 2 * V - gaussianGridPath T n p (T n))
          (At - 2 * V - gaussianGridPath T n p (T n) + 1) := by
  unfold gaussianGridFinalIncrement
  simp only [Set.mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Source endpoint and threshold errors keep the final unit window in a fixed bounded range. -/
theorem source_site_increment_window_location (At V d q a z ε K : ℝ)
    (hAt : |At - (2 * d + q)| ≤ ε) (hV : |V - d| ≤ K)
    (hz : z ∈ Set.Icc (q - a - 1) (q - a)) :
    At - 2 * V - z ∈ Set.Icc (a - ε - 2 * K) (a + 1 + ε + 2 * K) := by
  obtain ⟨hAtL, hAtU⟩ := abs_le.mp hAt
  obtain ⟨hVL, hVU⟩ := abs_le.mp hV
  constructor <;> linarith [hz.1, hz.2]

end SRWTightness
