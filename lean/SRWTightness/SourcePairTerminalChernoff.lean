import SRWTightness.SourcePairReferenceChernoff
import SRWTightness.SourceTerminalThresholdAsymptotic
import SRWTightness.SourceGreenScaleComparison

open MeasureTheory ProbabilityTheory Filter Matrix

namespace SRWTightness

noncomputable def sourcePairChernoffConstant : ℝ :=
  let C : ℝ := 1 + 4 * sourcePairVarianceError +
      4 * (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 +
        Real.log (4 * diskEnergyGapRatio)) + 1 / (2 / Real.pi)
  Real.exp (C + 4)

theorem sourcePairChernoffConstant_pos : 0 < sourcePairChernoffConstant := by
  exact Real.exp_pos _

/-- The pair Chernoff bound at the actual terminal root and threshold. -/
theorem source_pair_terminal_chernoff :
    ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (A : ℝ)
      (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (q : ℝ)
    (hq : Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q)
    (hqu : q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
    (k : ℕ) (hk : (sourceTerminalRoot t q) ^ 2 / 2 = (k : ℝ))
    (f : ℝ),
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let F := fun j ↦ normalizedWeightedSum M k α (2 / Real.pi) (sourceTerminalRoot t q)
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j)
    let d := sourceLowerTime (sourceLowerRadius t)
    let h := d - sourceObservationTime t A I (I - i + 1)
    ((μ.map (fun Y j ↦ F j Y)).prod (independentBridgeLaw ℕ)).real
      (sourcePairUpperEvent t A I i (sourceTerminalThreshold t (sourceTerminalRoot t q)) q f) ≤
      sourcePairChernoffConstant * Real.exp (-2 * d - 2 * h - 2 * q - 2 * f) := by
  have hasmall := (tendsto_order.1 sourceTerminalThresholdError_tendsto_zero).2 1
    (by norm_num)
  filter_upwards [source_pair_reference_chernoff,
    source_deficit_large_conditions, hasmall] with t happ htlarge herr
  intro b A hA ht I hI i hi z y hz hρ hlo hhi q hq hqu k hk f
  have hd := sourceLowerTime_ge_one t htlarge.1
  have hd0 : 0 < sourceLowerTime (sourceLowerRadius t) := by linarith
  have hu := sourceTerminalRoot_bounds t q htlarge.1 htlarge.2.1
    htlarge.2.2.1 htlarge.2.2.2 hq hqu
  have ha := sourceTerminalThreshold_target_error t q htlarge.1 htlarge.2.1
    htlarge.2.2.1 htlarge.2.2.2 hq hqu
  have hAt : 2 * sourceLowerTime (sourceLowerRadius t) + q - 1 ≤
      sourceTerminalThreshold t (sourceTerminalRoot t q) := by
    linarith [(abs_le.mp ha).1]
  have hp := happ A b hA ht I hI i hi z y hz hρ hlo hhi
    (sourceTerminalRoot t q) hu.1 k hk
    (sourceTerminalThreshold t (sourceTerminalRoot t q)) q f 1 hAt
  simpa only [sourcePairChernoffConstant, mul_one] using hp

end SRWTightness
