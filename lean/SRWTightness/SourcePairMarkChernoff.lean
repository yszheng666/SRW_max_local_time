import SRWTightness.SourcePairMarkProbability
import SRWTightness.SourcePairTerminalChernoff

open MeasureTheory ProbabilityTheory Filter

namespace SRWTightness

/-- The pair bound applies to every population in the actual GW deficit band. -/
theorem source_pair_mark_probability_chernoff :
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
    (L : ℕ) (r : GeometricGWRecord) (hr : r ∈ sourceGWCoarseBandEvent t L)
    (f : ℝ),
    let d := sourceLowerTime (sourceLowerRadius t)
    let h := d - sourceObservationTime t A I (I - i + 1)
    let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
    sourcePairMarkProbability t A b I i z y (geometricGWPopulation r L) f ≤
      sourcePairChernoffConstant *
        Real.exp (-2 * d - 2 * h - 2 * q - 2 * f) := by
  filter_upwards [source_pair_terminal_chernoff] with t happ
  intro b A hA ht I hI i hi z y hz hρ hlo hhi L r hr f
  let k := geometricGWPopulation r L
  let u := geometricGWHeight r L
  let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
  have hq : Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q ∧
      q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) := hr.2
  have hc := source_gw_terminal_count_identity t L r
  have hp := happ b A hA ht I hI i hi z y hz hρ hlo hhi
    q hq.1 hq.2 k hc.2 f
  dsimp only at hp
  rw [hc.1] at hp
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let μ := markProductLaw D M α k
  have hg := source_pair_observation_geometry b t A hA ht I hI i hi
  have hs := sourceScaleThreshold_conditions t A
    (diskGaussianMinimumRadius_ge_four.trans (diskPointGaussianMinimumRadius_ge_base.trans hA))
    ((le_max_left _ _).trans ht)
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith [hs.2.2.1])).1
  letI : IsProbabilityMeasure μ := markProductLaw_isProbabilityMeasure D M α hα.le hg.2.2.2.2 k
  have he := source_pair_original_probability b t A I i hA ht hI D M z y k α
    (2 / Real.pi) u (sourceTerminalThreshold t u) q f μ
  exact he.trans_le hp

end SRWTightness
