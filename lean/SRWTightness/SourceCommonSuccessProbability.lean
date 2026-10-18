import SRWTightness.SourceCommonSuccessInclusion
import SRWTightness.SourceCommonHighEstimate
import SRWTightness.SourceSiteBridgeLaw

open MeasureTheory Filter
open scoped ENNReal
namespace SRWTightness

/-- On the shared enlarged space, two successes are bounded by the original common event. -/
theorem source_common_success_probability_le (t A γ : ℝ) (b w : Site) (I J j : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (z' : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ J)))
    (hz : (z : Site) = b) (hz' : (z' : Site) = w)
    (ht : sourceScaleThreshold 4 ≤ t)
    (hj : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t)) :
    sourceEnlargedLaw
      (sourceSiteSuccessEvent t A γ b I z ∩ sourceSiteSuccessEvent t A γ w J z') ≤
      pathLaw (sourceCommonActualHighEvent t b w j) := by
  have hinc : sourceSiteSuccessEvent t A γ b I z ∩ sourceSiteSuccessEvent t A γ w J z' ⊆
      sourceCommonActualHighEvent t b w j ×ˢ Set.univ := by
    intro p hp
    exact ⟨source_common_success_inclusion t A γ b w I J j z z' hz hz' ht hj
      p.1 (p.2 b) (p.2 w) hp.1 hp.2, Set.mem_univ _⟩
  have hh := measure_mono (μ := sourceEnlargedLaw) hinc
  simpa only [sourceEnlargedLaw, Measure.prod_prod, measure_univ, mul_one] using hh

/-- The manuscript's actual two-success probability inherits the common quadratic bound. -/
theorem source_common_success_probability_upper (hpot : PotentialKernelAsymptoticInput)
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (hJoint : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWJointInput (Mark K)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      sourceCoarseLowerLevel t ≤ j →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ (A γ : ℝ) (I J : ℕ)
        (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
        (z' : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ J))),
      (z : Site) = b → (z' : Site) = w →
      sourceEnlargedLaw.real
        (sourceSiteSuccessEvent t A γ b I z ∩ sourceSiteSuccessEvent t A γ w J z') ≤
        C * t ^ 2 * Real.exp
          (-(sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
            (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 /
              sourceCommonPairRowScale t b w j) := by
  obtain ⟨C, hC, hu⟩ := source_common_high_estimate hpot hGW hOcc hRes
  refine ⟨C, hC, ?_⟩
  filter_upwards [hu, eventually_ge_atTop (sourceScaleThreshold 4)] with t ht hs
  intro b w j hbw hcut hi hd hlo hhi A γ I J z z' hz hz'
  let K := sourceCommonPairObservation b w
  letI : MeasurableSpace (List (Mark K)) := ⊤
  letI : MeasurableSingletonClass (List (Mark K)) := ⟨fun _ ↦ trivial⟩
  letI : MeasurableSpace (FiniteExcursionRecord (Mark K) j) := ⊤
  letI : MeasurableSingletonClass (FiniteExcursionRecord (Mark K) j) := ⟨fun _ ↦ trivial⟩
  letI : MeasurableSpace (List (FiniteExcursionRecord (Mark K) j)) := ⊤
  letI : MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) j)) := ⟨fun _ ↦ trivial⟩
  have hh := (source_common_success_probability_le t A γ b w I J j z z' hz hz' hs hd).trans
    (ht b w j hbw hcut hi hd hlo hhi (hJoint K))
  have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [Measure.real, ENNReal.toReal_ofReal
    (show 0 ≤ C * t ^ 2 * Real.exp _ by positivity)] using hh'

end SRWTightness
