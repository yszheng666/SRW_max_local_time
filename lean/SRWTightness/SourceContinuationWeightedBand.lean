import SRWTightness.SourceContinuationWeightedWindow
import SRWTightness.SourceContinuationBandScale

open Filter MeasureTheory
namespace SRWTightness

/-- Full terminal-band continuation bound, before instantiating the terminal mark probability. -/
theorem source_continuation_weighted_band (hGW : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (ν L k : ℕ) (a : ℝ) (P : GeometricGWRecord → ℝ),
      ν ≤ 2 * sourceCoarseLowerLevel t →
      (ν : ℝ) + (L : ℝ) = (sourceCoarseGeneration t : ℝ) → 0 < k →
      Real.sqrt (2 * (k : ℝ)) ≤ 4 + sourceBarrierSlope t * ν → 0 ≤ a →
      (∀ r, P r ∈ Set.Icc (0 : ℝ) 1) →
      (∀ r ∈ sourceContinuationBand t ν L,
        let d := sourceLowerTime (sourceLowerRadius t)
        let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
        P r ≤ a * (Real.exp (-2 * d - 2 * q) / d)) →
      (∫ r in sourceContinuationBand t ν L, P r ∂geometricGWRecordLaw k L) ≤
        C * a * ((ν : ℝ) + 1) * Real.sqrt (Real.sqrt (2 * (k : ℝ))) / t ^ 2 *
          Real.exp (-2 * sourceLowerTime (sourceLowerRadius t)) *
          Real.exp (-((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) -
            Real.sqrt (2 * (k : ℝ))) ^ 2 / (2 * (L : ℝ)))) := by
  obtain ⟨G, hG, hw⟩ := source_continuation_weighted_window hGW
  refine ⟨9 * G, by positivity, ?_⟩
  filter_upwards [hw, source_lower_time_eventually_ge 4] with t hw hd
  intro ν L k a P hν hN hk hx ha hP hpoint
  let Q := G * a * ((ν : ℝ) + 1) * Real.sqrt (Real.sqrt (2 * (k : ℝ))) / t ^ 2 *
    Real.exp (-2 * sourceLowerTime (sourceLowerRadius t)) *
    Real.exp (-((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) -
      Real.sqrt (2 * (k : ℝ))) ^ 2 / (2 * (L : ℝ))))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hh := source_continuation_band_scale t ν L k Q P hQ hd
    (gw_forest_probability_integrable k L P hP) (fun r ↦ (hP r).1) (fun q hq ↦
      hw ν L k q a P (sourceContinuationBand t ν L ∩ sourceContinuationWindow t ν L q)
        hν hN hk hq.1 hq.2 hx ha hP Set.inter_subset_right
        (fun r hr ↦ hpoint r hr.1))
  convert hh using 1 <;> dsimp [Q] <;> ring

end SRWTightness
