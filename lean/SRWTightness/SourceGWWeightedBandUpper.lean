import SRWTightness.SourceGWScalarUpperProbability
import SRWTightness.SourceCoarseTerminalWeight
import SRWTightness.SourceGWWindowIntegral
import SRWTightness.SourceGWBandScale
import SRWTightness.SourceTerminalWindowSum

open MeasureTheory Filter

namespace SRWTightness

/-- A terminal exponential upper weight integrates uniformly over the complete coarse deficit band. -/
theorem source_gw_weighted_band_upper (hUpper : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      let L := (sourceCoarseGeneration t).toNat
      ∀ (P : GeometricGWRecord → ℝ) (a : ℝ), 0 ≤ a →
      (∀ r, P r ∈ Set.Icc (0 : ℝ) 1) →
      (∀ r ∈ sourceGWCoarseBandEvent t L,
        let d := sourceLowerTime (sourceLowerRadius t)
        let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
        P r ≤ a * (Real.exp (-2 * d - 2 * q) / d)) →
      (∫ r in sourceGWCoarseBandEvent t L, P r ∂geometricGWRecordLaw 1 L) ≤
        C * a * Real.exp (-2 * t) := by
  obtain ⟨G, hG, hcoarse⟩ := source_gw_scalar_upper_probability hUpper
  obtain ⟨w, W, hw, hW, hweight⟩ := source_coarse_terminal_weight
  refine ⟨9 * (Real.exp 2 * G * W), by positivity, ?_⟩
  filter_upwards [hcoarse, hweight, source_lower_time_eventually_ge 4]
    with t hcoarse hweight hd
  dsimp only
  intro P a ha hP hpoint
  let L := (sourceCoarseGeneration t).toNat
  let d := sourceLowerTime (sourceLowerRadius t)
  let μ := geometricGWRecordLaw 1 L
  let B := sourceGWCoarseBandEvent t L
  have hPi := gw_record_probability_integrable L P hP
  have hP0 : ∀ r, 0 ≤ P r := fun r ↦ (hP r).1
  have hwindow : ∀ q : ℝ, q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      let E := sourceGWCoarseWindowEvent t L q
      (E ⊆ B → (0 : ℝ) * (Real.exp (-2 * t) * (1 + q) / d) ≤ ∫ r in E, P r ∂μ) ∧
      (∫ r in B ∩ E, P r ∂μ) ≤
        (a * Real.exp 2 * G * W) * (Real.exp (-2 * t) * (1 + q) / d) := by
    intro q hq
    let E := sourceGWCoarseWindowEvent t L q
    let wt := Real.exp (-2 * d - 2 * q) / d
    let wg := (1 + q) / (L : ℝ) ^ 2 *
      Real.exp (-(sourceTerminalRoot t q ^ 2 / (2 * (L : ℝ))))
    let v := Real.exp (-2 * t) * (1 + q) / d
    have hd0 : 0 < d := by dsimp [d]; linarith
    have hgw : μ.real E ≤ G * wg := hcoarse q hq.1 hq.2
    have hww : wg * wt ≤ W * v := (hweight q hq.1 hq.2).2
    have hi := source_gw_window_integral_bounds t L q 0 a P (B ∩ E)
      hd0 le_rfl ha hP Set.inter_subset_right (fun r hr ↦ by
        exact ⟨by simpa using hP0 r, hpoint r hr.1⟩)
    constructor
    · intro _
      simp only [zero_mul]
      exact integral_nonneg hP0
    · have hu : (∫ r in B ∩ E, P r ∂μ) ≤ (a * Real.exp 2 * wt) * μ.real (B ∩ E) := hi.2
      have hm : μ.real (B ∩ E) ≤ μ.real E := measureReal_mono Set.inter_subset_right
      calc
        _ ≤ (a * Real.exp 2 * wt) * μ.real (B ∩ E) := hu
        _ ≤ (a * Real.exp 2 * wt) * (G * wg) :=
          mul_le_mul_of_nonneg_left (hm.trans hgw) (by dsimp [wt]; positivity)
        _ = (a * Real.exp 2 * G) * (wg * wt) := by ring
        _ ≤ (a * Real.exp 2 * G) * (W * v) :=
          mul_le_mul_of_nonneg_left hww (by positivity)
        _ = _ := by ring
  have hb := (source_gw_band_integral_scale t L 0 (a * Real.exp 2 * G * W)
    P le_rfl (by positivity) hd hPi hP0 hwindow).2
  convert hb using 1 <;> ring

end SRWTightness
