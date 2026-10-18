import SRWTightness.SourceReferenceIntensityLimit
import SRWTightness.GrowingRecordComparison
import SRWTightness.SourceCommonPairPowerSeparation
import SRWTightness.SourceCommonPairObservationUniform
import SRWTightness.SourceCommonPairRadiusLower
import SRWTightness.SourceTerminalCapacityHalf

open MeasureTheory Filter
namespace SRWTightness

/-- Uniform finite-record comparison at the common endpoint's actual terminal radius. -/
theorem source_common_pair_record_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (j : ℕ), b ≠ w →
      1 ≤ Real.sqrt (normSq (w - b)) →
      Real.sqrt (normSq (w - b)) ≤ sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      let m := sourceCommonPairInnerRadius t j
      let H : ℝ := 14
      let a := 2 * Real.sqrt (normSq (w - b))
      let K := sourceCommonPairObservation b w
      let η : Mark K → ℝ := fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))
      let Q : Mark K → ℝ := fun v ↦
        (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))).real {v}
      ∀ n x (r : FiniteExcursionRecord (Mark K) n),
      growingRecordRadius m n - H - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ growingRecordRadius m n - H →
      Real.exp (-finiteRecordError (fun j ↦ 4 * (B * H / growingRecordRadius m j)) η n r) *
          finiteRecordReferenceWeight Q n r ≤
        pathLaw.real {ω | actualFiniteWordRecord (growingRecordEntrance b m H)
          (growingRecordExit b m H) (wordOccupationMark K) n x
          (killedPathWord (growingRecordExit b m H n) x ω) = r} ∧
      pathLaw.real {ω | actualFiniteWordRecord (growingRecordEntrance b m H)
          (growingRecordExit b m H) (wordOccupationMark K) n x
          (killedPathWord (growingRecordExit b m H n) x ω) = r} ≤
        Real.exp (finiteRecordError (fun j ↦ 4 * (B * H / growingRecordRadius m j)) η n r) *
          finiteRecordReferenceWeight Q n r := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ := growing_record_probability_comparison hinput
  refine ⟨B, W, hB, hW, ?_⟩
  filter_upwards [source_common_pair_observation_uniform,
    eventually_ge_atTop (sourceScaleThreshold 4), eventually_ge_atTop (8 * W),
    eventually_ge_atTop (56 * B), eventually_ge_atTop (T + 14),
    eventually_ge_atTop M, eventually_ge_atTop (112 : ℝ)]
    with t hgeom htbase htW htB htT htM ht112
  intro b w j hbw hρ houter hindex hdepth
  dsimp only
  let m := sourceCommonPairInnerRadius t j
  let a := 2 * Real.sqrt (normSq (w - b))
  have hmt : t ≤ m := (sourceLowerRadius_ge_self t htbase).trans
    (sourceCommonPairInnerRadius_ge_lower t j hdepth)
  have hm0 : 0 < m := sourceCommonPairInnerRadius_pos t j
  have hs := hgeom b w j hbw hindex
  have ht0 : 0 < t := by linarith
  have hcut : a ≤ m / t ^ 6 := source_common_pair_power_separation t _ j
    (by linarith) (by linarith) houter hindex
  have hp : (2 : ℝ) ^ 6 ≤ t ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
  norm_num at hp
  have ha : 1 ≤ a := hs.1
  have hc := (le_div_iff₀ (pow_pos ht0 6)).mp hcut
  have hsep : 2 * a < m - 14 - 2 := by nlinarith
  have hcap := source_terminal_capacity_half b m 14 a (sourceCommonPairObservation b w)
    ha hs.2.1 (by norm_num) (by linarith) (Finset.Subset.refl _) hs.2.2
  have herr := source_terminal_error_small W m a t hW (by linarith) htW ha hcut
  apply hh b m 14 a (sourceCommonPairObservation b w) (by norm_num) (by linarith)
    (by linarith) (by linarith) ?_ (by linarith) hsep (Finset.Subset.refl _) hcap herr
  apply (div_le_iff₀ hm0).mpr
  nlinarith

end SRWTightness
