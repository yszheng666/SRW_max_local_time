import SRWTightness.SourceUpperTreeComparison
import SRWTightness.SourceUpperForestBoundaryGeometry
import SRWTightness.SourceUpperBlockGrowing
import SRWTightness.BoundaryForestReferenceUpper

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Actual upper forests are bounded by independent reference roots with the root return rate. -/
theorem source_upper_forest_probability (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W L : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 1 ≤ L ∧ ∀ᶠ t : ℝ in atTop,
      ∀ b ∈ sourceUpperBlockCenters t, MarkedGWTreeInput (Mark (sourceUpperBlock t b)) →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
        (sourceUpperBlockForestDepth t b))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b)))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b)))],
      ∀ j : ℕ, 1 ≤ j →
      ∀ s : Set (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
        (sourceUpperBlockForestDepth t b))), ∀ E : ℝ,
      (∀ rs ∈ s, rs.length = j) →
      (∀ rs ∈ s, (rs.map (sourceUpperTreeError B W t (sourceUpperBlockForestDepth t b))).sum ≤ E) →
      pathLaw {ω | sourceUpperBlockForest t b (wordOccupationMark (sourceUpperBlock t b)) ω ∈ s} ≤
        ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + L)) ^ (j - 1) * Real.exp E) *
          independentForestLaw
            (finiteRecordReferenceMeasure (sourceUpperBlockMarkLaw t b)
              (sourceUpperBlockForestDepth t b)) j s := by
  obtain ⟨B, W, hB, hW, htree⟩ := source_upper_tree_probability_comparison hinput
  obtain ⟨L, hL, hreturn⟩ := source_upper_selected_root_return_rate hinput
  refine ⟨B, W, L, hB, hW, hL, ?_⟩
  filter_upwards [htree, hreturn, source_upper_block_reference_measure,
    source_upper_forest_boundary_geometry, source_upper_block_domain_geometry,
    source_upper_block_root_coarse_range, source_upper_block_root_lt_depth]
    with t ht hr hm hg hd hn hk
  intro b hb hmarked inst₁ inst₂ inst₃ inst₄ j hj s E hlen herr
  let n := sourceUpperBlockForestDepth t b
  let a := sourceUpperTraversalRadius t (sourceUpperBlockRoot t b + 1) - sourceUpperBuffer t
  let c := sourceUpperTraversalRadius t (sourceUpperBlockRoot t b) + sourceUpperBuffer t
  let F := actualFiniteWordRecord
    (growingRecordEntrance b (sourceUpperRadius t) (sourceUpperBuffer t))
    (growingRecordExit b (sourceUpperRadius t) (sourceUpperBuffer t))
    (wordOccupationMark (sourceUpperBlock t b)) n
  let μ := finiteRecordReferenceMeasure (sourceUpperBlockMarkLaw t b) n
  letI := finiteExcursionRecord_countable (Mark (sourceUpperBlock t b)) n
  letI : IsProbabilityMeasure μ := (hm b hmarked n).1
  have hgeom := hd (sourceUpperBlockRoot t b) (hn b hb) b hb
  have hsupport := hg b hb
  have hden : 1 ≤ (sourceUpperBlockRoot t b : ℝ) + L := by
    linarith [Nat.cast_nonneg (sourceUpperBlockRoot t b) (α := ℝ)]
  have hρ : 0 ≤ 1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + L) := by
    have h := (div_le_one₀ (by linarith : 0 < (sourceUpperBlockRoot t b : ℝ) + L)).mpr hden
    linarith
  have hC : translateFinset b (diskFinset c) =
      growingRecordExit b (sourceUpperRadius t) (sourceUpperBuffer t) n :=
    sourceUpperBlockOuter_growing t b (hk b hb)
  have hrad := source_single_root_radius (sourceUpperRadius t)
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (sourceUpperBlockRoot t b) (hk b hb)
  change sourceUpperTraversalRadius t (sourceUpperBlockRoot t b + 1) =
    growingRecordRadius (sourceUpperRadius t) n at hrad
  have ha : a = growingRecordRadius (sourceUpperRadius t) n - sourceUpperBuffer t := by
    dsimp [a]
    rw [hrad]
  have hF : ∀ z : Site, a - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ a → ∀ r,
      pathLaw.real {ω | F z (killedPathWord (translateFinset b (diskFinset c)) z ω) = r} ≤
        Real.exp (sourceUpperTreeError B W t n r) * μ.real {r} := by
    intro z hzlo hzhi r
    rw [ha] at hzlo hzhi
    rw [hC]
    change _ ≤ _ * (finiteRecordReferenceMeasure (sourceUpperBlockMarkLaw t b) n).real {r}
    rw [finiteRecordReferenceMeasure_real_singleton]
    exact (ht b n z r hzlo hzhi).2
  have h := boundary_forest_reference_upper (diskFinset (Real.exp t)) b a c
    hsupport.1 hgeom.1 hgeom.2 hsupport.2.1 F
    (1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + L)) hρ
    (sourceUpperTreeError B W t n) μ (hr b hb) hF 0 hsupport.2.2 j hj s E hlen herr
  simpa only [sourceUpperBlockForest_growing, sourceUpperBlockInner, sourceUpperBlockOuter,
    a, c, F, μ, n] using h

end SRWTightness
