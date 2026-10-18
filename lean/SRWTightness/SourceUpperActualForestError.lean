import SRWTightness.SourceUpperBlockForest
import SRWTightness.SourceUpperForestErrorBound

open Filter
open scoped Topology

namespace SRWTightness

/-- Full logarithmic comparison error of the actual upper block's chronological forest. -/
noncomputable def sourceUpperBlockForestError {M : Type*} (B W t a : ℝ) (b : Site)
    (F : Site → PathWord → M) (ω : Sample) : ℝ :=
  ((sourceUpperBlockForest t b F ω).map (finiteRecordError
    (fun i ↦ 4 * (B * sourceUpperBuffer t / growingRecordRadius (sourceUpperRadius t) i))
    (fun _ ↦ 2 * (W * (a + 1) / sourceUpperRadius t *
      Real.log (sourceUpperRadius t / a))) (sourceUpperBlockForestDepth t b))).sum

/-- Actual selected roots leave a well-defined finite tree below the root. -/
theorem source_upper_block_root_lt_depth :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      sourceUpperBlockRoot t b < sourceRootDepth (Real.exp t) (sourceUpperRadius t) := by
  filter_upwards [source_upper_block_root_coarse_range, source_upper_coarse_range_eventually]
    with t hk ht
  have hpos : 1 ≤ sourceRootDepth (Real.exp t) (sourceUpperRadius t) := by
    unfold sourceRootDepth
    rw [source_upper_root_log]
    exact (Nat.one_le_floor_iff _).mpr ht
  intro b hb
  have h := hk b hb
  unfold sourceUpperCoarseDepth at h
  omega

/-- Equation (4.22): the actual root and generation caps give a uniform vanishing error bound. -/
theorem source_upper_actual_forest_error (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ a : ℝ, 1 ≤ a →
      a ≤ 2 * upperTerminalFineRadius (sourceUpperLogRadius t) →
      ∀ b ∈ sourceUpperBlockCenters t, ∀ (M : Type*) (F : Site → PathWord → M) (ω : Sample),
      (sourceUpperBlockRootCount t b ω : ℝ) ≤ t ^ 2 →
      (∀ j : ℕ, sourceUpperBlockRoot t b < j → j ≤ sourceUpperCoarseDepth t →
        (sourceUpperBlockCount t b j ω : ℝ) ≤ 16 * t ^ 2) →
      sourceUpperBlockForestError B W t a b F ω ≤
        (3584 * B + 96 * W) * t ^ 2 * sourceUpperLogRadius t *
          Real.exp (-3 * sourceUpperLogRadius t / 4) := by
  filter_upwards [source_upper_forest_error_bound B W hB hW,
    source_upper_block_root_lt_depth] with t he hk
  intro a ha har b hb M F ω hroot hcounts
  exact he a ha har M (sourceUpperBlockForestDepth t b) (sourceUpperBlockForest t b F ω)
    (source_upper_block_forest_population_cap t b F ω (hk b hb) hroot hcounts)

/-- The deterministic error majorant in (4.22) tends to zero. -/
theorem source_upper_actual_forest_error_majorant_vanishes (B W : ℝ) :
    Tendsto (fun t : ℝ ↦ (3584 * B + 96 * W) * t ^ 2 * sourceUpperLogRadius t *
      Real.exp (-3 * sourceUpperLogRadius t / 4)) atTop (𝓝 0) := by
  simpa only [mul_assoc, mul_zero] using
    source_upper_forest_scale_vanishes.const_mul (3584 * B + 96 * W)

end SRWTightness
