import SRWTightness.SourceUpperBlockSuccess
import SRWTightness.SourceUpperBarrierCountCap

open Filter MeasureTheory

namespace SRWTightness

/-- Block success and finite-record success have the same actual path probability. -/
theorem source_upper_block_success_probability :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t, ∀ s : ℝ,
      pathLaw (sourceUpperBlockSuccess t s b) =
        pathLaw {ω | sourceUpperBlockForest t b
          (wordOccupationMark (sourceUpperBlock t b)) ω ∈ sourceUpperForestSuccess t s b} := by
  filter_upwards [source_upper_block_success_iff_ae] with t ht
  intro b hb s
  apply measure_congr
  filter_upwards [ht b hb] with ω hω
  exact propext (hω s)

/-- Every reference record in the capped success event satisfies all generation bounds. -/
theorem source_upper_success_forest_cap (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ rs : List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
        (sourceUpperBlockForestDepth t b)),
      rs ∈ sourceUpperForestSuccess t s b → (rs.length : ℝ) ≤ t ^ 2 →
      ∀ i ≤ sourceUpperBlockForestDepth t b,
        (forestLevelPopulation (sourceUpperBlockForestDepth t b) rs i : ℝ) ≤ 16 * t ^ 2 := by
  filter_upwards [source_upper_barrier_count_cap hScale,
    source_upper_block_root_lt_depth] with t ht hk
  intro b hb s hs hslog rs hrs hroot i hi
  by_cases heq : i = sourceUpperBlockForestDepth t b
  · subst i
    have he : forestLevelPopulation (sourceUpperBlockForestDepth t b) rs
        (sourceUpperBlockForestDepth t b) = rs.length := by
      simp [forestLevelPopulation, finiteRecordLevelPopulation_root]
    rw [he]
    nlinarith [sq_nonneg t]
  · let ℓ := sourceRootDepth (Real.exp t) (sourceUpperRadius t)
    let j := ℓ - (i + 1)
    have hki := hk b hb
    have hi' : i ≤ ℓ - (sourceUpperBlockRoot t b + 1) := hi
    have hn : i ≠ ℓ - (sourceUpperBlockRoot t b + 1) := heq
    have hj : sourceUpperBlockRoot t b < j := by dsimp [j]; omega
    have hjN : j ≤ sourceUpperCoarseDepth t := by
      change j ≤ ℓ - 1
      dsimp [j]
      omega
    have hidx : ℓ - (j + 1) = i := by dsimp [j]; omega
    have hbar := hrs.2 j hj hjN
    change Real.sqrt (2 * (forestLevelPopulation _ rs (ℓ - (j + 1)) : ℝ)) ≤ _ at hbar
    rw [hidx] at hbar
    exact ht s hs hslog j hjN _ hbar

end SRWTightness
