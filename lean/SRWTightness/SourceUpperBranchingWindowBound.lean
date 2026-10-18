import SRWTightness.GWUpperPrefactorBound
import SRWTightness.SourceUpperBranchingMargin
import SRWTightness.SourceUpperActualBranchingProbability
import SRWTightness.SourceUpperBarrierSlopeFactor

open Filter MeasureTheory

namespace SRWTightness

/-- Source equation (4.26), with the quarter-power population and squared-depth factors. -/
theorem source_upper_branching_window_bound (hScale : ExponentialFloorScaleInput)
    (hGW : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ J : ℕ, 0 < J → (J : ℝ) ≤ t ^ 2 →
      ∀ u : ℝ, t - 1 ≤ u → u ≤ sourceUpperBranchingEnd t s →
      let k := sourceUpperBlockRoot t b
      let L := sourceUpperCoarseDepth t - k
      (geometricGWRecordLaw J L).real
        {r | (∀ j : ℕ, 0 < j → j < L →
          geometricGWHeight r j ≤ sourceUpperBarrier t s (k + j)) ∧
          geometricGWHeight r L ∈ Set.Ico u (u + 1)} ≤
        C * (5 + s + k) * sourceUpperBranchingSlack t s u / (L : ℝ) ^ 2 *
          (J : ℝ) ^ (1 / 4 : ℝ) *
            Real.exp (-u ^ 2 / (2 * L) + (u / L) * Real.sqrt (2 * (J : ℝ))) := by
  obtain ⟨C, hC, hp⟩ := source_upper_actual_branching_probability hScale hGW
  refine ⟨14 * C, by positivity, ?_⟩
  filter_upwards [hp, source_upper_branching_depth_bounds,
    source_upper_barrier_slope_bounds hScale, eventually_ge_atTop (2 : ℝ)]
    with t ht hd hθ ht2
  intro b hb s hs hslog J hJ hJcap u hu hub
  dsimp only
  have hk := (hd b hb).1
  have hL : 0 < sourceUpperCoarseDepth t - sourceUpperBlockRoot t b := by omega
  have huL : (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) / (2 : ℝ) ≤ u := by
    linarith [(hd b hb).2.2]
  have hm := source_upper_branching_margin t s (Real.sqrt (2 * (J : ℝ)))
    (sourceUpperBlockRoot t b) hs (by linarith [(hθ s hs hslog).1]) (hθ s hs hslog).2
  have hbnd := gw_upper_prefactor_bound (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b)
    J u (sourceUpperBranchingStart t s (sourceUpperBlockRoot t b) (Real.sqrt (2 * (J : ℝ))))
    (sourceUpperBranchingEnd t s) (7 * (5 + s + sourceUpperBlockRoot t b)) hL
    (Nat.cast_nonneg _) huL hm.1 hm.2 (by linarith)
  have hh := (ht b hb s hs hslog J hJ hJcap u hu hub).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbnd hC.le)
  convert hh using 1 <;> first | rfl | (simp only [sourceUpperBranchingSlack]; ring)

end SRWTightness
