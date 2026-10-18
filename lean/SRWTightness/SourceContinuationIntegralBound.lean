import SRWTightness.SourceRootExponentialIntegrable
import SRWTightness.SourceContinuationNonnegative
import SRWTightness.SourceEarlyRootCap
import SRWTightness.CappedProductIntegral

open MeasureTheory Filter
namespace SRWTightness

/-- The continuation envelope integrates against the original joint count law, with both root
caps removed. Integrability is discharged using the generic finite-domain exit moment input. -/
theorem source_continuation_integral_upper_bound (hF : TwoLevelWordFlatteningInput)
    (hExit : FiniteKilledWalkMomentInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      ∀ ν : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t → ∀ (A γ C : ℝ) (I₀ I₁ : ℕ)
      (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
      (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))), 0 ≤ C →
      (∀ k l : ℕ, k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
        sourceContinuationProbability t A γ b I₀ z₀ ν k *
          sourceContinuationProbability t A γ w I₁ z₁ ν l ≤
        C * ((ν : ℝ) + 1) ^ 3 / (Real.exp t) ^ 4 * Real.exp (-4 * ν) *
          Real.exp (2 * Real.sqrt (2 * (k : ℝ)) + 2 * Real.sqrt (2 * (l : ℝ)))) →
      ∀ S : Set Sample, MeasurableSet S →
      (∫ ω, {u | u ∈ S ∧ sourceActualCount t b ν u ≤ sourceEarlyRootCap t ν ∧
          sourceActualCount t w ν u ≤ sourceEarlyRootCap t ν}.indicator
        (fun u ↦ sourceContinuationProbability t A γ b I₀ z₀ ν (sourceActualCount t b ν u) *
          sourceContinuationProbability t A γ w I₁ z₁ ν (sourceActualCount t w ν u)) ω
        ∂pathLaw) ≤
      C * ((ν : ℝ) + 1) ^ 3 / (Real.exp t) ^ 4 * Real.exp (-4 * ν) *
        ∫ ω, S.indicator (fun u ↦ Real.exp
          (2 * Real.sqrt (2 * (sourceActualCount t b ν u : ℝ)) +
            2 * Real.sqrt (2 * (sourceActualCount t w ν u : ℝ)))) ω ∂pathLaw := by
  filter_upwards [source_root_exponential_integrable hF hExit] with t ht
  intro b w hb hw ν hν A γ C I₀ I₁ z₀ z₁ hC hbound S hS
  exact capped_product_integral_upper_bound pathLaw S
    (sourceActualCount t b ν) (sourceActualCount t w ν) (sourceEarlyRootCap t ν)
    (sourceContinuationProbability t A γ b I₀ z₀ ν)
    (sourceContinuationProbability t A γ w I₁ z₁ ν) _ _ hS (ht b w hb hw ν hν)
    (by positivity)
    (source_continuation_probability_nonneg t A γ b I₀ z₀ ν)
    (source_continuation_probability_nonneg t A γ w I₁ z₁ ν)
    (fun _ ↦ (Real.exp_pos _).le) (fun ω hk hl ↦ hbound _ _ hk hl)

end SRWTightness
