import SRWTightness.SourceEarlyCommonPrefixError
import SRWTightness.SourceCommonActualHighInclusion
import SRWTightness.SourceEarlyPrefixEvent

open Filter
namespace SRWTightness

/-- The original prefix event selects one actual common record with exactly the original barrier. -/
theorem source_common_actual_prefix (t : ℝ) (b : Site) (K : Finset Site) (j : ℕ)
    (ω : Sample) (hω : ω ∈ sourceEarlyPrefixEvent t b j) :
    ∃ r : FiniteExcursionRecord (Mark K) j, sourceCommonActualForest t b K j ω = [r] ∧
      ∀ k : ℕ, 0 < k → k ≤ j →
      geometricGWHeight (finiteRecordPopulationList j r) k ≤
        4 + sourceBarrierSlope t * k -
          (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ) := by
  have hlen := (source_common_actual_forest_length t b K j ω).trans hω.1
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨r, hr, ?_⟩
  intro k hk hkj
  unfold geometricGWHeight
  rw [source_common_actual_forest_population t b K j ω r hr k hkj]
  exact hω.2 k hk hkj

/-- The full error bound of equation 8.12 applies to the actual original common record selected
by G_j, including its root count, chronological populations and terminal occupation marks. -/
theorem source_early_common_actual_error (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ρ := Real.sqrt (normSq (w - b))
      ∀ ω : Sample, ω ∈ sourceEarlyPrefixEvent t b j →
      ∃ r : FiniteExcursionRecord (Mark (sourceCommonPairObservation b w)) j,
      sourceCommonActualForest t b (sourceCommonPairObservation b w) j ω = [r] ∧
      finiteRecordError
        (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceCommonPairInnerRadius t j) i))
        (fun _ ↦ 2 * (W * (2 * ρ + 1) / sourceCommonPairInnerRadius t j *
          Real.log (sourceCommonPairInnerRadius t j / (2 * ρ)))) j r ≤
        57 * (128 * B + 48 * Real.exp 1 * W) := by
  obtain ⟨Jmin, hh⟩ := source_early_common_prefix_error B W hB hW
  refine ⟨Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, ht⟩ := hh J₀ hJ₀
  refine ⟨a₀, ha₀, ?_⟩
  filter_upwards [ht] with t ht
  intro b w hbw ha hrange
  dsimp only
  intro ω hω
  obtain ⟨r, hr, hbar⟩ := source_common_actual_prefix t b
    (sourceCommonPairObservation b w) _ ω hω
  exact ⟨r, hr, ht b w hbw ha hrange _ r hbar⟩

end SRWTightness
