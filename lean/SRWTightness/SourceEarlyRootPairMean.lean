import SRWTightness.SourceEarlyCommonRootMean

open MeasureTheory Filter
namespace SRWTightness

/-- The actual two-label common-mark mean, retaining the same probability space. -/
theorem source_early_root_pair_mean (hLast : FiniteLastVisitCountInput) :
    ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      (∫ Y, ((sourceCommonWordRootCount t b ν Y +
        sourceCommonWordRootCount t w ν Y : ℕ) : ℝ) ∂sourceCommonWordLaw t b w j) =
      2 * sourceCommonPairIntensity t j * capacity
        (sourceExitDomain (sourceLowerRadius t) 1
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
        (sourceEntranceDomain (sourceLowerRadius t) 1
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν) := by
  obtain ⟨Jmin, hmean⟩ := source_early_common_root_mean hLast
  refine ⟨Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, hm⟩ := hmean J₀ hJ₀
  refine ⟨a₀, ha₀, ?_⟩
  filter_upwards [hm] with t ht
  intro b w hbw ha hrange
  dsimp only
  have hb := (ht b w hbw ha hrange).2 b (by simp)
  have hw := (ht b w hbw ha hrange).2 w (by simp)
  simp only [Nat.cast_add]
  rw [integral_add hb.1 hw.1, hb.2, hw.2]
  simp only [sourceExitDomain, sourceEntranceDomain, capacity_translate]
  ring

end SRWTightness
