import SRWTightness.SourceUpperBranchingBarrier

open MeasureTheory

namespace SRWTightness

/-- The approved branching upper estimate applies to the source barrier and half-open window. -/
theorem source_upper_branching_probability (hGW : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t s u : ℝ) (k J : ℕ),
      k < sourceUpperCoarseDepth t → 0 < J → 0 ≤ s → 0 ≤ sourceUpperSlope t s →
      0 ≤ upperTerminalDepth (sourceUpperLogRadius t) →
      Real.sqrt (2 * (J : ℝ)) ≤ 4 * (sourceUpperCoarseDepth t - k : ℕ) →
      Real.sqrt 2 ≤ u → u ≤ 4 * (sourceUpperCoarseDepth t - k : ℕ) →
      u ≤ sourceUpperBranchingEnd t s →
      (geometricGWRecordLaw J (sourceUpperCoarseDepth t - k)).real
        {r | (∀ j : ℕ, 0 < j → j < sourceUpperCoarseDepth t - k →
          geometricGWHeight r j ≤ sourceUpperBarrier t s (k + j)) ∧
          geometricGWHeight r (sourceUpperCoarseDepth t - k) ∈ Set.Ico u (u + 1)} ≤
        C * gwBarrierPrefactor (sourceUpperCoarseDepth t - k) (Real.sqrt (2 * (J : ℝ))) u
          (sourceUpperBranchingStart t s k (Real.sqrt (2 * (J : ℝ))))
          (sourceUpperBranchingEnd t s) *
            Real.sqrt (Real.sqrt (2 * (J : ℝ)) /
              (u * (sourceUpperCoarseDepth t - k : ℕ))) := by
  obtain ⟨C, hC, hh⟩ := hGW 1 1 4 (1 / 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro t s u k J hk hJ hs hθ hd hx hu huL hub
  have hstart : Real.sqrt (2 * (J : ℝ)) ≤
      sourceUpperBranchingStart t s k (Real.sqrt (2 * (J : ℝ))) := by
    unfold sourceUpperBranchingStart
    have hmul := mul_nonneg hθ (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have hpow := Real.rpow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (1 / 4 : ℝ)
    linarith
  exact (measureReal_mono
    (source_upper_branching_event_subset t s (Real.sqrt (2 * (J : ℝ))) u k hk
      (Real.sqrt_nonneg _) hd) (measure_ne_top _ _)).trans
    (hh (sourceUpperCoarseDepth t - k) J _ _ u (by omega) hJ hx hu huL hstart hub)

end SRWTightness
