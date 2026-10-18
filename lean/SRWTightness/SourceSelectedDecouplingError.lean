import SRWTightness.SourceSelectedFineError
import SRWTightness.SourceGroupedFineCount

open MeasureTheory Filter
namespace SRWTightness

/-- The actual label-selected comparison errors satisfy the quantitative two-site bound. -/
theorem source_selected_decoupling_error_bound (hF : TwoLevelWordFlatteningInput)
    (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ (K₀ K₁ : Finset Site) (a₀ a₁ A C : ℝ),
      1 ≤ a₀ → a₀ ≤ sourceLowerRadius t / t ^ 6 →
      1 ≤ a₁ → a₁ ≤ sourceLowerRadius t / t ^ 6 → 0 ≤ A → 0 ≤ C →
      ∀ᵐ ω ∂pathLaw,
      sourceActualCount t b 0 ω = 1 → sourceWalkCoarseBand t b ω →
      sourceActualCount t w 0 ω = 1 → sourceWalkCoarseBand t w ω →
      sourceSelectedFineError A C B W t a₀ a₁ b w K₀ K₁ ν J ω ≤
        16 * ((ν : ℝ) + 1) ^ 2 *
          (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
            C * 15 / (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
          2 * sourceForestQuadraticError B W 8 t := by
  filter_upwards [source_decoupling_error_envelope_bound hF B W hB hW,
    source_grouped_fine_count hF, source_root_gw_horizon_large,
    source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with t he hcount hN htime hm ht
  intro b w ν J hb hw hbw ha hν hform K₀ K₁ a₀ a₁ A C ha₀ hc₀ ha₁ hc₁ hA hC
  have hnreal : (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by exact_mod_cast hnreal
  have hi : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
    have hp := hN.1
    omega
  have hr := sourceRecordRadius_ge_terminal (sourceLowerRadius t) (sourceLowerRadius_pos t).le
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) hi
  filter_upwards [he b w ν J hb hw hbw ha hν hform K₀ K₁ a₀ a₁ A C ha₀ hc₀ ha₁ hc₁ hA hC,
    hcount b w ν J hb hw hbw ha hν hform b (Or.inl rfl) K₀,
    hcount b w ν J hb hw hbw ha hν hform w (Or.inr rfl) K₁] with ω heω h₀ h₁
  intro hr₀ hb₀ hr₁ hb₁
  have hs := source_selected_fine_error_bound A C B W t a₀ a₁ b w K₀ K₁ ν J ω
    hC hB hW ht ha₀ hc₀ ha₁ hc₁ (by linarith)
  rw [h₀, h₁] at hs
  have henv : sourceSelectedFineError A C B W t a₀ a₁ b w K₀ K₁ ν J ω ≤
      sourceDecouplingErrorEnvelope A C B W t a₀ a₁ b w K₀ K₁ ν J ω := by
    simpa only [sourceDecouplingErrorEnvelope, Nat.cast_add] using hs
  exact henv.trans (heω hr₀ hb₀ hr₁ hb₁)

end SRWTightness
