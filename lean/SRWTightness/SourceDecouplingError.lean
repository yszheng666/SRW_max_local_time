import SRWTightness.SourceGroupedFineError
import SRWTightness.SourceLongSegmentCount
import SRWTightness.SourceSuccessPrefix

open MeasureTheory Filter
namespace SRWTightness

/-- The actual error envelope: one exit cost per long segment, one return cost per original short
root, and both complete grouped fine-record error sums. -/
noncomputable def sourceDecouplingErrorEnvelope (A C B W t a₀ a₁ : ℝ) (b w : Site)
    (K₀ K₁ : Finset Site) (ν J : ℕ) (ω : Sample) : ℝ :=
  A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) * (sourceLongSegmentCount t b w ν J ω : ℝ) +
    (C * 15 / (sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) *
        ((sourceActualCount t b ν ω + sourceActualCount t w ν ω : ℕ) : ℝ) +
    ((sourceGroupedFineForest t b w b K₀ ν J ω).map (sourceLongFineError B W t a₀ K₀ ν)).sum +
    ((sourceGroupedFineForest t b w w K₁ ν J ω).map (sourceLongFineError B W t a₁ K₁ ν)).sum

/-- The actual error envelope has the quantitative form in equation 8.5 on both source coarse events. -/
theorem source_decoupling_error_envelope_bound (hF : TwoLevelWordFlatteningInput)
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
      sourceDecouplingErrorEnvelope A C B W t a₀ a₁ b w K₀ K₁ ν J ω ≤
        16 * ((ν : ℝ) + 1) ^ 2 *
          (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
            C * 15 / (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
          2 * sourceForestQuadraticError B W 8 t := by
  filter_upwards [source_grouped_fine_error hF B W hB hW, source_long_segment_count_bound hF,
    source_early_root_cap_quadratic, source_deficit_large_conditions, source_root_gw_horizon_large,
    source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t he hM hcap ht hN htime hm16 ht0
  intro b w ν J hb hw hbw ha hν hform K₀ K₁ a₀ a₁ A C ha₀ hc₀ ha₁ hc₁ hA hC
  have hnreal : (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by exact_mod_cast hnreal
  have hi : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
    have hp := hN.1
    omega
  have hθ := (sourceBarrierSlope_bounds t ht.1 ht.2.1).1
  have hd := sourceLowerTime_ge_one t ht.1
  have hνtime : (ν : ℝ) ≤ sourceTotalTime t := by
    have hh := htime ν hν
    unfold sourceTotalTime
    linarith
  have hrad := sourceRecordRadius_ge_terminal (sourceLowerRadius t) (sourceLowerRadius_pos t).le
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) hi
  filter_upwards [he b w ν J hb hw hbw ha hν hform b (Or.inl rfl) K₀ a₀ ha₀ hc₀,
    he b w ν J hb hw hbw ha hν hform w (Or.inr rfl) K₁ a₁ ha₁ hc₁,
    hM b w ν J hb hw hbw ha hν hform] with ω he₀ he₁ hMω
  intro hroot₀ hbar₀ hroot₁ hbar₁
  have hprefix (z : Site) (hroot : sourceActualCount t z 0 ω = 1)
      (hbar : sourceWalkCoarseBand t z ω) : ω ∈ sourceEarlyPrefixEvent t z ν :=
    ⟨hroot, fun i hi hij ↦ hbar.1 i hi (hij.trans hn)⟩
  have hk₀ := source_prefix_count_cap t b ν ω hθ hνtime (hprefix b hroot₀ hbar₀) ν le_rfl
  have hk₁ := source_prefix_count_cap t w ν ω hθ hνtime (hprefix w hroot₁ hbar₁) ν le_rfl
  have htot : ((sourceActualCount t b ν ω + sourceActualCount t w ν ω : ℕ) : ℝ) ≤
      16 * ((ν : ℝ) + 1) ^ 2 := by
    have hh₀ : (sourceActualCount t b ν ω : ℝ) ≤ sourceEarlyRootCap t ν := Nat.cast_le.mpr hk₀
    have hh₁ : (sourceActualCount t w ν ω : ℝ) ≤ sourceEarlyRootCap t ν := Nat.cast_le.mpr hk₁
    rw [Nat.cast_add]
    linarith [hcap ν]
  have hMr : (sourceLongSegmentCount t b w ν J ω : ℝ) ≤
      ((sourceActualCount t b ν ω + sourceActualCount t w ν ω : ℕ) : ℝ) := Nat.cast_le.mpr hMω
  let δ := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ))
  let ε := C * 15 / (sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; exact div_nonneg (by positivity) (by linarith)
  have hseg := mul_le_mul_of_nonneg_left hMr hδ
  have htotal := mul_le_mul_of_nonneg_left htot (add_nonneg hδ hε)
  have hf₀ := he₀.2 hroot₀ hbar₀
  have hf₁ := he₁.2 hroot₁ hbar₁
  change δ * _ + ε * _ + _ + _ ≤ 16 * ((ν : ℝ) + 1) ^ 2 * (δ + ε) + _
  nlinarith only [hseg, htotal, hf₀, hf₁]

end SRWTightness
