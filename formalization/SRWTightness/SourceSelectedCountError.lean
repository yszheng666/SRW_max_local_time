import SRWTightness.SourceSelectedDecouplingError

open MeasureTheory Filter
namespace SRWTightness

/-- With zero fine coefficients, the local error is exactly the root-count comparison cost. -/
theorem source_long_fine_error_zero (t a : ℝ) (K : Finset Site) (ν : ℕ)
    (r : FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))) :
    sourceLongFineError 0 0 t a K ν r = 0 := by
  simp [sourceLongFineError, finiteRecordError_population_sum, finiteRecordTerminalError_constant]

/-- The root-count comparison error needs only capped original counts, without a fine success event. -/
theorem source_selected_count_error_bound (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ (K₀ K₁ : Finset Site) (a₀ a₁ A C : ℝ),
      1 ≤ a₀ → a₀ ≤ sourceLowerRadius t / t ^ 6 →
      1 ≤ a₁ → a₁ ≤ sourceLowerRadius t / t ^ 6 → 0 ≤ A → 0 ≤ C →
      ∀ᵐ ω ∂pathLaw,
      sourceActualCount t b ν ω ≤ sourceEarlyRootCap t ν →
      sourceActualCount t w ν ω ≤ sourceEarlyRootCap t ν →
      sourceSelectedFineError A C 0 0 t a₀ a₁ b w K₀ K₁ ν J ω ≤
        16 * ((ν : ℝ) + 1) ^ 2 *
          (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
            C * 15 / (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) := by
  filter_upwards [source_long_segment_count_bound hF, source_early_root_cap_quadratic,
    source_grouped_fine_count hF, source_root_gw_horizon_large,
    source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with t hM hcap hcount hN htime hm ht
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
  filter_upwards [hM b w ν J hb hw hbw ha hν hform,
    hcount b w ν J hb hw hbw ha hν hform b (Or.inl rfl) K₀,
    hcount b w ν J hb hw hbw ha hν hform w (Or.inr rfl) K₁] with ω hMω h₀ h₁
  intro hk₀ hk₁
  have hs := source_selected_fine_error_bound A C 0 0 t a₀ a₁ b w K₀ K₁ ν J ω
    hC (by norm_num) (by norm_num) ht ha₀ hc₀ ha₁ hc₁ (by linarith)
  have hz₀ : sourceLongFineError 0 0 t a₀ K₀ ν = fun _ ↦ 0 := by
    funext r; exact source_long_fine_error_zero t a₀ K₀ ν r
  have hz₁ : sourceLongFineError 0 0 t a₁ K₁ ν = fun _ ↦ 0 := by
    funext r; exact source_long_fine_error_zero t a₁ K₁ ν r
  simp only [h₀, h₁, hz₀, hz₁, List.map_const', List.sum_replicate,
    nsmul_zero, add_zero] at hs
  have htot : (sourceActualCount t b ν ω : ℝ) + sourceActualCount t w ν ω ≤
      16 * ((ν : ℝ) + 1) ^ 2 := by
    have hh₀ : (sourceActualCount t b ν ω : ℝ) ≤ sourceEarlyRootCap t ν := Nat.cast_le.mpr hk₀
    have hh₁ : (sourceActualCount t w ν ω : ℝ) ≤ sourceEarlyRootCap t ν := Nat.cast_le.mpr hk₁
    linarith [hcap ν]
  have hMr : (sourceLongSegmentCount t b w ν J ω : ℝ) ≤
      (sourceActualCount t b ν ω : ℝ) + sourceActualCount t w ν ω := by
    exact_mod_cast hMω
  let δ := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ))
  let ε := C * 15 / (sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; exact div_nonneg (by positivity) (by linarith)
  have hseg := mul_le_mul_of_nonneg_left hMr hδ
  have htotal := mul_le_mul_of_nonneg_left htot (add_nonneg hδ hε)
  change _ ≤ 16 * ((ν : ℝ) + 1) ^ 2 * (δ + ε)
  change _ ≤ δ * _ + ε * _ at hs
  nlinarith only [hs, hseg, htotal]

end SRWTightness
