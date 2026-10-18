import SRWTightness.SourceRemainingForestError
import SRWTightness.SourceTaggedErrorDecomposition
import SRWTightness.SourceLongEscapeProbability

open Filter
namespace SRWTightness

/-- Every remaining-success tagged tuple satisfies the full comparison error bound, without any
condition on the path before the split. -/
theorem source_tagged_remaining_error_bound (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ ν J : ℕ,
      ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (A C a₀ a₁ : ℝ) (K₀ K₁ : Finset Site), 0 ≤ A → 0 ≤ C →
      1 ≤ a₀ → a₀ ≤ sourceLowerRadius t / t ^ 6 →
      1 ≤ a₁ → a₁ ≤ sourceLowerRadius t / t ^ 6 →
      ∀ rs : List (SourceExteriorFineValue t K₀ K₁ ν),
      (∀ r ∈ rs, r.elim (fun us ↦ us ≠ []) (fun us ↦ us ≠ [])) →
      (taggedForestLeft rs).length ≤ sourceEarlyRootCap t ν →
      (taggedForestRight rs).length ≤ sourceEarlyRootCap t ν →
      forestPopulationList _ (taggedForestLeft rs) ∈ sourceContinuationBand t ν
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) →
      forestPopulationList _ (taggedForestRight rs) ∈ sourceContinuationBand t ν
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) →
      (rs.map (sourceExteriorFineError A C B W t a₀ a₁ K₀ K₁ ν J)).sum ≤
        16 * ((ν : ℝ) + 1) ^ 2 *
          (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
            C * 15 / (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
          2 * sourceForestQuadraticError B W 8 t := by
  filter_upwards [source_remaining_forest_error B W hB hW, source_early_root_cap_quadratic,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ))]
    with t he hcap hm
  intro ν J hν A C a₀ a₁ K₀ K₁ hA hC ha₀ hc₀ ha₁ hc₁ rs hr hk hl hb₀ hb₁
  have he₀ := he ν hν a₀ K₀ ha₀ hc₀ (taggedForestLeft rs) hk hb₀
  have he₁ := he ν hν a₁ K₁ ha₁ hc₁ (taggedForestRight rs) hl hb₁
  have hs : (rs.length : ℝ) ≤
      ((taggedForestLeft rs).length : ℝ) + (taggedForestRight rs).length := by
    exact_mod_cast tagged_forest_slots_le_roots rs hr
  have hkR := (Nat.cast_le.mpr hk : ((taggedForestLeft rs).length : ℝ) ≤ _).trans (hcap ν)
  have hlR := (Nat.cast_le.mpr hl : ((taggedForestRight rs).length : ℝ) ≤ _).trans (hcap ν)
  let δ := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ))
  let ε := C * 15 / (sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hrad := sourceRecordRadius_ge_terminal (sourceLowerRadius t)
    (sourceLowerRadius_pos t).le _ (ν + 1) hν
  have hε : 0 ≤ ε := div_nonneg (mul_nonneg hC (by norm_num)) (by linarith)
  have hcount : δ * (rs.length : ℝ) +
      ε * (((taggedForestLeft rs).length : ℝ) + (taggedForestRight rs).length) ≤
      16 * ((ν : ℝ) + 1) ^ 2 * (δ + ε) := by
    have hslots := mul_le_mul_of_nonneg_left hs hδ
    have htot := mul_le_mul_of_nonneg_left (show
      ((taggedForestLeft rs).length : ℝ) + (taggedForestRight rs).length ≤
        16 * ((ν : ℝ) + 1) ^ 2 by linarith) (add_nonneg hδ hε)
    nlinarith
  rw [source_tagged_error_decomposition]
  exact (add_le_add (add_le_add hcount he₀) he₁).trans_eq (by ring)

end SRWTightness
