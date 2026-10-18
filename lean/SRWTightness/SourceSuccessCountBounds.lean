import SRWTightness.SourceSuccessCount

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- The standard annulus count turns the actual success-count mean into uniform positive bounds. -/
theorem source_success_count_bounds (hLattice : LatticeAnnulusCountInput) :
    ∃ a B : ℝ, 0 < a ∧ 0 < B ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (A γ c C : ℝ), 0 ≤ γ → 0 < c → 0 < C →
      ∀ (I : sourceCandidateAnnulus R → ℕ)
        (z : ∀ b : sourceCandidateAnnulus R,
          translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b))),
      (∀ b : sourceCandidateAnnulus R, 1 ≤ A * diskEnergyGapRatio ^ I b ∧
        A * diskEnergyGapRatio ^ I b ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6) →
      (∀ b : sourceCandidateAnnulus R, c * (R ^ 2)⁻¹ ≤
          (pathLaw.prod (independentBridgeLaw ℕ)).real
            (sourceLocalTimeSuccessEvent (Real.log R) A γ b (I b) (z b)) ∧
        (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent (Real.log R) A γ b (I b) (z b)) ≤ C * (R ^ 2)⁻¹) →
      a * c ≤ (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) ∧
        (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) ≤ B * C := by
  obtain ⟨a, B, ha, hB, hcard⟩ := hLattice
  refine ⟨a, B, ha, hB, ?_⟩
  filter_upwards [hcard, source_success_count_first_moment, eventually_gt_atTop (0 : ℝ)]
    with R hcard hmean hR
  intro A γ c C hγ hc hC I z hcut hprob
  have hh := hmean A γ c C hγ I z hcut hprob
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  have hid (x y : ℝ) : (x * R ^ 2) * (y * (R ^ 2)⁻¹) = x * y := by
    field_simp
  have hlo := mul_le_mul_of_nonneg_right hcard.1
    (mul_nonneg hc.le (inv_nonneg.mpr (sq_nonneg R)))
  have hhi := mul_le_mul_of_nonneg_right hcard.2
    (mul_nonneg hC.le (inv_nonneg.mpr (sq_nonneg R)))
  rw [hid] at hlo hhi
  exact ⟨hlo.trans hh.1, hh.2.trans hhi⟩

end SRWTightness
