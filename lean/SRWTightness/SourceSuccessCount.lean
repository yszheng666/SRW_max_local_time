import SRWTightness.SourceSiteBridgeLaw
import SRWTightness.SourceCandidateAnnulus
import SRWTightness.FiniteSuccessFirstMomentAE

open MeasureTheory Filter
open scoped BigOperators Topology

namespace SRWTightness

/-- The manuscript successful-site count on the common walk and site-bridge space. -/
noncomputable def sourceSuccessCount (R A γ : ℝ)
    (I : sourceCandidateAnnulus R → ℕ)
    (z : ∀ b : sourceCandidateAnnulus R,
      translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b)))
    (p : Sample × (Site → ℕ → GaussianCoefficientSpace)) : ℝ :=
  ∑ b : sourceCandidateAnnulus R,
    (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b)).indicator (fun _ ↦ 1) p

/-- Actual one-point bounds sum to the first moment over the complete manuscript annulus. -/
theorem source_success_count_first_moment :
    ∀ᶠ R : ℝ in atTop, ∀ (A γ c C : ℝ), 0 ≤ γ →
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
      (sourceCandidateAnnulus R).card * (c * (R ^ 2)⁻¹) ≤
          ∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw ∧
        (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) ≤
          (sourceCandidateAnnulus R).card * (C * (R ^ 2)⁻¹) := by
  filter_upwards [Real.tendsto_log_atTop.eventually source_local_time_success_nullMeasurable,
    eventually_gt_atTop (0 : ℝ)] with R hnull hR
  intro A γ c C hγ I z hcut hprob
  have hs (b : sourceCandidateAnnulus R) :
      NullMeasurableSet (sourceLocalTimeSuccessEvent (Real.log R) A γ b (I b) (z b))
        (pathLaw.prod (independentBridgeLaw ℕ)) := by
    have hb := (mem_sourceCandidateAnnulus R hR b).mp b.property
    apply hnull A γ b (I b) (z b) hγ (hcut b).1 (hcut b).2
    · simpa only [Real.exp_log hR] using hb.1
    · simpa only [Real.exp_log hR] using hb.2
  have hh := finite_success_first_moment_ae_bounds sourceEnlargedLaw Finset.univ
    (fun b : sourceCandidateAnnulus R ↦ sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b))
    (fun b _ ↦ source_site_success_nullMeasurable (Real.log R) A γ b (I b) (z b) (hs b))
    (c * (R ^ 2)⁻¹) (C * (R ^ 2)⁻¹) (fun b _ ↦ by
      rw [source_site_success_probability (Real.log R) A γ b (I b) (z b) (hs b)]
      exact hprob b)
  simpa only [sourceSuccessCount, Finset.card_univ, Fintype.card_coe] using hh

end SRWTightness
