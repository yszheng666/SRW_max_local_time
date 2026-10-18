import SRWTightness.SourceSuccessCount
import SRWTightness.FiniteSuccessSecondMoment

open MeasureTheory Filter
open scoped BigOperators Topology

namespace SRWTightness

/-- The complete ordered-pair contribution on the manuscript common probability space. -/
noncomputable def sourcePairContribution (R A γ : ℝ)
    (I : sourceCandidateAnnulus R → ℕ)
    (z : ∀ b : sourceCandidateAnnulus R,
      translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b))) : ℝ :=
  ∑ b : sourceCandidateAnnulus R, ∑ w : sourceCandidateAnnulus R,
    sourceEnlargedLaw.real
      (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b) ∩
        sourceSiteSuccessEvent (Real.log R) A γ w (I w) (z w))

/-- Actual source scales make the true second moment equal the full pair contribution. -/
theorem source_success_second_moment :
    ∀ᶠ R : ℝ in atTop, ∀ (A γ : ℝ), 0 ≤ γ →
      ∀ (I : sourceCandidateAnnulus R → ℕ)
        (z : ∀ b : sourceCandidateAnnulus R,
          translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b))),
      (∀ b : sourceCandidateAnnulus R, 1 ≤ A * diskEnergyGapRatio ^ I b ∧
        A * diskEnergyGapRatio ^ I b ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6) →
      (∫ p, sourceSuccessCount R A γ I z p ^ 2 ∂sourceEnlargedLaw) =
        sourcePairContribution R A γ I z := by
  filter_upwards [Real.tendsto_log_atTop.eventually source_local_time_success_nullMeasurable,
    eventually_gt_atTop (0 : ℝ)] with R hnull hR
  intro A γ hγ I z hcut
  have hs (b : sourceCandidateAnnulus R) :
      NullMeasurableSet (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b))
        sourceEnlargedLaw := by
    have hb := (mem_sourceCandidateAnnulus R hR b).mp b.property
    apply source_site_success_nullMeasurable
    apply hnull A γ b (I b) (z b) hγ (hcut b).1 (hcut b).2
    · simpa only [Real.exp_log hR] using hb.1
    · simpa only [Real.exp_log hR] using hb.2
  exact finite_success_second_moment sourceEnlargedLaw Finset.univ
    (fun b : sourceCandidateAnnulus R ↦ sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b))
    (fun b _ ↦ hs b)

end SRWTightness
